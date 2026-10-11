import Asn1.X691.Decode

/-!
# Encoding PER, as the relation `per` reads

An executable encoder written to follow `per` case by case: `penc` builds the field-list of a value
with the functions the relation names and the computed PER view (`ViewC.lean`), and `encode` makes
it the complete encoding (11.1). `penc_sound` (`EncSound.lean`) proves that `per` relates the value
to what `penc` returns.

Where the relation leaves the sender a choice, the encoder makes CANONICAL-PER's, which BASIC-PER
also allows (`per_canonical_basic`):
- a DEFAULT component absent from the value, or present and certainly its default, is not encoded;
  present and certainly not its default, it is; otherwise BASIC-PER encodes it if its type is
  composite (19.5, 3.7.5), and CANONICAL-PER gives up;
- a SET OF value's components in BASIC-PER in the value's order, in CANONICAL-PER sorted by their
  encodings (22.1);
- an open type's value `.open_ ty y` is encoded as a value of `ty` read in the scope of the open
  type's notation, or failing that in the first module where it encodes: the relation allows any
  scope, and a value records none (the types of a table are usually defined in another module);
- a bit string with named bits gets the fewest trailing 0 bits the sizes allow (16.2, 16.3).

Not encoded: REAL values whose DER contents the encoder does not find (it computes a candidate and
checks it with the decoder), the ISO 2022 (register) string types and ObjectDescriptor, EMBEDDED PDV,
EXTERNAL, CHARACTER STRING and the time types.
-/

namespace Asn1.X691

open Asn1.X680
open Asn1.X690 (evalLit eqIsEq notDefaultB decReal nr3Print genTimeCanonB utcTimeCanonB valKeyEq)

/-! ## Values certainly equal -/

/-- Two values certainly the same notation (`eqLitB_spec`): simple values, and empty compositions. -/
def eqLitB : Val → Val → Bool
  | .seqOf [], .seqOf [] => true
  | .setOf [], .setOf [] => true
  | .seq [], .seq [] => true
  | .null, .null => true
  | .octets a, .octets b => a == b
  | .bits a, .bits b => a == b
  | x, y => valKeyEq x y

/-! ## REAL (15): the CER/DER contents, found and checked -/

/-- The odd mantissa and exponent of `m · 2^e`. -/
def oddPart : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | k + 1, m, e => if m % 2 = 0 ∧ m ≠ 0 then oddPart k (m / 2) (e + 1) else (m, e)

/-- `m · 10^e` with `m` not a multiple of ten. -/
def decPart : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | k + 1, m, e => if m % 10 = 0 ∧ m ≠ 0 then decPart k (m / 10) (e + 1) else (m, e)

/-- The least `k` with `d ∣ b^k`, if one is below the bound. -/
def powDividing (b d : Nat) : Nat → Option Nat
  | 0 => none
  | f + 1 => (List.range (f + 1)).find? fun k => b ^ k % d == 0

/-- X.690 8.5.7.4, 11.3.1: the exponent field and its format: the exponent's minimum
2's-complement octets, after a length octet if there are more than three. -/
def expOctets (e : Int) : Nat × Octets :=
  let os := bitsToOctets (tcMinFn e)
  if os.length ≤ 3 then (os.length - 1, os) else (3, octet os.length :: os)

/-- A candidate for the CER/DER contents octets of a real value (X.690 8.5, 11.3). -/
def realCandidate : RealVal → Option Octets
  | .plusZero => some []
  | .plusInfinity => some [octet 0x40]
  | .minusInfinity => some [octet 0x41]
  | .notANumber => some [octet 0x42]
  | .minusZero => some [octet 0x43]
  | .num .two q => do
    let k ← powDividing 2 q.den (q.den.size + 1)
    let (m, e) := oddPart (q.num.natAbs * 2 ^ k / q.den).size (q.num.natAbs * 2 ^ k / q.den) (-(k : Int))
    let (fmt, ef) := expOctets e
    pure (octet (128 + (if q.num < 0 then 64 else 0) + fmt) :: ef ++ bitsToOctets (nnbMinFn m))
  | .num .ten q => do
    let k ← powDividing 10 q.den (q.den.size + 1)
    let (m, e) := decPart (q.num.natAbs * 10 ^ k / q.den).size (q.num.natAbs * 10 ^ k / q.den) (-(k : Int))
    pure (octet 3 :: (nr3Print (q.num < 0) m e).map fun c => octet c.toNat)

/-! ## Character strings that are not known-multiplier (30.6) -/

/-- X.690 8.23.5: the octets of a character string value of a type whose characters have one
encoding (`StringOctets`, in BER and in DER). -/
def strOctetsE (k : StrType) : Val → Except String Octets
  | .chars cs => match k with
    | .numeric | .printable | .visible | .ia5 =>
      if cs.all (· < 128) then .ok (cs.map octet) else .error "8.23.5: a character beyond 127"
    | .universal => .ok (universalOctets' cs)
    | .bmp => .ok (X690.bmpOctets cs)
    | .utf8 => .ok (X690.utf8String cs)
    | _ => .error "30.6: a string of this type is ISO 2022, not encoded here"
  | _ => .error "30.6: not a character string value"
where universalOctets' := X690.universalOctets

/-! ## SEQUENCE and SET (19, 21) -/

/-- X.691 19.2–19.5: what is encoded for the entry `en` of the value with components `cs`
(`CompOut`). -/
def compOutE (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → Except String FieldList)
    (root : Bool) (cs : List (String × Val)) (en : Entry) : Except String (Option FieldList) :=
  match en.presence with
  | .mandatory => match cs.lookup en.name with
    | some x => do pure (some (← rec en.scope en.ty x))
    | none => if root then .error s!"X.680 25.7: the mandatory component {en.name} is missing" else pure none
  | .optional => match cs.lookup en.name with
    | some x => do pure (some (← rec en.scope en.ty x))
    | none => pure none
  | .default_ d => match evalValC E n en.scope d with
    | none => .error s!"19.5: the default value of {en.name} is not evaluated here"
    | some dv => match cs.lookup en.name with
      | none =>
        if eqvReflB E n en.scope en.ty dv then pure none
        else .error s!"19.5: whether the default of {en.name} is its own value is not decided here"
      | some x =>
        if eqLitB x dv && eqvReflB E n en.scope en.ty dv then pure none
        else if notDefaultB E n en x || neqvB E n en.scope en.ty x dv ||
            (!v.canonical && isCompositeB E n en.scope en.ty) then do
          pure (some (← rec en.scope en.ty x))
        else .error s!"19.5: whether {en.name} equals its default value is not decided here"

/-- X.691 19.9: an extension addition group (`GroupOut`). -/
def groupE (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → Except String FieldList)
    (cs : List (String × Val)) (es : List Entry) : Except String (Option FieldList) := do
  let outs ← es.mapM (compOutE E v n rec false cs)
  if outs.all Option.isNone then pure none
  else if (es.zip outs).all (fun p => !p.1.presence.isMandatory || p.2.isSome) then
    pure (some (seqRootFields v es outs))
  else .error "X.680 25.13: a mandatory component of an addition group is missing"

/-- X.691 19 (21): a SEQUENCE or SET value (`SeqFields`). -/
def seqE (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → Except String FieldList)
    (isExt : Bool) (rootEs : List Entry) (adds : List (List Entry × Bool)) (cs : List (String × Val)) :
    Except String FieldList := do
  if !(cs.all fun p => ((rootEs ++ adds.flatMap (·.1)).map (·.name)).contains p.1) then
    .error "X.680 25: a component the type does not have"
  let rootOuts ← rootEs.mapM (compOutE E v n rec true cs)
  let addOuts ← adds.mapM fun a =>
    if a.2 then groupE E v n rec cs a.1
    else match a.1 with
      | [e] => compOutE E v n rec false cs e
      | _ => .error "19.9: an addition that is not a group, with other than one component"
  let present := addOuts.map Option.isSome
  let anyAdd := present.any id
  let rootF := seqRootFields v rootEs rootOuts
  if isExt then
    pure (.unaligned [anyAdd] :: rootF ++
      (if anyAdd then lengthDet v .normallySmall (.field false (bitUnits present)) ++
         addOuts.flatMap fun o => match o with
           | some f => openField v f
           | none => []
       else []))
  else if anyAdd then .error "19.1: an extension addition in a type with no extension marker"
  else pure rootF

/-! ## The encoder -/

/-- The first of `xs` for which `f` succeeds. -/
def firstOkE {α β : Type} (f : α → Except String β) (err : String) : List α → Except String β
  | [] => .error err
  | x :: xs => match f x with
    | .ok b => .ok b
    | .error _ => firstOkE f err xs

/-- X.691 16.2, 16.3: the bits sent for a bit string with named bits: the value without trailing 0
bits, padded with 0 bits to the least size at least its length the sizes `S` allow. -/
def namedSentE (S : CSet) (bs : Bits) : Except String Bits :=
  let core := stripTrailingZeros bs
  match (S.a.inter [(some (core.length : Int), none)]).least? with
  | some k => .ok (core ++ List.replicate (k.toNat - core.length) false)
  | none => .error "16.3: no size the constraint allows carries the bits"

/-- `pencB E v n rec sc t sc' bt x`: the field-list of the value `x` of the built-in type `bt` (read
in `sc'`) that the notation `t` (read in `sc`) denotes; `rec` encodes components at one less fuel.
One case per case of `perB`. -/
def pencB (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → Except String FieldList)
    (sc : Scope) (t : Ty) (sc' : Scope) (bt : Ty) (x : Val) : Except String FieldList :=
  match bt, x with
  -- 12
  | .boolean, .bool b => pure [.unaligned [b]]
  -- 13
  | .integer _, .int i => do
    let some C := pIntC E n sc t | .error "13: a PER-visible constraint not evaluated here"
    if !C.a.mem i then .error s!"13: {i} is not a value of the type's PER view"
    if !C.ext && !C.r.mem i then .error s!"13: {i} is not in the root"
    pure (intFl v C i)
  -- 14
  | .enumerated root ext, .enum id =>
    let nums := enumNumbers root ext
    let rootItems := nums.take root.length
    let addItems := nums.drop root.length
    let isExt := ext.isSome || sc'.mod.header.extImplied
    match enumIndex rootItems id with
    | some k =>
      let f := constrainedInt v 0 (rootItems.length - 1 : Nat) k
      pure (if isExt then .unaligned [false] :: f else f)
    | none =>
      if isExt then match enumIndex addItems id with
        | some k => pure (.unaligned [true] :: normallySmall k)
        | none => .error s!"14: {id} is no item of the type"
      else .error s!"14: {id} is no item of the type"
  -- 15
  | .real, .real r => match realCandidate r with
    | some os => match decReal .der os with
      | .ok r' => if r' = r then pure (octetsWithLength os)
        else .error "15: the DER contents found do not read back as the value"
      | .error e => .error s!"15: {e}"
    | none => .error "15: a real value whose DER contents are not found here"
  -- 16
  | .bitString named, .bits bs => do
    let some S := pSizeC E n sc t | .error "16: a PER-visible constraint not evaluated here"
    let sent ← if named = [] then pure bs else namedSentE S bs
    if !S.a.mem sent.length then .error s!"16: size {sent.length} is not one of the type's PER view"
    if !S.ext && !S.r.mem sent.length then .error s!"16: size {sent.length} is not in the root"
    pure (sizedFl S sent.length (bitsRootFields v (lbOf S) (ubOf S) sent) (bitsRootFields v 0 none sent))
  -- 17
  | .octetString, .octets os => do
    let some S := pSizeC E n sc t | .error "17: a PER-visible constraint not evaluated here"
    if !S.a.mem os.length then .error s!"17: size {os.length} is not one of the type's PER view"
    if !S.ext && !S.r.mem os.length then .error s!"17: size {os.length} is not in the root"
    pure (sizedFl S os.length (octetsRootFields v (lbOf S) (ubOf S) os) (octetsRootFields v 0 none os))
  -- 18
  | .null, .null => pure []
  -- 19
  | .sequence r e r2, .seq cs =>
    let (rootEs, adds) := splitEntries (entries E n sc' r e r2) e
    seqE E v n rec (e.isSome || sc'.mod.header.extImplied) rootEs adds cs
  -- 21
  | .set r e r2, .seq cs =>
    let tagged := entryTags E n sc' r e r2
    let auto := autoSeq sc'.mod.header.tagDefault r e r2
    let key (p : Entry × Option (List Tag)) : Option Tag :=
      if auto then p.2.bind List.head? else sortTag E n p.1.scope p.1.ty
    let rootEs := (sortByTag key (tagged.filter (·.1.addition.isNone))).map (·.1)
    let adds := (splitEntries (tagged.map (·.1)) e).2
    seqE E v n rec (e.isSome || sc'.mod.header.extImplied) rootEs adds cs
  -- 20
  | .sequenceOf el, .seqOf vs => do
    let some S := pSizeC E n sc t | .error "20: a PER-visible constraint not evaluated here"
    let fls ← vs.mapM (rec sc' el)
    if !S.a.mem fls.length then .error s!"20: {fls.length} components is not a size of the type's PER view"
    if !S.ext && !S.r.mem fls.length then .error s!"20: {fls.length} components is not a size in the root"
    pure (seqOfFl v S fls)
  -- 22: BASIC-PER in the value's order; CANONICAL-PER sorted (22.1)
  | .setOf el, .setOf vs => do
    let some S := pSizeC E n sc t | .error "22: a PER-visible constraint not evaluated here"
    let pairs ← vs.mapM fun w => do pure (w, ← rec sc' el w)
    let pairs := if v.canonical then
        pairs.mergeSort fun a b => bitsLe (setOfKey v a.2) (setOfKey v b.2) else pairs
    let fls := pairs.map (·.2)
    if v.canonical && !decide (fls.Pairwise fun a b => bitsLe (setOfKey v a) (setOfKey v b) = true) then
      .error "22.1: the components' encodings are not in a total order"
    if !S.a.mem fls.length then .error s!"22: {fls.length} components is not a size of the type's PER view"
    if !S.ext && !S.r.mem fls.length then .error s!"22: {fls.length} components is not a size in the root"
    pure (seqOfFl v S fls)
  -- 23
  | .choice root ext, .choice nm y =>
    let alts := altTags E n sc' root ext
    let auto := autoChoice sc'.mod.header.tagDefault root ext
    let key (p : Alt × Option (List Tag)) : Option Tag :=
      if auto then p.2.bind List.head? else sortTag E n sc' p.1.ty
    let rootS := sortByTag key (alts.take root.length)
    let addS := sortByTag key (alts.drop root.length)
    let isExt := ext.isSome || sc'.mod.header.extImplied
    match (rootS.map (·.1.name)).idxOf? nm with
    | some k => match rootS[k]? with
      | some (a, _) => do
        let afl ← rec sc' a.ty y
        let f := constrainedInt v 0 (rootS.length - 1 : Nat) k ++ afl
        pure (if isExt then .unaligned [false] :: f else f)
      | none => .error "23: no alternative"
    | none => match (addS.map (·.1.name)).idxOf? nm with
      | some k => match addS[k]? with
        | some (a, _) =>
          if isExt then do
            let afl ← rec sc' a.ty y
            pure (.unaligned [true] :: normallySmall k ++ openField v afl)
          else .error "23: an addition alternative in a type with no extension marker"
        | none => .error "23: no alternative"
      | none => .error s!"23: {nm} is no alternative of the type"
  -- 24–27
  | .objectIdentifier, .oid arcs => pure (octetsWithLength (X690.oidContents arcs))
  | .relativeOid, .oid arcs => pure (octetsWithLength (X690.relOidContents arcs))
  | .oidIri, .iri arcs => pure (octetsWithLength (X690.iriContents arcs))
  | .relativeOidIri, .iri arcs => pure (octetsWithLength (X690.relIriContents arcs))
  -- 30
  | .restricted k, _ =>
    if k.knownMultiplier then match x with
      | .chars cs => do
        let some (S, A) := pStrC E n sc t | .error "30: a PER-visible constraint not evaluated here"
        let alpha := effAlphabetC k A
        if !cs.all (alpha.contains ·) then .error "30.5: a character outside the effective alphabet"
        if !S.a.mem cs.length then .error s!"30: length {cs.length} is not one of the type's PER view"
        if !S.ext && !S.r.mem cs.length then .error s!"30: length {cs.length} is not in the root"
        pure (sizedFl S cs.length (kmBody v alpha (lbOf S) (ubOf S) cs) (kmBody v alpha 0 none cs))
      | _ => .error "30: not a character string value"
    else do
      let os ← strOctetsE k x
      pure (unconstrainedLength (.field true (octetUnits os)))
  -- 10.6.5
  | .generalizedTime, .chars cs | .utcTime, .chars cs => do
    let alpha := effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))
    if !cs.all (alpha.contains ·) then .error "30.5: a character outside VisibleString"
    let canon := if bt matches .generalizedTime then genTimeCanonB (cs.map Char.ofNat)
      else utcTimeCanonB (cs.map Char.ofNat)
    if !canon then .error "10.6.5: not the form X.690 11.7 and 11.8 require"
    pure (sizedFl CSet.univ cs.length (kmBody v alpha (lbOf CSet.univ) (ubOf CSet.univ) cs)
      (kmBody v alpha 0 none cs))
  -- 11.2
  | .openType, .open_ ty y => do
    let afl ← firstOkE (fun sc'' => rec sc'' ty y) "11.2: the open type's value is not encoded in any scope"
      (sc' :: E.map Scope.ofModule)
    pure (openField v afl)
  | _, _ => .error "not a value of the type, or a type not encoded here"

/-- `penc E v n sc t x`: the field-list of the value `x` of `t` (read in `sc`), at fuel `n`. -/
def penc (E : Env) (v : Variant) : Nat → Scope → Ty → Val → Except String FieldList
  | 0, _, _, _ => .error "fuel"
  | n + 1, sc, t, x => match builtin E n sc t with
    | some (sc', bt) => pencB E v n (penc E v n) sc t sc' bt x
    | none => .error "a type that does not resolve"

/-- X.691 11.1: the complete encoding of the value `x` of `t` (written in module `m`), in octets. -/
def encode (E : Env) (v : Variant) (fuel : Nat) (m : Module) (t : Ty) (x : Val) : Except String Octets := do
  let fl ← penc E v fuel (.ofModule m) t x
  pure (bitsToOctets (completeFast v .other fl))

end Asn1.X691
