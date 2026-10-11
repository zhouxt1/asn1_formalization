import Asn1.X691.ViewC
import Asn1.X690.Decode

/-!
# Decoding PER, as the relation `per` reads

An executable decoder written to follow `per` case by case, so that the relation can be run on real
encodings (`asn1check decode uper|aper|cuper|caper`).

PER has no tags or lengths that say where a value ends: what the bits mean depends on the type at
every step, and in the ALIGNED variant on where in the encoding a field starts. The decoder is
therefore one recursive descent (`pdec`), with one case per case of `perB`, reading against the PER
view of the type, computed (`ViewC.lean`).

Each case reads the sender's choices (an extension bit, a length, an index, the bits of a number)
and then builds the field-list with the functions the relation names (`constrainedInt`,
`lengthDet`, `bitsRootFields`, `kmBody`, `seqRootFields`, `openField`, …), from the values it has
read. `decode` finally checks that the complete encoding (11.1) of that field-list is exactly the
input. So the reading itself never has to be proved right: `pdec_sound` (`DecodeSound.lean`) shows
that what `pdec` returns, `per` relates, and the final comparison gives the bits. A reader that
went wrong could only make the decoder reject.

Where `per` asks for a property of the value (a root value, a size in the root, a character in the
alphabet, the index of an item), the decoder checks it with the computed view. Where the text has
the sender choose (DEFAULT values in BASIC-PER, the order of a SET OF), the decoder accepts what it
reads, and checks what the relation asks of that choice.

Not decoded: EMBEDDED PDV, EXTERNAL, CHARACTER STRING and the time types (32), and any constraint
`ViewC.lean` does not evaluate. An open type is decoded only when a table constraint says which type
it holds (X.682 10): PER carries nothing else that could say.
-/

namespace Asn1.X691

open Asn1.X680
open Asn1.X690 (DFrame tableHint evalLit eqIsEq notDefaultB decReal decString decOidArcs decIri
  genTimeCanonB utcTimeCanonB)

/-! ## The complete encoding, in one pass -/

/-- X.691 11.1.2–11.1.4: the bits a field-list adds after `p` bits (`concatFields`, which copies
the encoding so far at every field, `layout_eq`). -/
def layout (al : Bool) : Nat → FieldList → Bits
  | _, [] => []
  | p, .unaligned bs :: fs => bs ++ layout al (p + bs.length) fs
  | p, .aligned bs :: fs =>
    let pad := if al then (8 - p % 8) % 8 else 0
    List.replicate pad false ++ bs ++ layout al (p + pad + bs.length) fs

/-- `complete`, computed with `layout` (`completeFast_eq`). -/
def completeFast (v : Variant) (c : Carrier) (fl : FieldList) : Bits :=
  let bs := layout v.aligned 0 fl
  if !v.aligned && c == .bitString then
    if bs = [] then [false] else bs
  else
    if bs = [] then List.replicate 8 false else pad8 bs

/-! ## Reading bits -/

/-- Where the decoder is: the number of bits read so far (for the ALIGNED variant's octet
boundaries), and the bits left. -/
structure Rd where
  pos : Nat
  bs : Bits

abbrev PM := StateT Rd (Except String)

/-- The next `k` bits. -/
def takeN (k : Nat) : PM Bits := do
  let r ← get
  if r.bs.length < k then throw "the encoding ends early"
  set (Rd.mk (r.pos + k) (r.bs.drop k))
  pure (r.bs.take k)

def bitR : PM Bool := do
  let bs ← takeN 1
  pure (bs.headD false)

/-- X.691 11.1.4: in the ALIGNED variant, the padding before an octet-aligned field. -/
def alignR (v : Variant) : PM Unit := do
  if v.aligned then
    let r ← get
    discard <| takeN ((8 - r.pos % 8) % 8)

/-- A bit-field of `k` bits, octet-aligned in the ALIGNED variant if `al`. -/
def fieldR (v : Variant) (al : Bool) (k : Nat) : PM Bits := do
  if al then alignR v
  takeN k

/-- `bs` cut into `k` units of `w` bits. -/
def chunks (w : Nat) : Nat → Bits → List Bits
  | 0, _ => []
  | k + 1, bs => bs.take w :: chunks w k (bs.drop w)

/-- `k` units of `w` bits, in one bit-field (11.9.2 a), b), d)). -/
def unitsR (v : Variant) (w : Nat) (al : Bool) (k : Nat) : PM (List Bits) := do
  let bs ← fieldR v al (w * k)
  pure (chunks w k bs)

/-! ## Whole numbers and lengths (11.5–11.9) -/

/-- X.691 11.5 with "ub − lb" below 64K (all of 11.5 but the indefinite length case): the number. -/
def wholeR (v : Variant) (lb ub : Int) : PM Int := do
  let range := (ub - lb + 1).toNat
  if range = 1 then pure lb
  else if !v.aligned then pure (lb + nnbValue (← takeN (bitsFor range)))
  else if range ≤ 255 then pure (lb + nnbValue (← takeN (bitsFor range)))
  else if range = 256 then pure (lb + nnbValue (← fieldR v true 8))
  else if range ≤ K64 then pure (lb + nnbValue (← fieldR v true 16))
  else throw "11.5.7.4: a length with a range of 64K or more"

/-- X.691 11.9.3.5–11.9.3.8: an unconstrained length and the fragments that follow, with `readK al k`
reading `k` units (in a bit-field octet-aligned if `al`). -/
def ulR {α : Type} (v : Variant) (readK : Bool → Nat → PM (List α)) (al : Bool) : Nat → PM (List α)
  | 0 => throw "11.9.3.8: too many fragments"
  | f + 1 => do
    let o ← fieldR v true 8
    match o with
    | false :: rest => readK al (nnbValue rest)
    | true :: false :: rest =>
      let o2 ← takeN 8
      readK al (nnbValue (rest ++ o2))
    | _ =>
      let q := nnbValue (o.drop 2)
      if q < 1 || q > 4 then throw "11.9.3.8: a fragment multiplier outside 1 to 4"
      let us ← readK true (q * K16)
      let more ← ulR v readK al f
      pure (us ++ more)

/-- X.691 11.9: a length determinant of kind `k` and the units it counts (`lengthDet`). -/
def lenDetR {α : Type} (v : Variant) (k : LenKind) (readK : Bool → Nat → PM (List α)) (al : Bool)
    (fuel : Nat) : PM (List α) :=
  match k with
  | .constrained lb ub =>
    if ub < K64 then do
      let c ← wholeR v lb ub
      if c.toNat = 0 then pure [] else readK al c.toNat
    else ulR v readK al fuel
  | .normallySmall => do
    if ← bitR then ulR v readK al fuel
    else
      let c ← takeN 6
      readK al (nnbValue c + 1)
  | .semi _ => ulR v readK al fuel

/-- Fuel for fragments: each takes at least a bit. -/
def fragFuel : PM Nat := do pure ((← get).bs.length + 1)

/-- The octets after an unconstrained length (24–27, 15, 30.6, open types). -/
def octetsUL (v : Variant) : PM Octets := do
  let us ← ulR v (unitsR v 8) true (← fragFuel)
  pure (us.map octetOf)

/-- X.691 11.5 (13.2.2, 13.2.5, 13.2.6 a)): a constrained whole number (`constrainedInt`). -/
def constrainedR (v : Variant) (lb ub : Int) : PM Int := do
  let range := (ub - lb + 1).toNat
  if v.aligned && range > K64 then
    let us ← lenDetR v (.constrained 1 (octetsFor (ub - lb).toNat)) (unitsR v 8) true (← fragFuel)
    pure (lb + nnbValue us.flatten)
  else wholeR v lb ub

/-- X.691 11.6: a normally small non-negative whole number (`normallySmall`). -/
def normallySmallR (v : Variant) : PM Nat := do
  if ← bitR then
    let us ← ulR v (unitsR v 8) true (← fragFuel)
    pure (nnbValue us.flatten)
  else pure (nnbValue (← takeN 6))

/-! ## Field-lists, computed from the view -/

/-- `intRootFields`, with the root as computed. -/
def intRootFieldsC (v : Variant) (s : Ivs) (i : Int) : FieldList :=
  match s.least?, s.greatest? with
  | some lb, some ub => constrainedInt v lb ub i
  | some lb, none => semiInt lb i
  | none, _ => unconstrainedInt i

/-- The field-list of `IntFields`, computed. -/
def intFl (v : Variant) (C : CSet) (i : Int) : FieldList :=
  if C.ext then
    if C.r.mem i then .unaligned [false] :: intRootFieldsC v C.r i
    else .unaligned [true] :: unconstrainedInt i
  else intRootFieldsC v C.r i

/-- The field-list of `BitsFields`, `OctetsFields`, `KmFields` and `SeqOfFields`: an extension bit
if `S` is extensible, then the root fields for a root size, or `ext` otherwise. -/
def sizedFl (S : CSet) (len : Nat) (rootF extF : FieldList) : FieldList :=
  if S.ext then
    if S.r.mem len then .unaligned [false] :: rootF else .unaligned [true] :: extF
  else rootF

/-- The root's least and greatest sizes. -/
def lbOf (S : CSet) : Nat := (S.r.natLeast?).getD 0
def ubOf (S : CSet) : Option Nat := S.r.natGreatest?

/-- The field-list of `SeqOfFields`, computed. -/
def seqOfFl (v : Variant) (S : CSet) (fls : List FieldList) : FieldList :=
  let lb := lbOf S
  let ub := (ubOf S).filter (· < K64)
  let rootF : FieldList := match ub with
    | some u => if lb = u then fls.flatten else lengthDet v (.constrained lb u) (.comps fls)
    | none => lengthDet v (.semi lb) (.comps fls)
  sizedFl S fls.length rootF (lengthDet v (.semi 0) (.comps fls))

/-! ## Reading sized values -/

/-- The extension bit of a type extensible for PER, and the bounds to read with: the root's, or
none for a size outside it. -/
def sizeBounds (S : CSet) : PM (Bool × Nat × Option Nat) := do
  if S.ext then
    if ← bitR then pure (true, 0, none) else pure (false, lbOf S, ubOf S)
  else pure (false, lbOf S, ubOf S)

/-- The bits of a bit string (16.8–16.11, `bitsRootFields`). -/
def bitsRootR (v : Variant) (lb : Nat) (ub : Option Nat) : PM Bits := do
  match ub with
  | some 0 => pure []
  | some u =>
    if lb = u ∧ u ≤ 16 then takeN u
    else if lb = u ∧ u < K64 then fieldR v true u
    else pure (← lenDetR v (.constrained lb u) (unitsR v 1) true (← fragFuel)).flatten
  | none => pure (← lenDetR v (.semi lb) (unitsR v 1) true (← fragFuel)).flatten

/-- The octets of an octet string (17.5–17.8, `octetsRootFields`). -/
def octetsRootR (v : Variant) (lb : Nat) (ub : Option Nat) : PM Octets := do
  match ub with
  | some 0 => pure []
  | some u =>
    if lb = u ∧ u ≤ 2 then pure (bitsToOctets (← takeN (8 * u)))
    else if lb = u ∧ u < K64 then pure (bitsToOctets (← fieldR v true (8 * u)))
    else pure ((← lenDetR v (.constrained lb u) (unitsR v 8) true (← fragFuel)).map octetOf)
  | none => pure ((← lenDetR v (.semi lb) (unitsR v 8) true (← fragFuel)).map octetOf)

/-- X.691 30.5.4: the character a "b"-bit unit stands for. -/
def charOf (v : Variant) (alpha : List Nat) (u : Bits) : Except String Nat :=
  let b := charWidth v alpha.length
  let ub := alpha.foldl max 0
  if ub ≤ 2 ^ b - 1 then .ok (nnbValue u)
  else match alpha[nnbValue u]? with
    | some c => .ok c
    | none => .error "30.5.4: a character index past the alphabet"

/-- The characters of a known-multiplier string (30.5.6, 30.5.7, `kmBody`). -/
def kmR (v : Variant) (alpha : List Nat) (alb : Nat) (aub : Option Nat) : PM (List Nat) := do
  let b := charWidth v alpha.length
  let us ← match aub with
    | some u =>
      if alb = u ∧ u < K64 then do
        let bs ← fieldR v (u * b > 16) (u * b)
        pure (chunks b u bs)
      else lenDetR v (.constrained alb u) (unitsR v b) (u * b ≥ 16) (← fragFuel)
    | none => lenDetR v (.semi alb) (unitsR v b) true (← fragFuel)
  match us.mapM (charOf v alpha) with
  | .ok cs => pure cs
  | .error e => throw e

/-! ## Open types and DEFAULT values -/

/-- X.682 10: the type a table constraint on the notation `t` picks for an open type. -/
def hintOf (E : Env) (n : Nat) (frames : List DFrame) (sc : Scope) : Ty → Option (Scope × Ty)
  | .constrained t c => (tableHint E n frames sc t c).or (hintOf E n frames sc t)
  | .tagged _ _ t => hintOf E n frames sc t
  | _ => none

/-- The notation is a type reference (under tags and constraints). -/
def refNotation : Ty → Bool
  | .ref _ | .extRef _ _ | .paramRef _ _ _ => true
  | .tagged _ _ t | .constrained t _ => refNotation t
  | _ => false

/-- X.682 10.10: the enclosing values visible from the components of a type: none through a type
reference, whose text is elsewhere (a table constraint on the notation itself still sees `frames`,
`hintOf`). -/
def framesIn (frames : List DFrame) (t : Ty) : List DFrame := if refNotation t then [] else frames

/-- Value notation evaluated, following `evalVal` (`evalValC_spec`): references, and the components
of composite values; not values from objects. -/
def evalValC (E : Env) : Nat → Scope → Val → Option Val
  | 0, _, _ => none
  | n + 1, sc, .ref mn name args =>
    (resolveVal E n sc mn name args).bind fun (sc', v) => evalValC E n sc' v
  | _ + 1, _, .fromObject _ _ => none
  | n + 1, sc, .seq cs => (cs.mapM fun (p : String × Val) => (evalValC E n sc p.2).map ((p.1, ·))).map .seq
  | n + 1, sc, .seqOf vs => (vs.mapM (evalValC E n sc)).map .seqOf
  | n + 1, sc, .setOf vs => (vs.mapM (evalValC E n sc)).map .setOf
  | n + 1, sc, .choice a x => (evalValC E n sc x).map (.choice a)
  | n + 1, sc, .open_ t x => (evalValC E n sc x).map (.open_ t)
  | _ + 1, _, .raw _ => none
  | _ + 1, _, v => some v

/-- `eqv E n sc t x x`, where it can be decided (`eqvReflB_spec`): every case of `eqv` whose
equality is reflexive on `x`. -/
def eqvReflB (E : Env) : Nat → Scope → Ty → Val → Bool
  | 0, _, _, _ => false
  | n + 1, sc, .ref name, x => match resolveTy E n sc none name [] with
    | some (sc', t) => eqvReflB E n sc' t x
    | none => false
  | n + 1, sc, .extRef mn name, x => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => eqvReflB E n sc' t x
    | none => false
  | n + 1, sc, .paramRef mn name args, x => match resolveTy E n sc mn name args with
    | some (sc', t) => eqvReflB E n sc' t x
    | none => false
  | n + 1, sc, .tagged _ _ t, x => eqvReflB E n sc t x
  | n + 1, sc, .constrained t _, x => eqvReflB E n sc t x
  | _ + 1, _, .selection _ _, _ => false
  | _ + 1, _, .classField _ _, _ => false
  | _ + 1, _, .instanceOf _, _ => false
  | n + 1, sc, .sequence r e r2, x | n + 1, sc, .set r e r2, x => match x with
    | .seq cs =>
      let es := entries E n sc r e r2
      cs.all (fun p => (es.map (·.name)).contains p.1) &&
      es.attach.all fun ⟨en, _⟩ => match cs.lookup en.name with
        | none => true
        | some y => eqvReflB E n en.scope en.ty y
    | _ => false
  | n + 1, sc, .sequenceOf e, x => match x with
    | .seqOf xs => xs.attach.all fun ⟨y, _⟩ => eqvReflB E n sc e y
    | _ => false
  | n + 1, sc, .setOf e, x => match x with
    | .setOf xs => xs.attach.all fun ⟨y, _⟩ => eqvReflB E n sc e y
    | _ => false
  | n + 1, sc, .choice root ext, x => match x with
    | .choice a y => (choiceAlts root ext).any fun alt => alt.name == a && eqvReflB E n sc alt.ty y
    | _ => false
  | _ + 1, _, .bitString _, x => match x with
    | .bits _ => true
    | _ => false
  | n + 1, sc, .openType, x => match x with
    | .open_ t y => eqvReflB E n sc t y
    | _ => false
  | _ + 1, _, .embeddedPdv, _ | _ + 1, _, .external, _ | _ + 1, _, .characterString, _ => false
  | _ + 1, _, .time, _ | _ + 1, _, .date, _ | _ + 1, _, .timeOfDay, _
  | _ + 1, _, .dateTime, _ | _ + 1, _, .duration, _ => false
  | _ + 1, _, _, _ => true

/-- `eqv E n sc t x y` certainly fails (`neqvB_spec`): values of different shapes or lengths, or
simple values that differ, through references, tags and constraints. -/
def neqvB (E : Env) : Nat → Scope → Ty → Val → Val → Bool
  | 0, _, _, _, _ => true
  | n + 1, sc, .ref name, x, y => match resolveTy E n sc none name [] with
    | some (sc', t) => neqvB E n sc' t x y
    | none => true
  | n + 1, sc, .extRef mn name, x, y => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => neqvB E n sc' t x y
    | none => true
  | n + 1, sc, .paramRef mn name args, x, y => match resolveTy E n sc mn name args with
    | some (sc', t) => neqvB E n sc' t x y
    | none => true
  | n + 1, sc, .tagged _ _ t, x, y => neqvB E n sc t x y
  | n + 1, sc, .constrained t _, x, y => neqvB E n sc t x y
  | _ + 1, _, .sequenceOf _, x, y => match x, y with
    | .seqOf xs, .seqOf ys => xs.length != ys.length
    | _, _ => true
  | _ + 1, _, .setOf _, x, y => match x, y with
    | .setOf xs, .setOf ys => xs.length != ys.length
    | _, _ => true
  | _ + 1, _, .boolean, x, y | _ + 1, _, .integer _, x, y | _ + 1, _, .enumerated _ _, x, y
  | _ + 1, _, .null, x, y | _ + 1, _, .objectIdentifier, x, y | _ + 1, _, .relativeOid, x, y
  | _ + 1, _, .octetString, x, y | _ + 1, _, .restricted _, x, y | _ + 1, _, .utcTime, x, y
  | _ + 1, _, .generalizedTime, x, y => X690.litNeq x y
  | _ + 1, _, .bitString named, x, y => match x, y with
    | .bits xs, .bits ys => if named = [] then xs != ys
      else stripTrailingZeros xs != stripTrailingZeros ys
    | _, _ => true
  | _ + 1, _, _, _, _ => false

/-- X.691 3.7.5: a composite type (`CompOut.isComposite`). -/
def isCompositeB (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Bool :=
  match builtin E n sc t with
  | some (_, .sequence ..) | some (_, .set ..) | some (_, .sequenceOf _) | some (_, .setOf _)
  | some (_, .choice ..) | some (_, .embeddedPdv) | some (_, .external)
  | some (_, .characterString) => true
  | _ => false

/-- X.691 19.5: what `CompOut` asks of a component that is encoded: if it has a DEFAULT, the default
evaluates, and the value is not the default, or (BASIC-PER) the type is composite. -/
def presentOkB (E : Env) (v : Variant) (n : Nat) (en : Entry) (x : Val) : Bool :=
  match en.presence with
  | .default_ d => match evalValC E n en.scope d with
    | some dv => notDefaultB E n en x || neqvB E n en.scope en.ty x dv ||
        (!v.canonical && isCompositeB E n en.scope en.ty)
    | none => false
  | _ => true

/-- X.691 19.5: what `CompOut` asks of a component that is not encoded: one in the root is not
mandatory, and a default evaluates to a value equal to itself. -/
def absentOkB (E : Env) (n : Nat) (root : Bool) (en : Entry) : Bool :=
  match en.presence with
  | .mandatory => !root
  | .optional => true
  | .default_ d => match evalValC E n en.scope d with
    | some dv => eqvReflB E n en.scope en.ty dv
    | none => false

/-! ## SEQUENCE and SET (19, 21) -/

/-- The components of a SEQUENCE or SET as frames see them (X.682 10.10). -/
def frameComps (es : List Entry) : List (String × Scope × Ty) := es.map fun en => (en.name, en.scope, en.ty)

/-- X.691 19.2–19.5: the components `es` after a preamble `pre` (one bit per component that is not
mandatory): each component's value and field-list, or `none`. -/
def compsR (E : Env) (v : Variant) (n : Nat) (rec : List DFrame → Scope → Ty → PM (Val × FieldList))
    (frames : List DFrame) (all : List (String × Scope × Ty)) (root : Bool) :
    List Entry → Bits → List (String × Val) → PM (List (String × Val) × List (Option FieldList))
  | [], _, acc => pure (acc, [])
  | en :: es, pre, acc => do
    let (present, pre') := if en.presence.isMandatory then (true, pre) else (pre.headD false, pre.tail)
    if present then
      let (x, f) ← rec (⟨.seq, all, acc, en.name⟩ :: frames) en.scope en.ty
      if !presentOkB E v n en x then
        throw s!"19.5: {en.name} has a default value it may equal, or one that is not evaluated here"
      let (cs, outs) ← compsR E v n rec frames all root es pre' (acc ++ [(en.name, x)])
      pure (cs, some f :: outs)
    else
      if !absentOkB E n root en then
        throw s!"19.2, 19.5: {en.name} is absent, and is mandatory or has a default not evaluated here"
      let (cs, outs) ← compsR E v n rec frames all root es pre' acc
      pure (cs, none :: outs)

/-- X.691 19.2, 19.3: the preamble of `es`. -/
def preambleR (v : Variant) (es : List Entry) : PM Bits := do
  let k := (es.filter fun e => !e.presence.isMandatory).length
  if k = 0 then pure []
  else if k < K64 then takeN k
  else pure (← lenDetR v (.constrained k k) (unitsR v 1) false (← fragFuel)).flatten

/-- The bits of an open type field (11.2), after its length. -/
def openR (v : Variant) : PM (List Bits) := do ulR v (unitsR v 8) true (← fragFuel)

/-- Decode `m` from the bits `bs` of an open type field, from its start. -/
def runInner {α : Type} (m : PM α) (bs : Bits) : Except String α :=
  (m.run ⟨0, bs⟩).map (·.1)

/-- X.691 19.7–19.9: one extension addition of a SEQUENCE or SET, after the components decoded so far
and the additions' outcomes so far: absent (bit 0), or its open type field (a group as a sequence of
its components). -/
def addStep (E : Env) (v : Variant) (n : Nat) (rec : List DFrame → Scope → Ty → PM (Val × FieldList))
    (frames : List DFrame) (all : List (String × Scope × Ty))
    (acc : List (String × Val) × List (Option FieldList)) (a : (List Entry × Bool) × Bool) :
    PM (List (String × Val) × List (Option FieldList)) := do
  let (cs, outs) := acc
  let ((es, grp), p) := a
  if !p then
    if !(es.all (absentOkB E n false)) then
      throw "19.5: an absent extension addition has a default not evaluated here"
    pure (cs, outs ++ [none])
  else
    let us ← openR v
    let inner := us.flatten
    let r : Except String (List (String × Val) × FieldList) :=
      if grp then runInner (do
        let pre ← preambleR v es
        let (cs', gouts) ← compsR E v n rec frames all false es pre cs
        if gouts.all Option.isNone then throw "19.9: an addition group with no component, encoded"
        if !((es.zip gouts).all fun p => !p.1.presence.isMandatory || p.2.isSome) then
          throw "X.680 25.13: a mandatory component of an addition group is missing"
        pure (cs', seqRootFields v es gouts)) inner
      else match es with
        | [e] => runInner (do
            let (x, f) ← rec (⟨.seq, all, cs, e.name⟩ :: frames) e.scope e.ty
            if !presentOkB E v n e x then
              throw s!"19.5: {e.name} has a default value it may equal, or one not evaluated here"
            pure (cs ++ [(e.name, x)], f)) inner
        | _ => .error "19.9: an addition that is not a group has one component"
    match r with
    | .error e => throw e
    | .ok (cs', f) =>
      if us != octetsOf (completeFast v .other f) then
        throw "11.2: the open type field is not the complete encoding of the addition"
      pure (cs', outs ++ [some f])

/-- X.691 19 (21): a SEQUENCE or SET value with root components `rootEs`, in the order they are
encoded, and extension additions `adds`; its components and its field-list (`SeqFields`). -/
def seqR (E : Env) (v : Variant) (n : Nat) (rec : List DFrame → Scope → Ty → PM (Val × FieldList))
    (frames : List DFrame) (isExt : Bool) (rootEs : List Entry) (adds : List (List Entry × Bool)) :
    PM (Val × FieldList) := do
  let allEs := rootEs ++ adds.flatMap (·.1)
  let all := frameComps allEs
  if !decide (allEs.map (·.name)).Nodup then throw "X.680 25: two components with one identifier"
  if !(adds.all fun a => a.2 || a.1.length == 1) then
    throw "19.9: an extension addition that is not a group, with other than one component"
  let anyAdd ← if isExt then bitR else pure false
  let pre ← preambleR v rootEs
  let (cs, rootOuts) ← compsR E v n rec frames all true rootEs pre []
  let rootF := seqRootFields v rootEs rootOuts
  if !anyAdd then
    -- no addition present: each is absent
    if !(adds.all fun a => a.1.all (absentOkB E n false)) then
      throw "19.5: an absent extension addition has a default not evaluated here"
    let fl := if isExt then .unaligned [false] :: rootF else rootF
    pure (.seq cs, fl)
  else
    let present ← lenDetR v .normallySmall (unitsR v 1) false (← fragFuel)
    let present := present.map fun u => u.headD false
    if present.length != adds.length then
      throw s!"19.7: {present.length} extension additions, the type has {adds.length}"
    let (cs, addOuts) ← (adds.zip present).foldlM (addStep E v n rec frames all) (cs, [])
    let present' := addOuts.map Option.isSome
    if !present'.any id then throw "19.6: the extension bit is set, and no addition is present"
    let fl := .unaligned [true] :: rootF ++
      (lengthDet v .normallySmall (.field false (bitUnits present')) ++
        addOuts.flatMap fun o => match o with
          | some f => openField v f
          | none => [])
    pure (.seq cs, fl)

/-! ## The decoder -/

/-- `pdecB E v n rec frames hint sc t sc' bt`: one value of the built-in type `bt` (read in `sc'`),
which the notation `t` (read in `sc`) denotes, and its field-list; `rec` decodes the components at
one less fuel. One case per case of `perB`. -/
def pdecB (E : Env) (v : Variant) (n : Nat) (rec : List DFrame → Scope → Ty → PM (Val × FieldList))
    (frames : List DFrame) (hint : Option (Scope × Ty)) (sc : Scope) (t : Ty) (sc' : Scope) (bt : Ty) :
    PM (Val × FieldList) :=
  match bt with
  -- 12
  | .boolean => do
    let b ← bitR
    pure (.bool b, [.unaligned [b]])
  -- 13
  | .integer _ => do
    let some C := pIntC E n sc t | throw "13: a PER-visible constraint not evaluated here"
    let e ← if C.ext then bitR else pure false
    let i ← if e then do
        let us ← ulR v (unitsR v 8) true (← fragFuel)
        pure (tcValue us.flatten)
      else match C.r.least?, C.r.greatest? with
        | some lb, some ub => constrainedR v lb ub
        | some lb, none => do
          let us ← ulR v (unitsR v 8) true (← fragFuel)
          pure (lb + nnbValue us.flatten)
        | none, _ => do
          let us ← ulR v (unitsR v 8) true (← fragFuel)
          pure (tcValue us.flatten)
    if !C.a.mem i then throw s!"13: {i} is not a value of the type's PER view"
    if !C.ext && !C.r.mem i then throw s!"13: {i} is not in the root"
    if C.ext && e != !C.r.mem i then throw s!"13.1: the extension bit says {e} for {i}"
    pure (.int i, intFl v C i)
  -- 14
  | .enumerated root ext => do
    let nums := enumNumbers root ext
    let rootItems := nums.take root.length
    let addItems := nums.drop root.length
    let isExt := ext.isSome || sc'.mod.header.extImplied
    let e ← if isExt then bitR else pure false
    let byIndex (items : List (String × Int)) (k : Nat) : Option String :=
      ((items.mergeSort fun a b => decide (a.2 ≤ b.2))[k]?).map (·.1)
    if !e then
      let k ← constrainedR v 0 (rootItems.length - 1 : Nat)
      let k := k.toNat
      match byIndex rootItems k with
      | some id =>
        if enumIndex rootItems id != some k then throw "14: two items with one number"
        let f := constrainedInt v 0 (rootItems.length - 1 : Nat) k
        pure (.enum id, if isExt then .unaligned [false] :: f else f)
      | none => throw s!"14.2: index {k} past the root's {rootItems.length} items"
    else
      let k ← normallySmallR v
      match byIndex addItems k with
      | some id =>
        if enumIndex addItems id != some k then throw "14: two items with one number"
        pure (.enum id, .unaligned [true] :: normallySmall k)
      | none => throw s!"14.3: addition index {k} past the {addItems.length} additions"
  -- 15
  | .real => do
    let os ← octetsUL v
    match decReal .der os with
    | .ok r => pure (.real r, octetsWithLength os)
    | .error e => throw s!"15: {e}"
  -- 16
  | .bitString named => do
    let some S := pSizeC E n sc t | throw "16: a PER-visible constraint not evaluated here"
    let (e, lb, ub) ← sizeBounds S
    let bs ← bitsRootR v lb ub
    if !S.a.mem bs.length then throw s!"16: size {bs.length} is not one of the type's PER view"
    if !S.ext && !S.r.mem bs.length then throw s!"16: size {bs.length} is not in the root"
    if S.ext && e != !S.r.mem bs.length then throw s!"16.6: the extension bit says {e} for size {bs.length}"
    if named != [] then
      -- 16.2, 16.3: the bits sent are the value with as few trailing 0 bits as the sizes allow
      let core := stripTrailingZeros bs
      if !((List.range bs.length).all fun k => decide (k < core.length) || !S.a.mem k) then
        throw "16.3: trailing 0 bits beyond the smallest size the constraint allows"
    pure (.bits bs, sizedFl S bs.length (bitsRootFields v (lbOf S) (ubOf S) bs)
      (bitsRootFields v 0 none bs))
  -- 17
  | .octetString => do
    let some S := pSizeC E n sc t | throw "17: a PER-visible constraint not evaluated here"
    let (e, lb, ub) ← sizeBounds S
    let os ← octetsRootR v lb ub
    if !S.a.mem os.length then throw s!"17: size {os.length} is not one of the type's PER view"
    if !S.ext && !S.r.mem os.length then throw s!"17: size {os.length} is not in the root"
    if S.ext && e != !S.r.mem os.length then throw s!"17.3: the extension bit says {e} for size {os.length}"
    pure (.octets os, sizedFl S os.length (octetsRootFields v (lbOf S) (ubOf S) os)
      (octetsRootFields v 0 none os))
  -- 18
  | .null => pure (.null, [])
  -- 19
  | .sequence r e r2 =>
    let (rootEs, adds) := splitEntries (entries E n sc' r e r2) e
    seqR E v n rec frames (e.isSome || sc'.mod.header.extImplied) rootEs adds
  -- 21
  | .set r e r2 =>
    let tagged := entryTags E n sc' r e r2
    let auto := autoSeq sc'.mod.header.tagDefault r e r2
    let key (p : Entry × Option (List Tag)) : Option Tag :=
      if auto then p.2.bind List.head? else sortTag E n p.1.scope p.1.ty
    let rootEs := (sortByTag key (tagged.filter (·.1.addition.isNone))).map (·.1)
    let adds := (splitEntries (tagged.map (·.1)) e).2
    seqR E v n rec frames (e.isSome || sc'.mod.header.extImplied) rootEs adds
  -- 20, 22
  | .sequenceOf el | .setOf el => do
    let some S := pSizeC E n sc t | throw "20: a PER-visible constraint not evaluated here"
    let (e, lb, ub) ← sizeBounds S
    let ub := ub.filter (· < K64)
    let fr : DFrame := ⟨if bt matches .setOf _ then .setOf else .seqOf, [], [], ""⟩
    let comp (_ : Bool) (k : Nat) : PM (List (Val × FieldList)) :=
      (List.replicate k ()).mapM fun _ => rec (fr :: frames) sc' el
    let xs ← match ub with
      | some u => if lb = u then comp true u else lenDetR v (.constrained lb u) comp true (← fragFuel)
      | none => lenDetR v (.semi lb) comp true (← fragFuel)
    let len := xs.length
    if !S.a.mem len then throw s!"20: {len} components is not a size of the type's PER view"
    if !S.ext && !S.r.mem len then throw s!"20: {len} components is not a size in the root"
    if S.ext && e != !S.r.mem len then throw s!"20.4: the extension bit says {e} for {len} components"
    let fls := xs.map (·.2)
    if bt matches .setOf _ then
      if v.canonical && !decide (fls.Pairwise fun a b => bitsLe (setOfKey v a) (setOfKey v b) = true) then
        throw "22.1: SET OF components not in ascending order"
      pure (.setOf (xs.map (·.1)), seqOfFl v S fls)
    else pure (.seqOf (xs.map (·.1)), seqOfFl v S fls)
  -- 23
  | .choice root ext => do
    let alts := altTags E n sc' root ext
    let auto := autoChoice sc'.mod.header.tagDefault root ext
    let key (p : Alt × Option (List Tag)) : Option Tag :=
      if auto then p.2.bind List.head? else sortTag E n sc' p.1.ty
    let rootS := sortByTag key (alts.take root.length)
    let addS := sortByTag key (alts.drop root.length)
    let isExt := ext.isSome || sc'.mod.header.extImplied
    let e ← if isExt then bitR else pure false
    if !e then
      let k ← constrainedR v 0 (rootS.length - 1 : Nat)
      let k := k.toNat
      let some (a, _) := rootS[k]? | throw s!"23.6: index {k} past the {rootS.length} root alternatives"
      if (rootS.map (·.1.name)).idxOf? a.name != some k then throw "X.680 29: two alternatives with one identifier"
      let fr : DFrame := ⟨.choice, (choiceAlts root ext).map fun a => (a.name, sc', a.ty), [], a.name⟩
      let (y, afl) ← rec (fr :: frames) sc' a.ty
      let f := constrainedInt v 0 (rootS.length - 1 : Nat) k ++ afl
      pure (.choice a.name y, if isExt then .unaligned [false] :: f else f)
    else
      let k ← normallySmallR v
      let some (a, _) := addS[k]? | throw s!"23.8: index {k} past the {addS.length} addition alternatives"
      if (addS.map (·.1.name)).idxOf? a.name != some k then throw "X.680 29: two alternatives with one identifier"
      let us ← openR v
      let fr : DFrame := ⟨.choice, (choiceAlts root ext).map fun a => (a.name, sc', a.ty), [], a.name⟩
      match runInner (rec (fr :: frames) sc' a.ty) us.flatten with
      | .error err => throw err
      | .ok (y, afl) =>
        if us != octetsOf (completeFast v .other afl) then
          throw "11.2: the open type field is not the complete encoding of the alternative"
        pure (.choice a.name y, .unaligned [true] :: normallySmall k ++ openField v afl)
  -- 24–27
  | .objectIdentifier => do
    let os ← octetsUL v
    match decOidArcs false os with
    | some a => if X690.oidContents a != os then throw "24: OBJECT IDENTIFIER contents" else
      pure (.oid a, octetsWithLength (X690.oidContents a))
    | none => throw "24: OBJECT IDENTIFIER contents"
  | .relativeOid => do
    let os ← octetsUL v
    match decOidArcs true os with
    | some a => if X690.relOidContents a != os then throw "25: RELATIVE-OID contents" else
      pure (.oid a, octetsWithLength (X690.relOidContents a))
    | none => throw "25: RELATIVE-OID contents"
  | .oidIri => do
    let os ← octetsUL v
    match decIri false os with
    | some a => if X690.iriContents a != os then throw "26: OID-IRI contents" else
      pure (.iri a, octetsWithLength (X690.iriContents a))
    | none => throw "26: OID-IRI contents"
  | .relativeOidIri => do
    let os ← octetsUL v
    match decIri true os with
    | some a => if X690.relIriContents a != os then throw "27: RELATIVE-OID-IRI contents" else
      pure (.iri a, octetsWithLength (X690.relIriContents a))
    | none => throw "27: RELATIVE-OID-IRI contents"
  -- 30
  | .restricted k =>
    if k.knownMultiplier then do
      let some (S, A) := pStrC E n sc t | throw "30: a PER-visible constraint not evaluated here"
      let alpha := effAlphabetC k A
      let (e, lb, ub) ← sizeBounds S
      let cs ← kmR v alpha lb ub
      if !cs.all (alpha.contains ·) then throw "30.5: a character outside the effective alphabet"
      if !S.a.mem cs.length then throw s!"30: length {cs.length} is not one of the type's PER view"
      if !S.ext && !S.r.mem cs.length then throw s!"30: length {cs.length} is not in the root"
      if S.ext && e != !S.r.mem cs.length then throw s!"30.4: the extension bit says {e} for length {cs.length}"
      pure (.chars cs, sizedFl S cs.length (kmBody v alpha (lbOf S) (ubOf S) cs) (kmBody v alpha 0 none cs))
    else do
      let os ← octetsUL v
      match decString (if v.canonical then .der else .ber) k os with
      | .ok x => pure (x, unconstrainedLength (.field true (octetUnits os)))
      | .error err => throw s!"30.6: {err}"
  -- 10.6.5
  | .generalizedTime | .utcTime => do
    let alpha := effAlphabetC .visible (CSet.plain (rangeIvs visibleChars))
    let (_, lb, ub) ← sizeBounds CSet.univ
    let cs ← kmR v alpha lb ub
    if !cs.all (alpha.contains ·) then throw "30.5: a character outside VisibleString"
    let canon := if bt matches .generalizedTime then genTimeCanonB (cs.map Char.ofNat)
      else utcTimeCanonB (cs.map Char.ofNat)
    if !canon then throw "10.6.5: not the form X.690 11.7 and 11.8 require"
    pure (.chars cs, sizedFl CSet.univ cs.length (kmBody v alpha (lbOf CSet.univ) (ubOf CSet.univ) cs)
      (kmBody v alpha 0 none cs))
  | .objectDescriptor => do
    let os ← octetsUL v
    match decString (if v.canonical then .der else .ber) .graphic os with
    | .ok x => pure (x, unconstrainedLength (.field true (octetUnits os)))
    | .error err => throw s!"30.6: {err}"
  -- 11.2
  | .openType => do
    let some (sc'', ty) := hint | throw "11.2: an open type whose type no table constraint gives"
    let us ← openR v
    match runInner (rec [] sc'' ty) us.flatten with
    | .error err => throw err
    | .ok (y, afl) =>
      if us != octetsOf (completeFast v .other afl) then
        throw "11.2: the open type field is not the complete encoding of its value"
      if !valSemB E n sc'' ty y then
        throw "X.680: the open type's value is not a value of the type the table gives"
      pure (.open_ ty y, openField v afl)
  | .embeddedPdv | .external | .characterString => throw "28, 29, 31: not decoded here"
  | .time | .date | .timeOfDay | .dateTime | .duration => throw "32: the time types are not decoded here"
  | _ => throw "not a built-in type PER encodes"

/-- The contents constraint on the notation `t` (under tags and other constraints), if any. -/
def contentsOf : Ty → Option (Option Ty × Option Val)
  | .constrained _ (.contents ct enc) => some (ct, enc)
  | .constrained t _ => contentsOf t
  | .tagged _ _ t => contentsOf t
  | _ => none

/-- X.682 11.4 with X.691 11.1.1 a), b): the value `x` of an OCTET STRING or BIT STRING whose notation
`t` has a contents constraint CONTAINING a type, under this variant (no ENCODED BY, or a PER object
identifier naming this variant, `variantOfOid`), is the complete encoding of a value of the
contained type, read with `dec`. Part of the value set (`perHook`), not of `per`: so it can only
make the decoder reject. Not decided (accepted): another variant, other encoding rules, and a
contained type with an open type no table gives. -/
def contentsOkB (E : Env) (v : Variant) (n : Nat) (dec : List DFrame → Scope → Ty → PM (Val × FieldList))
    (sc : Scope) (t : Ty) (x : Val) : Bool :=
  match contentsOf t with
  | some (some ct, enc) =>
    let same : Bool := match enc with
      | none => true
      | some e => match evalLit E n sc e with
        | some (.oid o) => variantOfOid o == some v
        | _ => false
    let check (c : Carrier) (bs : Bits) : Bool :=
      match (dec [] sc ct).run ⟨0, bs⟩ with
      | .ok ((_, fl), _) => completeFast v c fl == bs
      | .error e => e.startsWith "11.2: an open type whose type no table constraint gives"
    !same || match x with
      | .octets os => check .other (bitsOf os)
      | .bits bs => check .bitString bs
      | _ => true
  | _ => true

/-- `pdec E v n frames sc t`: a value of type `t` (read in `sc`), and its field-list, at fuel `n`
(`per`'s): tags, references and constraints seen through by `builtin`. -/
def pdec (E : Env) (v : Variant) : Nat → List DFrame → Scope → Ty → PM (Val × FieldList)
  | 0, _, _, _ => throw "fuel"
  | n + 1, frames, sc, t => match builtin E n sc t with
    | some (sc', bt) => do
      let r ← pdecB E v n (pdec E v n) (framesIn frames t) (hintOf E n frames sc t) sc t sc' bt
      if !contentsOkB E v n (pdec E v n) sc t r.1 then
        throw "X.682 11.4: the octets are not a complete encoding of a value of the contained type"
      pure r
    | none => throw "a type that does not resolve"

/-- X.691 11.1, 10.1: decode the octets `os` as the complete encoding of one value of `t` (written in
module `m`) under variant `v`: the value, read as `per` relates it, whose complete encoding is
exactly `os`. -/
def decode (E : Env) (v : Variant) (fuel : Nat) (m : Module) (t : Ty) (os : Octets) :
    Except String Val := do
  let bits := bitsOf os
  let ((x, fl), _) ← (pdec E v fuel [] (.ofModule m) t).run ⟨0, bits⟩
  if completeFast v .other fl != bits then
    throw "11.1: the input is not the complete encoding of the value read (extra octets, nonzero padding, or a field not in its fewest bits)"
  if !valSemB E fuel (.ofModule m) t x then
    throw "X.680: the value is not a value of the type (a constraint or format)"
  if !X690.presentOkB E fuel (.ofModule m) t x then
    throw "X.680 25.7, 27.1, 41: a mandatory component is missing, or a character not of its string type"
  pure x

/-- X.691 7.9, 11.1: decode a complete encoding at the start of `os`, followed by other octets (a
transport block's padding, say): the value, and the number of octets after the complete encoding.
PER is self-delimiting given the type (7.9), so where the complete encoding ends is fixed. -/
def decodePrefix (E : Env) (v : Variant) (fuel : Nat) (m : Module) (t : Ty) (os : Octets) :
    Except String (Val × Nat) := do
  let bits := bitsOf os
  let ((x, fl), _) ← (pdec E v fuel [] (.ofModule m) t).run ⟨0, bits⟩
  let c := completeFast v .other fl
  if c != bits.take c.length then
    throw "11.1: the input does not start with the complete encoding of the value read (nonzero padding, or a field not in its fewest bits)"
  if !valSemB E fuel (.ofModule m) t x then
    throw "X.680: the value is not a value of the type (a constraint or format)"
  if !X690.presentOkB E fuel (.ofModule m) t x then
    throw "X.680 25.7, 27.1, 41: a mandatory component is missing, or a character not of its string type"
  pure (x, (bits.length - c.length) / 8)

end Asn1.X691
