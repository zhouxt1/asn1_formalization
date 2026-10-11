import Asn1.Format
import Asn1.X690.Contents
import Asn1.X691.Visible
import Asn1.X691.Time
import Asn1.X680.Enumerated

/-!
# PER: the encoding of each type into a field-list (X.691 10.5–10.6, 11.2, 12–31), and the rule

`per E v n sc t x fl`: under variant `v`, the value `x` of type `t` (read in scope `sc`) encodes to
the field-list `fl` (10.5). It is a relation: where the text leaves the sender a choice (19.5:
DEFAULT components of composite types in BASIC-PER; 22.2: the order of a SET OF value in BASIC-PER;
29.6–29.7: the EXTERNAL encoding alternative), every choice is allowed. CANONICAL-PER fixes the
choices (19.5, 22.1, 30.6.1), so BASIC and CANONICAL, ALIGNED and UNALIGNED, are one definition.

Tags and references are invisible (10.4.1, 10.6.2–10.6.4): the encoding follows `builtin`, the
built-in type. Constraints are seen only through the PER view of the type (`Visible.lean`).
Extension additions are told apart from root values by the PER view for integers and strings, and
by the type's notation for SEQUENCE, SET, CHOICE and ENUMERATED (10.3.22).

The complete encoding of the outermost value is `complete` (11.1), and `rule v` is PER as an
`EncodingRule`.

OPEN (ledger X691-20): PER encoding instructions (clause 9, X.695) are not represented: a `Ty` carries
no encoding instructions, so 9.3 never applies. The ALIGNED variant ignores them anyway (9.2).
-/

namespace Asn1.X691

open Asn1.X680
open Classical

/-! ## Fields built by the procedures of clause 11 -/

/-- Octets as the units of a length determinant (11.9.2 a)). -/
def octetUnits (os : Octets) : List Bits := os.map octetBits

/-- Bits as the units of a length determinant (11.9.2 b)). -/
def bitUnits (bs : Bits) : List Bits := bs.map fun b => [b]

/-- X.691 11.2: an open type field. The field-list of the value is made a complete encoding (11.1),
"n" octets, which is added after an unconstrained length "n" in octets (11.9), as a bit-field
octet-aligned in the ALIGNED variant. -/
def openField (v : Variant) (fl : FieldList) : FieldList :=
  unconstrainedLength (.field true (octetsOf (complete v .other fl)))

/-- X.691 13.2.2, 13.2.5, 13.2.6 a): a constrained whole number, with a constrained length
determinant (lb 1, ub the octets needed for the range) when 11.5 gives the indefinite length case. -/
def constrainedInt (v : Variant) (lb ub i : Int) : FieldList :=
  let w := constrainedWhole v lb ub i
  match w.len with
  | none => w.fields
  | some _ => lengthDet v (.constrained 1 (octetsFor (ub - lb).toNat))
      (.field true (octetsOf (w.fields.flatMap Field.bits)))

/-- X.691 13.2.3, 13.2.6 b): a semi-constrained whole number with an unconstrained length. -/
def semiInt (lb i : Int) : FieldList :=
  unconstrainedLength (.field true (octetsOf ((semiWhole lb i).fields.flatMap Field.bits)))

/-- X.691 13.2.4, 13.2.6 b): an unconstrained whole number with an unconstrained length. -/
def unconstrainedInt (i : Int) : FieldList :=
  unconstrainedLength (.field true (octetsOf ((unconstrainedWhole i).fields.flatMap Field.bits)))

/-- X.691 13.2: an integer with no extension marker in its PER-visible constraint, whose root is
`S`: no field for a single value (13.2.1, which is 11.5.4), a constrained whole number between the
least and greatest root values (13.2.2), a semi-constrained one above the least (13.2.3), or an
unconstrained one (13.2.4). -/
noncomputable def intRootFields (v : Variant) (S : Int → Prop) (i : Int) : FieldList :=
  match least? S, greatest? S with
  | some lb, some ub => constrainedInt v lb ub i
  | some lb, none => semiInt lb i
  | none, _ => unconstrainedInt i

/-- X.691 13: an integer value `i` of a type whose PER view is `P`. 13.1: with an extension marker,
a bit, 0 for a value in the root (then encoded as without the marker) and 1 for one outside it
(then encoded as an unconstrained whole number).

OPEN (ledger X691-7): 13.1, 16.6, 17.3, 20.4 and 30.4 test whether the value is "within the range of
the extension root". We read it as: a root value of the PER view (10.4.3, B.1.4), not as: between
the least and greatest root values. -/
noncomputable def IntFields (v : Variant) (P : PSet Int) (i : Int) (fl : FieldList) : Prop :=
  P.a i ∧
  if P.ext then
    (P.r i ∧ fl = .unaligned [false] :: intRootFields v P.r i) ∨
    (¬ P.r i ∧ fl = .unaligned [true] :: unconstrainedInt i)
  else P.r i ∧ fl = intRootFields v P.r i

/-! ## ENUMERATED (14) -/

/-- X.691 14.1: an item's enumeration index among `items` (the root, or the additions): the number
of items with a smaller enumeration value. -/
def enumIndex (items : List (String × Int)) (id : String) : Option Nat :=
  (items.find? (·.1 == id)).map fun (_, k) => (items.filter (·.2 < k)).length

/-- X.691 14: the value `id` of `ENUMERATED { root, ..., ext }` declared in a module with
EXTENSIBILITY IMPLIED `implied`.
- 14.2: without an extension marker, the index as a constrained integer 0 to the largest index;
- 14.3: with one, a bit, then the root index as in 14.2, or the addition's index as a normally small
  non-negative whole number (11.6). -/
def EnumFields (v : Variant) (root : List (String × Option Int))
    (ext : Option (List (String × Option Int))) (implied : Bool) (id : String) (fl : FieldList) :
    Prop :=
  let nums := enumNumbers root ext
  let rootItems := nums.take root.length
  let addItems := nums.drop root.length
  let rootFields (k : Nat) := constrainedInt v 0 (rootItems.length - 1 : Nat) k
  if ext.isSome || implied then
    (∃ k, enumIndex rootItems id = some k ∧ fl = .unaligned [false] :: rootFields k) ∨
    (∃ k, enumIndex addItems id = some k ∧ fl = .unaligned [true] :: normallySmall k)
  else ∃ k, enumIndex rootItems id = some k ∧ fl = rootFields k

/-! ## Strings of bits, octets and characters (16, 17, 30) -/

/-- X.691 16.2, 16.3: the bits sent for the value `bs` of a bit string type with named bits whose
sizes are `S`: trailing 0 bits added or removed to give the smallest size that carries the value
and satisfies the effective size constraint (16.2: with no PER-visible constraint every size does,
so all trailing 0 bits go).

OPEN (ledger X691-8): when the type is extensible for PER, we take "satisfies the effective size
constraint" over all sizes, root and additions. -/
def NamedBitsSent (S : PSet Nat) (bs sent : Bits) : Prop :=
  let core := stripTrailingZeros bs
  ∃ k, sent = core ++ List.replicate (k - core.length) false ∧ core.length ≤ k ∧ S.a k ∧
    ∀ k', core.length ≤ k' → S.a k' → k ≤ k'

/-- X.691 16.8–16.11: a bit string of `n` bits with sizes between "lb" and "ub" and no extension. -/
def bitsRootFields (v : Variant) (lb : Nat) (ub : Option Nat) (bs : Bits) : FieldList :=
  match ub with
  -- 16.8
  | some 0 => []
  | some u =>
    if lb = u ∧ u ≤ 16 then [.unaligned bs]                      -- 16.9
    else if lb = u ∧ u < K64 then [.aligned bs]                   -- 16.10
    else lengthDet v (.constrained lb u) (.field true (bitUnits bs))  -- 16.11
  | none => lengthDet v (.semi lb) (.field true (bitUnits bs))   -- 16.11

/-- X.691 16: the bits `bs` (as sent, 16.2–16.3) of a bit string type with size view `S`. 16.6: if it
is extensible for PER, a bit, then as without the extension for a root size, or with a
semi-constrained length otherwise (16.11). -/
noncomputable def BitsFields (v : Variant) (S : PSet Nat) (bs : Bits) (fl : FieldList) : Prop :=
  let rootF := bitsRootFields v ((natLeast? S.r).getD 0) (natGreatest? S.r) bs
  S.a bs.length ∧
  if S.ext then
    (S.r bs.length ∧ fl = .unaligned [false] :: rootF) ∨
    (¬ S.r bs.length ∧ fl = .unaligned [true] :: bitsRootFields v 0 none bs)
  else S.r bs.length ∧ fl = rootF

/-- X.691 17.5–17.8: an octet string with sizes between "lb" and "ub" and no extension. -/
def octetsRootFields (v : Variant) (lb : Nat) (ub : Option Nat) (os : Octets) : FieldList :=
  let bs := bitsOf os
  match ub with
  | some 0 => []                                                  -- 17.5
  | some u =>
    if lb = u ∧ u ≤ 2 then [.unaligned bs]                       -- 17.6
    else if lb = u ∧ u < K64 then [.aligned bs]                   -- 17.7
    else lengthDet v (.constrained lb u) (.field true (octetUnits os))  -- 17.8
  | none => lengthDet v (.semi lb) (.field true (octetUnits os))  -- 17.8

/-- X.691 17: an octet string with size view `S` (17.3 as 16.6). -/
noncomputable def OctetsFields (v : Variant) (S : PSet Nat) (os : Octets) (fl : FieldList) : Prop :=
  let rootF := octetsRootFields v ((natLeast? S.r).getD 0) (natGreatest? S.r) os
  S.a os.length ∧
  if S.ext then
    (S.r os.length ∧ fl = .unaligned [false] :: rootF) ∨
    (¬ S.r os.length ∧ fl = .unaligned [true] :: octetsRootFields v 0 none os)
  else S.r os.length ∧ fl = rootF

/-- X.691 30.5.2: the smallest power of two that is at least `b` (1 for 0 and 1). -/
def pow2Ceil (b : Nat) : Nat := if b ≤ 1 then 1 else 2 ^ Nat.size (b - 1)

/-- X.691 30.5.2: "b", the bits per character for an effective permitted alphabet of `N`
characters: B, the least with 2^B ≥ N, in UNALIGNED; the least power of two ≥ B in ALIGNED.

OPEN (ledger X691-9): for an alphabet of one character B is 0, and the least power of 2 that is at
least 0 is 1 (2⁰), so ALIGNED spends one bit per character and UNALIGNED none. -/
def charWidth (v : Variant) (N : Nat) : Nat :=
  let B := bitsFor N
  if v.aligned then pow2Ceil B else B

/-- X.691 30.5.3–30.5.5: the "b"-bit field of character `c` from the effective alphabet `alpha`
(ascending): its value "v" (its code, 30.5.3) if the largest code fits in "b" bits (30.5.4 a)),
else its position in the canonical order (30.5.4 b)). -/
def charField (v : Variant) (alpha : List Nat) (c : Nat) : Bits :=
  let b := charWidth v alpha.length
  let ub := alpha.foldl max 0
  nnbFn b (if ub ≤ 2 ^ b - 1 then c else alpha.idxOf c)

/-- X.691 30.5.6, 30.5.7: the characters' fields, after a length determinant unless the length is
fixed below 64K. -/
def kmBody (v : Variant) (alpha : List Nat) (alb : Nat) (aub : Option Nat) (cs : List Nat) :
    FieldList :=
  let b := charWidth v alpha.length
  let units := cs.map (charField v alpha)
  match aub with
  | some u =>
    if alb = u ∧ u < K64 then
      -- 30.5.6
      [if u * b > 16 then .aligned units.flatten else .unaligned units.flatten]
    else lengthDet v (.constrained alb u) (.field (u * b ≥ 16) units)  -- 30.5.7
  | none => lengthDet v (.semi alb) (.field true units)               -- 30.5.7

/-- X.691 30.2–30.5: the characters `cs` of a known-multiplier type `k` with view `(S, A)`.
30.4: if extensible for PER (the effective size constraint is, 10.3.11 making the alphabet never
so), a bit, then as with no extension for a root size, or with no effective size constraint
otherwise. -/
noncomputable def KmFields (v : Variant) (k : StrType) (P : PSet Nat × PSet Nat) (cs : List Nat)
    (fl : FieldList) : Prop :=
  let S := P.1
  let alpha := effAlphabet k P.2
  (∀ c ∈ cs, c ∈ alpha) ∧ S.a cs.length ∧
  let rootF := kmBody v alpha ((natLeast? S.r).getD 0) (natGreatest? S.r) cs
  if S.ext then
    (S.r cs.length ∧ fl = .unaligned [false] :: rootF) ∨
    (¬ S.r cs.length ∧ fl = .unaligned [true] :: kmBody v alpha 0 none cs)
  else S.r cs.length ∧ fl = rootF

/-- X.691 30.6: a character string type that is not known-multiplier: its base encoding (X.690
8.23.5, with 11.4's restrictions for CANONICAL-PER, 30.6.1) after an unconstrained length in
octets. -/
def OtherStringFields (v : Variant) (k : StrType) (x : Val) (fl : FieldList) : Prop :=
  ∃ os, X690.StringOctets (if v.canonical then .der else .ber) k x os ∧
    fl = unconstrainedLength (.field true (octetUnits os))

/-- The octets of a value whose PER encoding is BER contents octets (24–27) or an unconstrained
octet string, after an unconstrained length in octets. -/
def octetsWithLength (os : Octets) : FieldList := unconstrainedLength (.field true (octetUnits os))

/-! ## The canonical order of tags (10.2, 21, 23.2–23.3) -/

/-- The least of some tags in the canonical order (X.680 8.6). -/
def minTag : List Tag → Option Tag
  | [] => none
  | t :: ts => match minTag ts with
    | some u => some (if Tag.lt u t then u else t)
    | none => some t

/-- X.691 21, 23.3: the tag a type is sorted by: its own outermost tag, or, for an untagged CHOICE,
the smallest tag among the alternatives of its extension root, and of the untagged choice types
nested in them.

OPEN (ledger X691-16): "any untagged choice types nested within" is read as nested within the root
alternatives, through their extension roots. -/
def sortTag (E : Env) : Nat → Scope → Ty → Option Tag
  | 0, _, _ => none
  | n + 1, sc, t =>
    if hasTag E n sc t then (tagsOf E n sc t).bind List.head? else
    match builtin E n sc t with
    | some (sc', .choice root ext) =>
      if autoChoice sc'.mod.header.tagDefault root ext then
        -- 29.5: the root alternatives are tagged [0], [1], …
        if root = [] then none else some ⟨.context, 0⟩
      else minTag (root.filterMap fun a => sortTag E n sc' a.ty)
    | _ => (tagsOf E n sc t).bind List.head?

/-- Sort by a key in the canonical order of tags (a missing key sorts last). -/
def sortByTag {α : Type} (key : α → Option Tag) (xs : List α) : List α :=
  xs.mergeSort fun a b => match key a, key b with
    | some x, some y => !Tag.lt y x
    | some _, none => true
    | none, some _ => false
    | none, none => true

/-! ## SET OF in CANONICAL-PER (22.1) -/

/-- X.691 22.1: a component encoding as compared: its bits, padded with 0 bits to an octet.

OPEN (ledger X691-17): in the ALIGNED variant a component's padding depends on where it starts in
the whole encoding. We compare each component's field-list as if it started on an octet boundary. -/
def setOfKey (v : Variant) (fl : FieldList) : Bits := pad8 (concatFields v.aligned [] fl)

/-- Bit strings compared with the shorter padded with 0 bits (22.1: "with 0-octets added to the
shorter one"), `false` before `true`. -/
def bitsLe : Bits → Bits → Bool
  | [], _ => true
  | xs, [] => xs.all (· == false)
  | x :: xs, y :: ys => if x == y then bitsLe xs ys else (!x && y)

/-! ## The relation -/

/-- An entry of a SEQUENCE or SET, and what the encoder made of it: `none` for no encoding, `some fl`
for its field-list (19.2–19.5). `root`: a root component (an extension addition that is not
OPTIONAL may also be absent: X.680 25.15). -/
def CompOut (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → FieldList → Prop)
    (root : Bool) (cs : List (String × Val)) (en : Entry) (out : Option FieldList) : Prop :=
  let enc (x : Val) : Prop := ∃ fl, rec en.scope en.ty x fl ∧ out = some fl
  match en.presence with
  | .mandatory => match cs.lookup en.name with
    | some x => enc x
    | none => root = false ∧ out = none
  | .optional => match cs.lookup en.name with
    | some x => enc x
    | none => out = none
  -- 19.5: absent if the value is the default value (25.12: an omitted component has it), except
  -- that BASIC-PER may encode a default value of a composite type (3.7.5)
  | .default_ d => ∃ dv, evalVal E n en.scope d dv ∧
    let x := (cs.lookup en.name).getD dv
    (eqv E n en.scope en.ty x dv →
      out = none ∨ (v.canonical = false ∧ isComposite E n en.scope en.ty ∧ enc x)) ∧
    (¬ eqv E n en.scope en.ty x dv → enc x)
where
  /-- X.691 3.7.5: a composite type. -/
  isComposite (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Prop :=
    match builtin E n sc t with
    | some (_, .sequence ..) | some (_, .set ..) | some (_, .sequenceOf _) | some (_, .setOf _)
    | some (_, .choice ..) | some (_, .embeddedPdv) | some (_, .external)
    | some (_, .characterString) => True
    | _ => False

/-- X.691 19.2–19.4: the preamble (a bit per OPTIONAL or DEFAULT root component, after an
"n = ub = lb" length if there are 64K or more) and the root components' field-lists. -/
def seqRootFields (v : Variant) (es : List Entry) (outs : List (Option FieldList)) : FieldList :=
  let pre := (es.zip outs).filterMap fun (e, o) =>
    if e.presence.isMandatory then none else some o.isSome
  let preF : FieldList :=
    if pre = [] then []
    else if pre.length < K64 then [.unaligned pre]
    else lengthDet v (.constrained pre.length pre.length) (.field false (bitUnits pre))
  preF ++ outs.flatMap (·.getD [])

/-- X.691 19.9: an "ExtensionAdditionGroup" is present unless all its components are missing; it is
then encoded as a sequence of its components (19.2–19.6), whose mandatory components are present
(X.680 25.13). -/
def GroupOut (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → FieldList → Prop)
    (cs : List (String × Val)) (es : List Entry) (out : Option FieldList) : Prop :=
  ∃ outs, List.Forall₂ (CompOut E v n rec false cs) es outs ∧
    if outs.all Option.isNone then out = none
    else (∀ p ∈ es.zip outs, p.1.presence.isMandatory → p.2.isSome) ∧
      out = some (seqRootFields v es outs)

/-- X.691 19 (and 21, after the root is sorted): a SEQUENCE value `cs` with root components
`rootEs` (in the order they are encoded) and extension additions `adds` (each its components, and
whether it is a group), with an extension bit if `isExt` (19.1).
- 19.2–19.5: the preamble and the root components;
- 19.6–19.8: if an extension addition is present, a normally small length and a bit-map of the
  additions present;
- 19.9: each present addition as an open type field (11.2). -/
def SeqFields (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → FieldList → Prop)
    (isExt : Bool) (rootEs : List Entry) (adds : List (List Entry × Bool))
    (cs : List (String × Val)) (fl : FieldList) : Prop :=
  -- every component of the value is one of the type's
  (∀ p ∈ cs, p.1 ∈ (rootEs ++ adds.flatMap (·.1)).map (·.name)) ∧
  ∃ rootOuts addOuts,
    List.Forall₂ (CompOut E v n rec true cs) rootEs rootOuts ∧
    List.Forall₂ (fun (a : List Entry × Bool) (o : Option FieldList) =>
      if a.2 then GroupOut E v n rec cs a.1 o
      else ∃ e, a.1 = [e] ∧ CompOut E v n rec false cs e o) adds addOuts ∧
    let present := addOuts.map Option.isSome
    let anyAdd := present.any id
    let rootF := seqRootFields v rootEs rootOuts
    if isExt then
      fl = .unaligned [anyAdd] :: rootF ++
        (if anyAdd then lengthDet v .normallySmall (.field false (bitUnits present)) ++
           addOuts.flatMap fun o => match o with
             | some f => openField v f
             | none => []
         else [])
    else anyAdd = false ∧ fl = rootF

/-- The root components of a SEQUENCE or SET (in textual order, 19.9 NOTE 2), and its extension
additions, each with its components and whether it is a group. -/
def splitEntries (es : List Entry) (ext : Option (List ExtAdd)) : List Entry × List (List Entry × Bool) :=
  (es.filter (·.addition.isNone),
   (ext.getD []).zipIdx.map fun (a, i) => (es.filter (·.addition == some i), a.isGroup))

/-- X.691 20: a sequence-of value whose components encode to `fls`, with size view `S`.
- 20.4: if the PER-visible constraint is extensible, a bit, then as without it for a root count,
  or with a semi-constrained count otherwise;
- 20.5: a count fixed below 64K has no length determinant;
- 20.6: otherwise 11.9 with a constrained count if "ub" is set (below 64K), else semi-constrained. -/
noncomputable def SeqOfFields (v : Variant) (S : PSet Nat) (fls : List FieldList) (fl : FieldList) :
    Prop :=
  let n := fls.length
  let lb := (natLeast? S.r).getD 0
  let ub := (natGreatest? S.r).filter (· < K64)
  let rootF : FieldList := match ub with
    | some u => if lb = u then fls.flatten else lengthDet v (.constrained lb u) (.comps fls)
    | none => lengthDet v (.semi lb) (.comps fls)
  S.a n ∧
  if S.ext then
    (S.r n ∧ fl = .unaligned [false] :: rootF) ∨
    (¬ S.r n ∧ fl = .unaligned [true] :: lengthDet v (.semi 0) (.comps fls))
  else S.r n ∧ fl = rootF

/-- X.691 23: a CHOICE value whose alternative has index `k` among the sorted root alternatives
(`some k` with `rootN` of them) or among the sorted additions (`none`, `addK`), with field-list
`afl`.
- 23.6, 23.7: a root alternative's index as an integer 0 to "n" (no field if only one, 23.4);
- 23.5: an extension bit if there is an extension marker;
- 23.8: an addition's index as a normally small number, and its encoding as an open type field. -/
def ChoiceFields (v : Variant) (isExt : Bool) (rootN : Nat) (idx : Nat ⊕ Nat) (afl : FieldList)
    (fl : FieldList) : Prop :=
  match idx with
  | .inl k =>
    let f := constrainedInt v 0 (rootN - 1 : Nat) k ++ afl
    fl = if isExt then .unaligned [false] :: f else f
  | .inr k => isExt = true ∧ fl = .unaligned [true] :: normallySmall k ++ openField v afl

/-- The identification of an EMBEDDED PDV or CHARACTER STRING value (X.680 36.5, 44.5). -/
def identificationOf : Val → Option Val
  | .seq cs => cs.lookup "identification"
  | _ => none

/-- X.691 28.1 a), 31.1 a): the "predefined" case: every value of the type has, by a PER-visible inner
type constraint (10.3.15), the same `syntaxes` value, or the `fixed` alternative.

OPEN (ledger X691-10): the text decides by the constraint ("constrained … to a single value", "to
the fixed alternative"). We decide by the value set that results, which a constraint produces. -/
def Predefined (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Prop :=
  let vals := (sem E anyHook n sc [] t).all
  (∃ s, ∀ w, vals w → identificationOf w = some (.choice "syntaxes" s)) ∨
  (∀ w, vals w → ∃ x, identificationOf w = some (.choice "fixed" x))

/-- X.691 28.3, 31.3: the associated type (X.680 36.5, 44.5) "with the data-value-descriptor
component removed". -/
def pdvGeneral (dataName : String) : Ty :=
  .sequence [.mk "identification" (.choice identificationAlts none) .mandatory,
             .mk dataName .octetString .mandatory] none []

/-- X.691 29.1, 29.4, Table 1: the components `direct-reference` and `indirect-reference` for an
EXTERNAL value's identification; the other alternatives "cannot occur". -/
def externalRefs : Val → Option (Option (List Nat) × Option Int)
  | .choice "syntax" (.oid o) => some (some o, none)
  | .choice "presentation-context-id" (.int i) => some (none, some i)
  | .choice "context-negotiation" (.seq [("presentation-context-id", .int i),
      ("transfer-syntax", .oid o)]) => some (some o, some i)
  | _ => none

/-- X.691 29: an EXTERNAL value (the associated type of X.680 37.5) as the PER encoding of the
sequence type of 29.1, in an environment of EXPLICIT TAGS:
- the preamble: direct-reference, indirect-reference, data-value-descriptor present (29.3, 29.4);
- direct-reference (24), indirect-reference (13, unconstrained), data-value-descriptor (an
  ObjectDescriptor, which is a GraphicString, 10.6.5 and 30.6);
- `encoding`, a CHOICE of three alternatives tagged [0], [1], [2]: its index in two bits, then the
  data value: single-ASN1-type as an open type field (29.9, 11.2), whose complete encoding is the
  data value's octets, or octet-aligned as an OCTET STRING (29.10). An abstract value's data value
  is octets (X.680 37.5), so the arbitrary alternative (29.8) does not occur.

OPEN (ledger X691-11): 29.6 chooses single-ASN1-type when the data value is of a single ASN.1 type
encoded by PER; whether it is is not part of the abstract value. Both alternatives are allowed. -/
def ExternalFields (v : Variant) (x : Val) (fl : FieldList) : Prop :=
  ∃ ident data, (match x with
    | .seq cs => cs.lookup "identification" = some ident ∧ cs.lookup "data-value" = some (.octets data)
    | _ => False) ∧
  ∃ dref iref, externalRefs ident = some (dref, iref) ∧
  ∃ (descF : Option FieldList),
    (match x with
     | .seq cs => match cs.lookup "data-value-descriptor" with
       | some d => ∃ f, OtherStringFields v .graphic d f ∧ descF = some f
       | none => descF = none
     | _ => False) ∧
  ∃ alt : Nat, (alt = 0 ∨ alt = 1) ∧
    fl = [.unaligned [dref.isSome, iref.isSome, descF.isSome]] ++
      (match dref with | some o => octetsWithLength (X690.oidContents o) | none => []) ++
      (match iref with | some i => unconstrainedInt i | none => []) ++
      descF.getD [] ++
      constrainedInt v 0 2 alt ++ octetsWithLength data

/-- X.691 10.6.5: GeneralizedTime and UTCTime are VisibleString (X.680 46.3, 47.3), with no
PER-visible constraints, and their values in the form X.690 11.7 and 11.8 require.

OPEN (ledger X691-18): as X.690's X690-4: the values are strings (X.680 46.1, 47.1), so a value not
in that form is not converted; it has no PER encoding, in BASIC-PER too. -/
noncomputable def UsefulTimeFields (v : Variant) (canon : List Char → Prop) (x : Val)
    (fl : FieldList) : Prop :=
  ∃ cs, x = .chars cs ∧ canon (cs.map Char.ofNat) ∧
    KmFields v .visible (PSet.univ, .plain fun c => visibleChars.mem c) cs fl

/-- X.691 12–31: the field-list of a value `x` of the built-in type `bt` (read in `sc'`), which the
type notation `t` (read in `sc`) denotes. `rec` encodes the components, at one less fuel. -/
noncomputable def perB (E : Env) (v : Variant) (n : Nat) (rec : Scope → Ty → Val → FieldList → Prop)
    (sc : Scope) (t : Ty) (sc' : Scope) (bt : Ty) (x : Val) (fl : FieldList) : Prop :=
  match bt, x with
  -- 12
  | .boolean, .bool b => fl = [.unaligned [b]]
  -- 13
  | .integer _, .int i => IntFields v (pInt E n sc t) i fl
  -- 14: no PER-visible constraints apply
  | .enumerated root ext, .enum id => EnumFields v root ext sc'.mod.header.extImplied id fl
  -- 15: the CER/DER contents octets, after an unconstrained length
  | .real, .real r => ∃ os, X690.RealContents .der r os ∧ fl = octetsWithLength os
  -- 16
  | .bitString named, .bits bs =>
    let S := pSize E n sc t
    ∃ sent, (if named = [] then sent = bs else NamedBitsSent S bs sent) ∧ BitsFields v S sent fl
  -- 17
  | .octetString, .octets os => OctetsFields v (pSize E n sc t) os fl
  -- 18
  | .null, .null => fl = []
  -- 19
  | .sequence r e r2, .seq cs =>
    let (rootEs, adds) := splitEntries (entries E n sc' r e r2) e
    SeqFields E v n rec (e.isSome || sc'.mod.header.extImplied) rootEs adds cs fl
  -- 21: the root sorted by tag (with automatic tagging, 25.10), the additions in textual order
  | .set r e r2, .seq cs =>
    let tagged := entryTags E n sc' r e r2
    let auto := autoSeq sc'.mod.header.tagDefault r e r2
    let key (p : Entry × Option (List Tag)) : Option Tag :=
      if auto then p.2.bind List.head? else sortTag E n p.1.scope p.1.ty
    let rootEs := (sortByTag key (tagged.filter (·.1.addition.isNone))).map (·.1)
    let adds := (splitEntries (tagged.map (·.1)) e).2
    SeqFields E v n rec (e.isSome || sc'.mod.header.extImplied) rootEs adds cs fl
  -- 20
  | .sequenceOf el, .seqOf vs =>
    ∃ fls, List.Forall₂ (rec sc' el) vs fls ∧ SeqOfFields v (pSize E n sc t) fls fl
  -- 22: the components in some order; in CANONICAL-PER, ascending (22.1). A SET OF value is
  -- unordered (X.680 28), so BASIC-PER may send it in any order (22.2).
  | .setOf el, .setOf vs =>
    ∃ ws fls, ws.Perm vs ∧ List.Forall₂ (rec sc' el) ws fls ∧
      (v.canonical = true → fls.Pairwise fun a b => bitsLe (setOfKey v a) (setOfKey v b)) ∧
      SeqOfFields v (pSize E n sc t) fls fl
  -- 23: alternatives in the canonical order of their tags, root and additions apart (23.2).
  -- OPEN (ledger X691-19): 23.2 numbers the additions "similarly"; we sort them by tag too, which
  -- X.680 29.7 makes their textual order.
  | .choice root ext, .choice nm y =>
    let alts := altTags E n sc' root ext
    let auto := autoChoice sc'.mod.header.tagDefault root ext
    let key (p : Alt × Option (List Tag)) : Option Tag :=
      if auto then p.2.bind List.head? else sortTag E n sc' p.1.ty
    let rootS := sortByTag key (alts.take root.length)
    let addS := sortByTag key (alts.drop root.length)
    let isExt := ext.isSome || sc'.mod.header.extImplied
    ∃ a afl, rec sc' a.ty y afl ∧
      ((∃ k, (rootS.map (·.1.name)).idxOf? nm = some k ∧ rootS[k]?.map (·.1) = some a ∧
          ChoiceFields v isExt rootS.length (.inl k) afl fl) ∨
       (∃ k, (addS.map (·.1.name)).idxOf? nm = some k ∧ addS[k]?.map (·.1) = some a ∧
          ChoiceFields v isExt rootS.length (.inr k) afl fl))
  -- 24–27: the BER contents octets, after a semi-constrained length in octets
  | .objectIdentifier, .oid arcs => fl = octetsWithLength (X690.oidContents arcs)
  | .relativeOid, .oid arcs => fl = octetsWithLength (X690.relOidContents arcs)
  | .oidIri, .iri arcs => fl = octetsWithLength (X690.iriContents arcs)
  | .relativeOidIri, .iri arcs => fl = octetsWithLength (X690.relIriContents arcs)
  -- 28
  | .embeddedPdv, .seq cs =>
    if Predefined E n sc t then ∃ os, cs.lookup "data-value" = some (.octets os) ∧
      OctetsFields v PSet.univ os fl
    else rec (.ofModule assocModule) (pdvGeneral "data-value")
      (.seq (cs.filter (·.1 ≠ "data-value-descriptor"))) fl
  -- 29
  | .external, _ => ExternalFields v x fl
  -- 30
  | .restricted k, _ =>
    if k.knownMultiplier then ∃ cs, x = .chars cs ∧ KmFields v k (pStr E n sc t) cs fl
    else OtherStringFields v k x fl
  -- 31
  | .characterString, .seq cs =>
    if Predefined E n sc t then ∃ os, cs.lookup "string-value" = some (.octets os) ∧
      OctetsFields v PSet.univ os fl
    else rec (.ofModule assocModule) (pdvGeneral "string-value")
      (.seq (cs.filter (·.1 ≠ "data-value-descriptor"))) fl
  -- 32: as a value of an encoding type (`Time.lean`)
  | .time, .time tv | .date, .time tv | .timeOfDay, .time tv | .dateTime, .time tv
  | .duration, .time tv =>
    ∃ name w, TimeAs (pTime E n sc t).a tv name w ∧ rec (.ofModule timeEncModule) (.ref name) w fl
  -- 10.6.5
  | .generalizedTime, _ => UsefulTimeFields v X690.GenTimeCanon x fl
  | .utcTime, _ => UsefulTimeFields v X690.UtcTimeCanon x fl
  | .objectDescriptor, _ => OtherStringFields v .graphic x fl
  -- 11.2: an open type's value is a value of some type, encoded as an open type field
  | .openType, .open_ ty y => ∃ sc'' afl, rec sc'' ty y afl ∧ fl = openField v afl
  | _, _ => False

/-- X.691 10.5: `x`, a value of the type `t` read in scope `sc`, encodes to the field-list `fl`
under variant `v`, at fuel `n`. Tags, references, selections (10.6.2) and constraints are seen
through: the encoding is that of the built-in type, with the PER view of `t`. -/
noncomputable def per (E : Env) (v : Variant) : Nat → Scope → Ty → Val → FieldList → Prop
  | 0, _, _, _, _ => False
  | n + 1, sc, t, x, fl => match builtin E n sc t with
    | some (sc', bt) => perB E v n (per E v n) sc t sc' bt x fl
    | none => False

/-! ## The rule -/

/-- X.691 33.2: the object identifiers of the four PER transfer syntaxes. -/
def variantOfOid : List Nat → Option Variant
  | [2, 1, 3, 0, 0] => some ⟨true, false⟩
  | [2, 1, 3, 0, 1] => some ⟨false, false⟩
  | [2, 1, 3, 1, 0] => some ⟨true, true⟩
  | [2, 1, 3, 1, 1] => some ⟨false, true⟩
  | _ => none

/-- X.682 11.4 for PER: the values of an OCTET STRING or BIT STRING with a contents constraint are
the complete encodings (11.1.1 a), b)) of the contained type's values `tvals`, under the variant in
use or, with ENCODED BY one of the PER object identifiers, that variant.

OPEN (ledger X691-12): ENCODED BY an object identifier that is not one of 33.2's names other
encoding rules, which PER does not define; such a constraint then admits every string. A contents
constraint with only ENCODED BY likewise admits every string. -/
def perHook (v : Variant) (E : Env) : ContentsHook := fun sc t enc tvals x =>
  let ok (v' : Variant) : Prop := match t with
    | some ty => ∃ y, tvals y ∧ Eventually fun n => ∃ fl, per E v' n sc ty y fl ∧
        ((∃ os, x = .octets os ∧ bitsOf os = complete v' .other fl) ∨
         (∃ bs, x = .bits bs ∧ bs = complete v' .bitString fl))
    | none => True
  match enc with
  | none => ok v
  | some (.oid o) => match variantOfOid o with
    | some v' => ok v'
    | none => True
  | some _ => True

/-- PER, variant `v`, as an encoding rule: a value of the type, and the complete encoding (11.1) of
its field-list, as the outermost value carried in octets (11.1.1 a), c), d), e)). -/
noncomputable def rule (v : Variant) : EncodingRule where
  hook := perHook v
  Encodes E m t x bs := Has E (perHook v E) m t x ∧
    Eventually fun n => ∃ fl, per E v n (.ofModule m) t x fl ∧ bs = complete v .other fl

end Asn1.X691
