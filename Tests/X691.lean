import Asn1.X691.Encode

/-! Checks of X.691's procedures as `Encode.lean` composes them.

The relation `per` takes its bounds and alphabets from the PER view of a type, which is defined by
least and greatest elements of sets (noncomputable). The tests below compose the same computable
procedures the relation names, with the bounds and alphabets X.691 gives for each component, and
compare the complete encodings with the worked examples of Annex A. A few `example`s check that
the relation itself relates small values as the text says. -/

open Asn1 Asn1.X680 Asn1.X691

namespace Asn1.X691.Test

def hexBits (s : String) : Bits :=
  (s.toList.filter fun c => c.isDigit || ('A' ≤ c && c ≤ 'F')).flatMap fun c =>
    let d := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10
    nnbFn 4 d

def chars (s : String) : List Nat := s.toList.map Char.toNat

def AL : Variant := ⟨true, false⟩
def UN : Variant := ⟨false, false⟩

/-- VisibleString with no PER-visible constraint: 95 characters (30.5.1). -/
def visAlpha : List Nat := List.range' 32 95

/-- A VisibleString with no constraint (30.5.7: a semi-constrained length). -/
def vis (v : Variant) (s : String) : FieldList := kmBody v visAlpha 0 none (chars s)

/-! ## A.1: no subtype constraints -/

/-- `Name ::= SEQUENCE { givenName, initial, familyName VisibleString }`: no preamble (19.2). -/
def name1 (v : Variant) (g i f : String) : FieldList := vis v g ++ vis v i ++ vis v f

/-- `ChildInformation ::= SET { name Name, dateOfBirth [0] Date }`: [APPLICATION 1] before [0] (21). -/
def child1 (v : Variant) (g i f d : String) : FieldList := name1 v g i f ++ vis v d

/-- `PersonnelRecord`: the SET in canonical tag order (21): name [APPLICATION 1], number
[APPLICATION 2], title [0], dateOfHire [1], nameOfSpouse [2], children [3], after a one-bit preamble
for children, which is DEFAULT {} and not empty (19.2, 19.5). -/
def record1 (v : Variant) : FieldList :=
  [.unaligned [true]] ++ name1 v "John" "P" "Smith" ++ unconstrainedInt 51 ++ vis v "Director" ++
    vis v "19710917" ++ name1 v "Mary" "T" "Smith" ++
    lengthDet v (.semi 0) (.comps [child1 v "Ralph" "T" "Smith" "19571111",
                                  child1 v "Susan" "B" "Jones" "19590717"])

-- A.1.3.1
#guard complete AL .other (record1 AL) = hexBits
  "80044A6F 686E0150 05536D69 74680133 08446972 6563746F 72083139 37313039
   3137044D 61727901 5405536D 69746802 0552616C 70680154 05536D69 74680831
   39353731 31313105 53757361 6E014205 4A6F6E65 73083139 35393037 3137"
-- A.1.4.1
#guard complete UN .other (record1 UN) = hexBits
  "824ADFA3 700D005A 7B74F4D0 02661113 4F2CB8FA 6FE410C5 CB762C1C B16E0937
   0F2F2035 0169EDD3 D340102D 2C3B3868 01A80B4F 6E9E9A02 18B96ADD 8B162C41
   69F5E787 700C2059 5BF765E6 10C5CB57 2C1BB16E"

/-! ## A.2: subtype constraints -/

/-- `NameString ::= VisibleString (FROM ("a".."z" | "A".."Z" | "-.") ^ SIZE (1..64))`: the effective
permitted alphabet (10.3.12), in canonical order. -/
def nameAlpha : List Nat :=
  (chars "-." ++ List.range' 65 26 ++ List.range' 97 26).mergeSort (fun a b => decide (a ≤ b))

/-- `Date ::= VisibleString (FROM ("0".."9") ^ SIZE (8))` -/
def dateAlpha : List Nat := List.range' 48 10

def nameStr (v : Variant) (s : String) : FieldList := kmBody v nameAlpha 1 (some 64) (chars s)
def initial (v : Variant) (s : String) : FieldList := kmBody v nameAlpha 1 (some 1) (chars s)
def date (v : Variant) (s : String) : FieldList := kmBody v dateAlpha 8 (some 8) (chars s)

def name2 (v : Variant) (g i f : String) : FieldList := nameStr v g ++ initial v i ++ nameStr v f
def child2 (v : Variant) (g i f d : String) : FieldList := name2 v g i f ++ date v d

def record2 (v : Variant) : FieldList :=
  [.unaligned [true]] ++ name2 v "John" "P" "Smith" ++ unconstrainedInt 51 ++ vis v "Director" ++
    date v "19710917" ++ name2 v "Mary" "T" "Smith" ++
    lengthDet v (.semi 0) (.comps [child2 v "Ralph" "T" "Smith" "19571111",
                                  child2 v "Susan" "B" "Jones" "19590717"])

-- 30.5.2: 54 characters take 6 bits UNALIGNED and 8 ALIGNED; ten digits take 4 bits
#guard nameAlpha.length = 54 ∧ charWidth UN 54 = 6 ∧ charWidth AL 54 = 8 ∧ charWidth AL 10 = 4
-- A.2.3.1
#guard complete AL .other (record2 AL) = hexBits
  "864A6F68 6E501053 6D697468 01330844 69726563 746F7219 7109170C 4D617279
   5410536D 69746802 1052616C 70685410 536D6974 68195711 11105375 73616E42
   104A6F6E 65731959 0717"
-- A.2.4.1
#guard complete UN .other (record2 UN) = hexBits
  "865D51D2 888A5125 F1809984 44D3CB2E 3E9BF90C B8848B86 7396E8A8 8A5125F1
   81089B93 D71AA229 4497C632 AE222222 985CE521 885D54C1 70CAC838 B8"

/-! ## A.3: extension markers -/

/-- `NameString ::= VisibleString (FROM (…) ^ SIZE (1..64, ...))`: a root length, so a 0 bit (30.4). -/
def ns3 (v : Variant) (s : String) : FieldList := .unaligned [false] :: nameStr v s

/-- `Name ::= SEQUENCE { …, ... }`: no extension values (19.1); `initial` is `NameString (SIZE (1))`,
whose serially applied SIZE removes the extensibility (10.3.20). -/
def name3 (v : Variant) (g i f : String) : FieldList :=
  .unaligned [false] :: ns3 v g ++ initial v i ++ ns3 v f

/-- `Date ::= VisibleString (FROM ("0".."9") ^ SIZE (8, ..., 9..20))` -/
def date3 (v : Variant) (s : String) : FieldList := .unaligned [false] :: date v s

/-- `ChildInformation ::= SET { name, dateOfBirth, ..., sex [1] IMPLICIT ENUMERATED {…} OPTIONAL }`:
with `sex` present, the extension bit, a bit-map of one after a normally small length (19.8), and
`female` (index 1 of 3) as an open type field (19.9). -/
def child3 (v : Variant) (g i f d : String) (sex : Option Nat) : FieldList :=
  match sex with
  | none => .unaligned [false] :: name3 v g i f ++ date3 v d
  | some k => .unaligned [true] :: name3 v g i f ++ date3 v d ++
      lengthDet v .normallySmall (.field false [[true]]) ++ openField v (constrainedInt v 0 2 k)

def record3 (v : Variant) : FieldList :=
  [.unaligned [false], .unaligned [true]] ++ name3 v "John" "P" "Smith" ++
    (.unaligned [false] :: constrainedInt v 0 9999 51) ++ vis v "Director" ++
    date3 v "19710917" ++ name3 v "Mary" "T" "Smith" ++
    -- SEQUENCE (SIZE (2, ...)) OF: a root count fixed at 2, no length (20.4, 20.5)
    (.unaligned [false] :: child3 v "Ralph" "T" "Smith" "19571111" none ++
      child3 v "Susan" "B" "Jones" "19590717" (some 1))

-- A.3.3.1
#guard complete AL .other (record3 AL) = hexBits
  "40C04A6F 686E5008 536D6974 68000033 08446972 6563746F 72001971 0917034D
   61727954 08536D69 74680100 52616C70 68540853 6D697468 00195711 11820053
   7573616E 42084A6F 6E657300 19590717 010140"
-- A.3.4.1
#guard complete UN .other (record3 UN) = hexBits
  "40CBAA3A 5108A512 5F180330 889A7965 C7D37F20 CB8848B8 19CE5BA2 A114A24B
   E3011372 7AE35422 94497C61 95711118 22985CE5 21842EAA 60B832B2 0E2E0202 80"

/-! ## A.4: extension addition groups -/

/-- `Ax ::= SEQUENCE { a INTEGER (250..253), b BOOLEAN, c CHOICE { d INTEGER, ..., [[ e BOOLEAN,
f IA5String ]], ... }, ..., [[ g NumericString (SIZE(3)), h BOOLEAN OPTIONAL ]], ..., i BMPString
OPTIONAL, j PrintableString OPTIONAL }`, value `{ a 253, b TRUE, c e : TRUE, g "123", h TRUE }`:
- the extension bit, the bit-map for i and j (19.9 NOTE 2: after the root), a, b;
- c: an extension bit and `e`, addition index 0, as an open type field (23.8);
- one extension addition, the group, as a sequence (its bit-map for h, g, h) in an open type field
  (19.9). -/
def recordAx (v : Variant) : FieldList :=
  [.unaligned [true], .unaligned [false, false]] ++ constrainedInt v 250 253 253 ++
    [.unaligned [true]] ++ (.unaligned [true] :: normallySmall 0 ++ openField v [.unaligned [true]]) ++
    lengthDet v .normallySmall (.field false [[true]]) ++
    openField v ([.unaligned [true]] ++ kmBody v (chars " 0123456789") 3 (some 3) (chars "123") ++
      [.unaligned [true]])

-- A.4.3.1, A.4.4.1
#guard complete AL .other (recordAx AL) = hexBits "9E000180 010291A4"
#guard complete UN .other (recordAx UN) = hexBits "9E000600 040A4690"

/-! ## Single procedures -/

-- 13.2.6 a) NOTE: `INTEGER (256..1234567)`, value 256, ALIGNED: a 2-bit length (00, one octet),
-- then the octet 00000000
#guard constrainedInt AL 256 1234567 256 =
  [.unaligned [false, false], .aligned (nnbFn 8 0)]
-- 14.1: enumeration indices sort by value
#guard enumIndex [("a", 5), ("b", 1), ("c", 3)] "a" = some 2
#guard enumIndex [("a", 5), ("b", 1), ("c", 3)] "b" = some 0
-- 30.5.4 b): NumericString's 11 characters take 4 bits and their positions
#guard charField UN (chars " 0123456789") '5'.toNat = nnbFn 4 6
-- 30.5.4 a): IA5String's 128 characters fit their codes in 7 bits
#guard charField UN (List.range 128) 'A'.toNat = nnbFn 7 65
-- 22.1: compared as bits padded with zeros
#guard bitsLe [true] [true, false, false] && !bitsLe [true, true] [true]
-- 10.2, X.680 8.6: the canonical order
#guard minTag [⟨.context, 3⟩, ⟨.application, 7⟩, ⟨.context, 1⟩] = some ⟨.application, 7⟩
-- 33.2
#guard variantOfOid [2, 1, 3, 1, 1] = some ⟨false, true⟩

/-! ## The relation on small values -/

def m0 : Module := { name := "M", header := ⟨.explicit, false⟩ }

-- 12: a BOOLEAN is one bit
example : per [] AL 3 (.ofModule m0) .boolean (.bool true) [.unaligned [true]] := by
  simp [per, builtin, perB]

-- 18: NULL adds nothing
example : per [] UN 3 (.ofModule m0) (.tagged ⟨.context, 4⟩ .explicit .null) .null [] := by
  simp [per, builtin, perB]

-- 24: an object identifier is its BER contents octets after a length
example : per [] AL 2 (.ofModule m0) .objectIdentifier (.oid [2, 999, 3])
    (octetsWithLength (X690.oidContents [2, 999, 3])) := by
  simp [per, builtin, perB]

-- 13.2.2 through the PER view: `INTEGER (0..7)` has root 0..7 (10.3.18), so "lb" 0 and "ub" 7
def t07 : Ty := .constrained (.integer []) (.mk (.elem (.range (.val (.int 0)) false (.val (.int 7)) false)) false none)

theorem pInt_t07 : pInt [] 3 (.ofModule m0) t07 = PSet.plain fun i => 0 ≤ i ∧ i ≤ 7 := by
  simp [pInt, view, t07, intCons, consDep, esDep, elDep, evalC, evalES, intAtom, psetAlg, PSet.ofSpecs,
    PSet.plain, PSet.univ, EvalBound, evalVal, RangeHas, InRange, Val.le, stepTy]

theorem least_07 : least? (fun i => 0 ≤ i ∧ i ≤ 7) = some 0 := by
  have h : IsLeast {x : Int | 0 ≤ x ∧ x ≤ 7} 0 := ⟨by simp, fun x hx => hx.1⟩
  unfold least?; rw [dite_eq_left_of_eq_true (eq_true ⟨0, h⟩)]; congr 1
  exact (Classical.choose_spec (p := fun l => IsLeast {x : Int | 0 ≤ x ∧ x ≤ 7} l) ⟨0, h⟩).unique h

theorem greatest_07 : greatest? (fun i => 0 ≤ i ∧ i ≤ 7) = some 7 := by
  have h : IsGreatest {x : Int | 0 ≤ x ∧ x ≤ 7} 7 := ⟨by simp, fun x hx => hx.2⟩
  unfold greatest?; rw [dite_eq_left_of_eq_true (eq_true ⟨7, h⟩)]; congr 1
  exact (Classical.choose_spec (p := fun l => IsGreatest {x : Int | 0 ≤ x ∧ x ≤ 7} l) ⟨7, h⟩).unique h

-- 13.2.2, 11.5.7.1: INTEGER (0..7), value 5, ALIGNED: three bits 101
example : per [] ⟨true, false⟩ 4 (.ofModule m0) t07 (.int 5) [.unaligned (nnbFn 3 5)] := by
  have hb : builtin [] 3 (.ofModule m0) t07 = some (.ofModule m0, .integer []) := by
    simp [t07, builtin]
  rw [per, hb]
  show IntFields _ (pInt [] 3 (.ofModule m0) t07) 5 _
  rw [pInt_t07]
  simp [IntFields, PSet.plain, intRootFields, least_07, greatest_07, constrainedInt, constrainedWhole,
    bitsFor]
  decide

end Asn1.X691.Test
