import Asn1.X690.Ber
import Asn1.X690.Decode

/-! Checks of BER, CER and DER against X.690's own examples. Each example is a proof that the
octets X.690 prints are an encoding under the relation (and, where the example shows a BER-only
form, that DER rejects it). -/

open Asn1 Asn1.X690 Asn1.X680

def hex (os : Octets) : List Nat := os.map (·.val)
def ascii (s : String) : Octets := s.toList.map fun c => octet c.toNat
def str (s : String) : Val := .chars (s.toList.map Char.toNat)

/-! ## Identifier and length octets (8.1.2, 8.1.3) -/

-- 8.1.3.4 EXAMPLE: L = 38 in the short form
#guard hex (lengthOctets .short 38) = [0x26]
-- 8.1.3.5 EXAMPLE: L = 201 in the long form, 10000001 11001001
#guard hex (lengthOctets (.long 1) 201) = [0x81, 0xC9]
-- 8.1.2.4: a tag number of 31 or more takes the high-tag-number form
#guard hex (identOctets ⟨.context, 31⟩ false) = [0x9F, 0x1F]
#guard hex (identOctets ⟨.application, 200⟩ true) = [0x7F, 0x81, 0x48]
-- 10.1: DER uses the fewest length octets
example : ¬ LenForm.Allowed .der false .short 128 := by simp [LenForm.Allowed, minLenForm]
example : LenForm.Allowed .der false (.long 1) 128 := by simp [LenForm.Allowed, minLenForm, LenForm.Fits]; decide
-- 8.1.3.5 NOTE 2: BER may use more length octets than necessary
example : LenForm.Allowed .ber false (.long 2) 5 := by simp [LenForm.Allowed, LenForm.Fits]
-- 8.1.3.2 a): never the indefinite form for a primitive encoding
example : ¬ LenForm.Allowed .ber false .indefinite 5 := by simp [LenForm.Allowed]

/-! ## BOOLEAN (8.2, 11.1) -/

def expl : Module := { name := "X", header := ⟨.explicit, false⟩ }

-- 8.2.2 EXAMPLE: TRUE as 01 01 FF
example : ber [expl] .der 1 (.ofModule expl) .boolean (.bool true) (.prim (univ 1) .short [255]) := by
  simp [ber, Prim, BoolContents, Profile.restricted]
#guard hex (Node.prim (univ 1) .short [255]).octets = [0x01, 0x01, 0xFF]
-- 8.2.2: any non-zero octet in BER; 11.1: only FF in DER
example : ber [expl] .ber 1 (.ofModule expl) .boolean (.bool true) (.prim (univ 1) .short [1]) := by
  simp [ber, Prim, BoolContents, Profile.restricted]
example : ¬ ber [expl] .der 1 (.ofModule expl) .boolean (.bool true) (.prim (univ 1) .short [1]) := by
  simp [ber, Prim, BoolContents, Profile.restricted]

/-! ## INTEGER (8.3) -/

#guard hex (intContents 0) = [0]
#guard hex (intContents 127) = [0x7F]
#guard hex (intContents 128) = [0x00, 0x80]
#guard hex (intContents (-128)) = [0x80]
#guard hex (intContents (-129)) = [0xFF, 0x7F]
-- 8.3.2: 00 7F is not an encoding of 127 (the first nine bits are all zero)
example : ¬ IntContents 127 [0, 127] := by
  simp [IntContents, TcMinOctets, bitsOf, octetBits]; decide

/-! ## BIT STRING (8.6) -/

/-- '0A3B5F291CD'H, 44 bits -/
def bits0A3B : Bits := bitsOf ([0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0].map octet) |>.take 44

-- 8.6.4.2: primitive, 03 07 04 0A 3B 5F 29 1C D0
example : ber [expl] .der 2 (.ofModule expl) (.bitString []) (.bits bits0A3B)
    (.prim (univ 3) .short ([0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0].map octet)) := by
  simp only [ber, bitsEnc, ite_true]
  exact ⟨bits0A3B, rfl, Or.inl ⟨.short, _, rfl,
    ⟨4, [false, false, false, false], by decide, rfl, by decide, by decide, by decide, fun _ => rfl⟩,
    by decide, by decide⟩⟩

#guard hex (Node.prim (univ 3) .short ([0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0].map octet)).octets =
  [0x03, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0]

/-- 8.6.4.2: the constructed form, 23 80 (03 03 00 0A 3B) (03 05 04 5F 29 1C D0) 00 00 -/
def bitsCons : Node :=
  .cons (univ 3) .indefinite
    [.prim (univ 3) .short ([0x00, 0x0A, 0x3B].map octet),
     .prim (univ 3) .short ([0x04, 0x5F, 0x29, 0x1C, 0xD0].map octet)]

#guard hex bitsCons.octets =
  [0x23, 0x80, 0x03, 0x03, 0x00, 0x0A, 0x3B, 0x03, 0x05, 0x04, 0x5F, 0x29, 0x1C, 0xD0, 0x00, 0x00]

example : ber [expl] .ber 3 (.ofModule expl) (.bitString []) (.bits bits0A3B) bitsCons ∧
    bitsCons.LenOk .ber := by
  refine ⟨?_, ?_⟩
  · simp only [ber, bitsEnc, ite_true]
    refine ⟨bits0A3B, rfl, Or.inr ⟨.indefinite, _, [bits0A3B.take 16, bits0A3B.drop 16], rfl,
      by decide, by decide, ?_, fun h => absurd h (by decide)⟩⟩
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · exact Or.inl ⟨.short, _, rfl, ⟨0, [], by decide, rfl, by decide, by decide, by decide,
        by decide⟩, by decide, by decide⟩
    · exact Or.inl ⟨.short, _, rfl, ⟨4, [false, false, false, false], by decide, rfl, by decide,
        by decide, by decide, by decide⟩, by decide, by decide⟩
  · simp [bitsCons, Node.LenOk, Node.LenOkList, LenForm.Allowed, LenForm.Fits]

-- 10.2: DER never uses the constructed form
example : ¬ ber [expl] .der 3 (.ofModule expl) (.bitString []) (.bits bits0A3B) bitsCons := by
  simp [ber, bitsEnc, bitsCons]

/-! ## Tagging (8.14) -/

/-- 8.14 EXAMPLE, in an explicit tagging environment. -/
def m814 : Module where
  name := "M"
  header := ⟨.explicit, false⟩
  types := [("Type1", .restricted .visible),
            ("Type2", .tagged ⟨.application, 3⟩ .implicit (.ref "Type1")),
            ("Type3", .tagged ⟨.context, 2⟩ .default_ (.ref "Type2")),
            ("Type4", .tagged ⟨.application, 7⟩ .implicit (.ref "Type3")),
            ("Type5", .tagged ⟨.context, 2⟩ .implicit (.ref "Type2"))]

def sc814 : Scope := .ofModule m814
def jones : Node := .prim (univ 26) .short (ascii "Jones")
def jones2 : Node := .prim ⟨.application, 3⟩ .short (ascii "Jones")
def jones3 : Node := .cons ⟨.context, 2⟩ .short [jones2]


theorem t1 (n : Nat) (h : resolveTy [m814] (n + 2) sc814 none "Type1" [] = some (sc814, .restricted .visible)) :
    ber [m814] .der (n + 3) sc814 (.ref "Type1") (str "Jones") jones := by
  simp only [ber, h]
  exact ⟨ascii "Jones", by simp [StringOctets, str, ascii], 26, rfl, by simp [octetsEnc, jones]⟩

-- Type1: 1A 05 4A 6F 6E 65 73
#guard hex jones.octets = [0x1A, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]

-- Type2: 43 05 4A 6F 6E 65 73
theorem t2 : ber [m814] .der 10 sc814 (.ref "Type2") (str "Jones") jones2 := by
  simp only [ber]
  exact ⟨jones, t1 5 (by rfl), by simp [isExplicit, jones, jones2, Node.retag]⟩
#guard hex jones2.octets = [0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]

-- Type3: A2 07 43 05 4A 6F 6E 65 73 (explicit: the module's default)
theorem t3 : ber [m814] .der 11 sc814 (.ref "Type3") (str "Jones") jones3 := by
  simp only [ber]
  refine ⟨jones2, ?_, ?_⟩
  · simp only [ber]
    exact ⟨jones, t1 4 (by rfl), by simp [isExplicit, jones, jones2, Node.retag]⟩
  · have : isExplicit [m814] 9 (Scope.ofModule sc814.mod) .default_ (.ref "Type2") = true := by rfl
    simp [this, jones3]
#guard hex jones3.octets = [0xA2, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
-- Type4: 67 07 43 05 …, Type5: 82 05 4A 6F 6E 65 73
#guard hex (jones3.retag ⟨.application, 7⟩).octets = [0x67, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
#guard hex (jones2.retag ⟨.context, 2⟩).octets = [0x82, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]

/-! ## SEQUENCE (8.9) -/

/-- 8.9.3 EXAMPLE: `SEQUENCE {name IA5String, ok BOOLEAN}`, `{name "Smith", ok TRUE}`, as
30 0A 16 05 "Smith" 01 01 FF. -/
def seqTy : Ty := .sequence [.mk "name" (.restricted .ia5) .mandatory, .mk "ok" .boolean .mandatory] none []
def smithVal : Val := .seq [("name", str "Smith"), ("ok", .bool true)]
def smithNode : Node :=
  .cons (univ 16) .short [.prim (univ 22) .short (ascii "Smith"), .prim (univ 1) .short [255]]

#guard hex smithNode.octets =
  [0x30, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF]

example : ber [expl] .der 4 (.ofModule expl) seqTy smithVal smithNode ∧ smithNode.LenOk .der := by
  refine ⟨?_, by simp [smithNode, Node.LenOk, Node.LenOkList, LenForm.Allowed, minLenForm, LenForm.Fits,
    Node.octetsList, Node.octets, identOctets, lengthOctets, ascii, univ, TagClass.bits87]⟩
  have hc : compTys [expl] 3 (.ofModule expl) [.mk "name" (.restricted .ia5) .mandatory,
      .mk "ok" .boolean .mandatory] none [] =
    [(⟨.ofModule expl, "name", .restricted .ia5, .mandatory, none, false⟩, .restricted .ia5),
     (⟨.ofModule expl, "ok", .boolean, .mandatory, none, false⟩, .boolean)] := by rfl
  simp only [seqTy, smithVal, ber, hc]
  refine ⟨.short, [((⟨.ofModule expl, "name", .restricted .ia5, .mandatory, none, false⟩, .restricted .ia5),
      .prim (univ 22) .short (ascii "Smith")),
    ((⟨.ofModule expl, "ok", .boolean, .mandatory, none, false⟩, .boolean), .prim (univ 1) .short [255])],
    rfl, ?_, [some (str "Smith"), some (.bool true)], ?_, ?_⟩
  · simp
  · simp [CompChoice, IsDefault, Profile.restricted]
    all_goals rfl
  · refine List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
    · exact ⟨ascii "Smith", by simp [StringOctets, str, ascii], 22, rfl, by simp [octetsEnc]⟩
    · simp [ber, Prim, BoolContents, Profile.restricted]

/-! ## Object identifiers (8.19, 8.20) -/

-- 8.19.5 EXAMPLE: {2 999 3} as 06 03 88 37 03
#guard hex (Node.prim (univ 6) .short (oidContents [2, 999, 3])).octets = [0x06, 0x03, 0x88, 0x37, 0x03]
-- 8.20.5 EXAMPLE: {8571 3 2} as 0D 04 C2 7B 03 02
#guard hex (Node.prim (univ 13) .short (relOidContents [8571, 3, 2])).octets =
  [0x0D, 0x04, 0xC2, 0x7B, 0x03, 0x02]

/-! ## Character strings (8.23) -/

/-- 8.23.5 EXAMPLE: "Jones" as a VisibleString, constructed with definite length:
3A 09 (04 03 4A 6F 6E) (04 02 65 73). -/
def jonesDef : Node := .cons (univ 26) .short
  [.prim (univ 4) .short (ascii "Jon"), .prim (univ 4) .short (ascii "es")]
#guard hex jonesDef.octets = [0x3A, 0x09, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73]

example : ber [expl] .ber 3 (.ofModule expl) (.restricted .visible) (str "Jones") jonesDef ∧
    jonesDef.LenOk .ber := by
  refine ⟨?_, by simp [jonesDef, Node.LenOk, Node.LenOkList, LenForm.Allowed, LenForm.Fits,
    Node.octetsList, Node.octets, identOctets, lengthOctets, ascii, univ, TagClass.bits87]⟩
  simp only [ber]
  refine ⟨ascii "Jones", by simp [StringOctets, str, ascii], 26, rfl, ?_⟩
  simp only [octetsEnc]
  refine Or.inr ⟨.short, _, [ascii "Jon", ascii "es"], rfl, by decide, by decide, ?_, fun h => by cases h⟩
  exact List.Forall₂.cons (Or.inl ⟨.short, rfl, fun h => by cases h⟩)
    (List.Forall₂.cons (Or.inl ⟨.short, rfl, fun h => by cases h⟩) List.Forall₂.nil)

-- ... and with indefinite length: 3A 80 (04 03 …) (04 02 …) 00 00
#guard hex (Node.cons (univ 26) .indefinite
    [.prim (univ 4) .short (ascii "Jon"), .prim (univ 4) .short (ascii "es")]).octets =
  [0x3A, 0x80, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73, 0x00, 0x00]

/-! ## REAL (8.5, 11.3) -/

-- 8.5.2, 8.5.9
example : RealContents .der .plusZero [] := rfl
example : RealContents .der .minusZero [octet 0x43] := rfl
-- 11.3.1: 0.5 = 1 × 2^-1, base 2, F = 0, N odd: 80 FF 01
example : RealContents .der (.num .two (1 / 2)) ([0x80, 0xFF, 0x01].map octet) := by
  refine ⟨false, 0, 0, -1, 1, 0, [octet 0xFF], [octet 0x01], by decide, by decide, by decide,
    by norm_num [realBase], rfl, by decide, by decide, ?_⟩
  simp [Profile.restricted, ExpFieldMin, tcOctetsFor]; decide
-- 11.3.2: 1.5 = 15 × 10^-1, as NR3 "15.E-1"
example : Nr3Canon (3 / 2) "15.E-1".toList :=
  ⟨false, 15, -1, by decide, by decide, by norm_num, by decide⟩
#guard nrValue 3 "15.E-1".toList = some (3 / 2)
#guard nrValue 2 " -0,5".toList = some (-1 / 2)
#guard nrValue 1 "+42".toList = some 42

/-! ## Time types (8.26, 11.9) -/

-- 11.9.1 b): the minutes of a whole-hour time difference are removed; a) full stop
#guard String.ofList (TimePrint.time (.point (.dateTime (.ymd 2020 1 5)
    { hour := 10, minute := some 5, frac := [⟨5, by decide⟩], zone := .diff 120 }))) =
  "2020-01-05T10:05.5+02"
-- 11.9.1 d): zero components removed, except the least significant present
#guard String.ofList (TimePrint.time (.interval (.d { years := some 0, months := some 1, days := some 0 }))) =
  "P1M0D"
-- 8.26.4.2: DATE-TIME drops "-", ":" and "T"
#guard String.ofList (TimeKind.dateTime.strip "2020-01-05T10:05:00".toList) = "20200105100500"
-- 11.7: GeneralizedTime in DER
example : GenTimeCanon "19920722132100.3Z".toList :=
  ⟨rfl, "19920722132100".toList, "3".toList, rfl, rfl, rfl, rfl, by decide⟩

-- 11.9: the canonical notation printed for a TIME value is a notation of that value (X.680 38.3.2),
-- so a CER/DER time encoding is a BER one, checked on values of every shape
def tDates : List DateV := [.c 19, .c 0, .c (-5), .c 123, .y 2020, .y 0, .y (-1), .y 12345, .y (-12345),
  .ym 2020 1, .ymd 2020 2 29, .ymd 1999 12 31, .yd 2021 365, .yw 2020 53, .ywd 2021 1 7, .ymd (-44) 3 15]
def tZones : List Zone := [.local_, .utc, .diff 120, .diff (-90), .diff 0, .diff 345]
def tFracs : List Digits := [[], [⟨5, by decide⟩], [⟨0, by decide⟩, ⟨5, by decide⟩, ⟨0, by decide⟩]]
def tTods : List TimeOfDayV := Id.run do
  let mut out := []
  for z in tZones do
    for f in tFracs do
      out := out ++ [{hour := 10, frac := f, zone := z}, {hour := 23, minute := some 5, frac := f, zone := z},
        {hour := 0, minute := some 0, second := some 59, frac := f, zone := z},
        {hour := 24, minute := some 0, second := some 0, zone := z}]
  return out
def tDurs : List DurationV := [{years := some 1}, {years := some 0, months := some 2, days := some 0},
  {weeks := some 3}, {hours := some 1, minutes := some 0, seconds := some 5, frac := [⟨2, by decide⟩]},
  {days := some 1, hours := some 2}, {seconds := some 0}, {years := some 5, frac := [⟨5, by decide⟩]}]
def tPoints : List PointV := tDates.map .date ++ tTods.map .time ++
  ((tDates.take 8).flatMap fun d => (tTods.take 12).map fun t => .dateTime d t)
def tVals : List TimeV := tPoints.map .point ++ tDurs.map (.interval ∘ .d) ++
  (tPoints.take 30).flatMap (fun p => tDurs.map fun d => .interval (.sd p d)) ++
  [.recurring (some 5) (.d {days := some 1}), .recurring none (.se (.time {hour := 10, zone := .diff 60}) (.time {hour := 12, zone := .diff 60})),
   .interval (.se (.dateTime (.ymd 2020 1 1) {hour := 10, zone := .diff 60}) (.dateTime (.ymd 2020 1 2) {hour := 10, zone := .diff 120}))]

def roundTrips (v : TimeV) : Bool :=
  !v.Wf || match Notation.parse (TimePrint.time v.norm) with
    | some w => w.Wf && w.norm == v.norm
    | none => false

#guard (tVals.filter TimeV.Wf).length = 308
#guard tVals.all roundTrips

/-! ## The decoder on the same examples (`Asn1/X690/Decode.lean`) -/

def m814t : Module := { m814 with types := m814.types ++ [("Seq", seqTy), ("Bits", .bitString []),
  ("Vis", .restricted .visible)] }
def okAs (p : Profile) (t : String) (os : List Nat) : Bool :=
  (decode [m814t] p 50 m814t (.ref t) (os.map octet)).toBool

-- 8.14 EXAMPLE: Type1 to Type5
#guard okAs .der "Type1" [0x1A, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
#guard okAs .der "Type2" [0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
#guard okAs .der "Type3" [0xA2, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
#guard okAs .der "Type4" [0x67, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
#guard okAs .der "Type5" [0x82, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
-- the wrong tag for Type3 (implicit where it is explicit)
#guard !okAs .ber "Type3" [0x82, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
-- 8.9.3 EXAMPLE
#guard okAs .der "Seq" [0x30, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF]
-- 8.2.2 and 11.1: TRUE as 01 in BER only
#guard okAs .ber "Seq" [0x30, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0x01]
#guard !okAs .der "Seq" [0x30, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0x01]
-- 8.6.4.2: the bit string, primitive (all profiles) and constructed (BER only)
#guard okAs .der "Bits" [0x03, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0]
#guard okAs .ber "Bits" [0x23, 0x80, 0x03, 0x03, 0x00, 0x0A, 0x3B, 0x03, 0x05, 0x04, 0x5F, 0x29, 0x1C, 0xD0, 0x00, 0x00]
#guard !okAs .der "Bits" [0x23, 0x80, 0x03, 0x03, 0x00, 0x0A, 0x3B, 0x03, 0x05, 0x04, 0x5F, 0x29, 0x1C, 0xD0, 0x00, 0x00]
-- 8.23.5 EXAMPLE: "Jones" constructed, definite and indefinite (BER only)
#guard okAs .ber "Vis" [0x3A, 0x09, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73]
#guard okAs .ber "Vis" [0x3A, 0x80, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73, 0x00, 0x00]
#guard !okAs .der "Vis" [0x3A, 0x09, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73]
-- 8.1.3.5 NOTE 2: more length octets than necessary, in BER only
#guard okAs .ber "Type1" [0x1A, 0x81, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
#guard !okAs .der "Type1" [0x1A, 0x81, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]
-- 8.1.3.2 a): no indefinite length on a primitive encoding
#guard !okAs .ber "Type1" [0x1A, 0x80, 0x4A, 0x6F, 0x6E, 0x65, 0x73, 0x00, 0x00]
