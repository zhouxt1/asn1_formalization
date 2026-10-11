/-!
# The ISO International Register of Coded Character Sets to be used with Escape Sequences

X.680 41, Table 8 defines TeletexString, VideotexString, GraphicString and GeneralString (and,
nominally, IA5String and VisibleString) by registration numbers in this register (ISO/IEC 2375),
and X.690 8.23.5 encodes their values with its escape sequences (ISO/IEC 2022).

This is the register's index (sections 2.1–2.8), as published by ITSCJ, the registration
authority, with its last registration, 234 (2004). Each entry is a registration number, the kind of
set registered (which fixes the form of its escape sequences, ISO/IEC 2022 13.2.2), and the Final
byte of its escape sequence. The register's character tables (the contents of each set) are not
transcribed here: X.680 needs only which cells a set has, which its kind determines.
-/

namespace Asn1.X680

/-- The kinds of registration, by the section of the register's index they are in. -/
inductive SetKind where
  /-- 2.1: a 94-character graphic set, designated by ESC 2/8–2/11 F -/
  | g94
  /-- 2.2: a 94-character graphic set with a second Intermediate byte, ESC 2/8–2/11 2/1 F -/
  | g94x
  /-- 2.3: a 96-character graphic set, designated by ESC 2/13–2/15 F (not as G0) -/
  | g96
  /-- 2.4: a multiple-byte graphic set, ESC 2/4 2/8–2/11 F. Every set in this section is a
  94 × 94 set of two-byte characters (ledger X680-20). -/
  | multi
  /-- 2.5: a C0 control set, ESC 2/1 F -/
  | c0
  /-- 2.6: a C1 control set, ESC 2/2 F -/
  | c1
  /-- 2.7: a single control function, ESC F -/
  | single
  /-- 2.8: a coding system different from that of ISO/IEC 2022, ESC 2/5 F (with standard return)
  or ESC 2/5 2/15 F (without) -/
  | docs (standardReturn : Bool)
  deriving DecidableEq, Repr

/-- A registration: its number (some numbers have parts, "8-1"), its kind, and the Final byte of its
escape sequence, as column/row (`4/2` is `0x42`). A registration that updates another with the
same Final byte is announced by "identify revised registration", ESC 2/6 F' (ISO/IEC 2022 13.3);
`irr` is that F'. -/
structure RegEntry where
  no : String
  kind : SetKind
  final : Nat
  irr : Option Nat := none
  deriving DecidableEq, Repr

/-- column/row notation -/
def cr (c r : Nat) : Nat := 16 * c + r

def regEntry (k : SetKind) (no : String) (c r : Nat) : RegEntry := ⟨no, k, cr c r, none⟩

/-- 2.1: 94-character graphic sets with one Intermediate byte. -/
def regG94 : List RegEntry := [
  ("2", 4, 0), ("4", 4, 1), ("6", 4, 2), ("8-1", 4, 3), ("8-2", 4, 4), ("9-1", 4, 5), ("9-2", 4, 6),
  ("10", 4, 7), ("11", 4, 8), ("13", 4, 9), ("14", 4, 10), ("15", 5, 9), ("16", 4, 12),
  ("17", 5, 10), ("18", 5, 11), ("19", 5, 12), ("21", 4, 11), ("25", 5, 2), ("27", 5, 5),
  ("31", 5, 8), ("37", 4, 14), ("38", 4, 15), ("39", 4, 13), ("47", 5, 6), ("49", 5, 7),
  ("50", 5, 13), ("51", 5, 14), ("53", 5, 0), ("54", 5, 1), ("55", 5, 3), ("57", 5, 4),
  ("59", 5, 15), ("60", 6, 0), ("61", 6, 1), ("68", 6, 5), ("69", 6, 6), ("70", 6, 2), ("71", 6, 3),
  ("72", 6, 4), ("84", 6, 7), ("85", 6, 8), ("86", 6, 9), ("88", 6, 10), ("89", 6, 11),
  ("90", 6, 12), ("91", 6, 13), ("92", 6, 14), ("93", 6, 15), ("94", 7, 0), ("95", 7, 1),
  ("96", 7, 2), ("98", 7, 3), ("99", 7, 4), ("102", 7, 5), ("103", 7, 6), ("121", 7, 7),
  ("122", 7, 8), ("128", 7, 12), ("137", 7, 9), ("141", 7, 10), ("146", 7, 11), ("147", 7, 13),
  ("173", 6, 4)].map fun (n, c, r) => regEntry .g94 n c r

/-- 2.2: 94-character graphic sets with second Intermediate byte 2/1. -/
def regG94x : List RegEntry := [
  ("150", 4, 0), ("151", 4, 1), ("170", 4, 2), ("207", 4, 3), ("230", 4, 4), ("231", 4, 5),
  ("232", 4, 6)].map fun (n, c, r) => regEntry .g94x n c r

/-- 2.3: 96-character graphic sets. -/
def regG96 : List RegEntry := [
  ("100", 4, 1), ("101", 4, 2), ("109", 4, 3), ("110", 4, 4), ("111", 4, 0), ("123", 4, 5),
  ("126", 4, 6), ("127", 4, 7), ("129", 7, 13), ("138", 4, 8), ("139", 4, 9), ("142", 4, 10),
  ("143", 4, 11), ("144", 4, 12), ("148", 4, 13), ("152", 4, 14), ("153", 4, 15), ("154", 5, 0),
  ("155", 5, 1), ("156", 5, 2), ("157", 5, 6), ("158", 5, 8), ("164", 5, 3), ("166", 5, 4),
  ("167", 5, 5), ("179", 5, 9), ("180", 5, 10), ("181", 5, 11), ("182", 5, 12), ("197", 5, 13),
  ("198", 5, 14), ("199", 5, 15), ("200", 6, 0), ("201", 6, 1), ("203", 6, 2), ("204", 6, 3),
  ("205", 6, 4), ("206", 6, 5), ("226", 6, 6), ("208", 6, 7), ("209", 6, 8), ("227", 6, 9),
  ("234", 6, 10)].map fun (n, c, r) => regEntry .g96 n c r

/-- 2.4: multiple-byte graphic sets. 168 updates 87 and has its Final byte (the index's "Update
Registration 87"). -/
def regMulti : List RegEntry :=
  ([("42", 4, 0), ("58", 4, 1), ("87", 4, 2), ("149", 4, 3), ("159", 4, 4), ("165", 4, 5),
    ("169", 4, 6), ("171", 4, 7), ("172", 4, 8), ("183", 4, 9), ("184", 4, 10), ("185", 4, 11),
    ("186", 4, 12), ("187", 4, 13), ("202", 4, 14), ("228", 4, 15), ("229", 5, 0),
    ("233", 5, 1)].map fun (n, c, r) => regEntry .multi n c r) ++
  [{ no := "168", kind := .multi, final := cr 4 2, irr := some (cr 4 0) }]

/-- 2.5: C0 control sets. -/
def regC0 : List RegEntry := [
  ("1", 4, 0), ("7", 4, 1), ("26", 4, 3), ("36", 4, 4), ("48", 4, 2), ("74", 4, 6), ("104", 4, 7),
  ("106", 4, 5), ("130", 4, 8), ("132", 4, 9), ("134", 4, 10), ("135", 4, 11),
  ("140", 4, 12)].map fun (n, c, r) => regEntry .c0 n c r

/-- 2.6: C1 control sets. The index gives 124, the "upward compatible version of ISO 6630
(Registration 67)", the Final bytes "4/0 4/2": 67's 4/2, announced as a revision. -/
def regC1 : List RegEntry :=
  ([("40", 4, 5), ("56", 4, 0), ("67", 4, 2), ("73", 4, 1), ("77", 4, 3), ("105", 4, 7),
    ("107", 4, 8), ("133", 4, 4), ("136", 4, 6)].map fun (n, c, r) => regEntry .c1 n c r) ++
  [{ no := "124", kind := .c1, final := cr 4 2, irr := some (cr 4 0) }]

/-- 2.7: single control functions. -/
def regSingle : List RegEntry := [
  ("32", 6, 0), ("33", 6, 1), ("34", 6, 2), ("35", 6, 3), ("62", 6, 14), ("63", 6, 15),
  ("64", 7, 12), ("65", 7, 13), ("66", 7, 14), ("189", 6, 4)].map fun (n, c, r) =>
    regEntry .single n c r

/-- 2.8: coding systems different from that of ISO/IEC 2022. -/
def regDocs : List RegEntry :=
  ([("108", 4, 1), ("131", 4, 3), ("145", 4, 4), ("160", 4, 5), ("161", 4, 6), ("178", 4, 2),
    ("188", 4, 8), ("196", 4, 7)].map fun (n, c, r) => regEntry (.docs true) n c r) ++
  ([("125", 4, 2), ("162", 4, 0), ("163", 4, 1), ("174", 4, 3), ("175", 4, 4), ("176", 4, 5),
    ("177", 4, 6), ("190", 4, 7), ("191", 4, 8), ("192", 4, 9), ("193", 4, 10), ("194", 4, 11),
    ("195", 4, 12)].map fun (n, c, r) => regEntry (.docs false) n c r)

/-- The register. -/
def register : List RegEntry := regG94 ++ regG94x ++ regG96 ++ regMulti ++ regC0 ++ regC1 ++
  regSingle ++ regDocs

def RegEntry.find? (no : String) : Option RegEntry := register.find? (·.no == no)

/-- A graphic (G) set. -/
def SetKind.isG : SetKind → Bool
  | .g94 | .g94x | .g96 | .multi => true
  | _ => false

/-- A control (C) set. -/
def SetKind.isC : SetKind → Bool
  | .c0 | .c1 => true
  | _ => false

/-- The cells of a set, by their bit combinations (ISO/IEC 2022 6.3, 8.2): a 94-set has 2/1 to
7/14, a 96-set 2/0 to 7/15, a two-byte 94 × 94 set a pair of 2/1 to 7/14, a C0 set 0/0 to 1/15 and
a C1 set 8/0 to 9/15. ESCAPE, 1/11, is the escape character in every C0 set (ISO/IEC 2022 6.2,
8.3) and is not a cell of one. Single control functions and other coding systems have no cells. -/
def SetKind.hasCell : SetKind → List Nat → Bool
  | .g94, [b] | .g94x, [b] => 0x21 ≤ b && b ≤ 0x7E
  | .g96, [b] => 0x20 ≤ b && b ≤ 0x7F
  | .multi, [b1, b2] => 0x21 ≤ b1 && b1 ≤ 0x7E && 0x21 ≤ b2 && b2 ≤ 0x7E
  | .c0, [b] => b ≤ 0x1F && b != 0x1B
  | .c1, [b] => 0x80 ≤ b && b ≤ 0x9F
  | _, _ => false

end Asn1.X680
