import Asn1.Bits
import Asn1.X680.Register

/-!
# Character collections (X.680 12.1.6, 41)

Characters are ISO/IEC 10646 code points (`Nat`). A collection is a list of closed ranges of code
points, kept as data so that it stays decidable and can be compared with a codec's tables.
-/

namespace Asn1.X680

/-- X.680 41, Table 8: the restricted character string types. T61String is TeletexString and
ISO646String is VisibleString (41.1), so neither has a constructor of its own. -/
inductive StrType where
  | bmp | general | graphic | ia5 | numeric | printable | teletex | universal | utf8 | videotex
  | visible
  deriving DecidableEq, Repr

/-- A set of characters: closed ranges of code points. -/
abbrev CharRanges := List (Nat × Nat)

def CharRanges.mem (rs : CharRanges) (c : Nat) : Bool := rs.any fun (lo, hi) => lo ≤ c && c ≤ hi

/-- X.680 12.1.6: the newline characters. -/
def newlineChars : CharRanges := [(10, 13)]

/-- X.680 12.1.6: the white-space characters. -/
def whiteSpaceChars : CharRanges := [(9, 13), (32, 32), (160, 160)]

/-- X.680 Annex A.2.6: `\d`, "[0-9]". -/
def digitChars : CharRanges := [(48, 57)]

/-- X.680 Annex A.2.6: `\w`, "[a-zA-Z0-9]". -/
def wordChars : CharRanges := [(48, 57), (65, 90), (97, 122)]

/-- The largest ISO/IEC 10646 code point.

OPEN (ledger X680-4): X.680 41.6 allows "any of the characters allowed by ISO/IEC 10646", and
41.12–41.13 address characters by a quadruple with a group below 128, which is a 31-bit space.
ISO/IEC 10646 has limited its code space to U+10FFFF since 2003. We take the current limit,
excluding the surrogate cells, which are not characters. -/
def maxCodePoint : Nat := 0x10FFFF

/-- The surrogate cells, D800 to DFFF, which address characters outside the BMP in UTF-16 and are not
characters themselves (X.680 41.15). -/
def surrogates : Nat × Nat := (0xD800, 0xDFFF)

/-- X.680 41.6: the characters of UniversalString (and of UTF8String, 41.16). -/
def universalChars : CharRanges := [(0, 0xD7FF), (0xE000, maxCodePoint)]

/-- X.680 41.15: the characters of BMPString. These are the first 64K−2 cells, less the cells used to
address characters outside the BMP. -/
def bmpChars : CharRanges := [(0, 0xD7FF), (0xE000, 0xFFFD)]

/-- X.680 41, Table 8: IA5String is register entries 1 (C0 controls) and 6 (ISO 646 IRV
graphics), plus SPACE and DELETE: all of 0 to 127. -/
def ia5Chars : CharRanges := [(0, 127)]

/-- X.680 41, Table 8: VisibleString is register entry 6 plus SPACE. -/
def visibleChars : CharRanges := [(32, 126)]

/-- X.680 41.2, Table 9: NumericString. -/
def numericChars : CharRanges := [(32, 32), (48, 57)]

/-- X.680 41.4, Table 10: PrintableString. -/
def printableChars : CharRanges :=
  [(32, 32), (39, 41), (43, 47), (48, 57), (58, 58), (61, 61), (63, 63), (65, 90), (97, 122)]

/-- The types defined by registration numbers whose characters are not ISO/IEC 10646 characters:
TeletexString, VideotexString, GraphicString and GeneralString (X.680 41, Table 8). IA5String and
VisibleString are also defined by registration numbers (1 and 6), but those are the ISO/IEC 646
characters, which are ISO/IEC 10646 characters with the same code points (43.7, 43.8). -/
def StrType.isRegister : StrType → Bool
  | .teletex | .videotex | .graphic | .general => true
  | _ => false

/-- The characters a restricted character string type allows, as ISO/IEC 10646 code points (X.680
41, Table 8). The types of `StrType.isRegister` have none: their characters are `RegChar`s. -/
def StrType.chars : StrType → CharRanges
  | .utf8 | .universal => universalChars
  | .bmp => bmpChars
  | .ia5 => ia5Chars
  | .visible => visibleChars
  | .numeric => numericChars
  | .printable => printableChars
  | .teletex | .videotex | .graphic | .general => []

/-! ## Characters from the International Register (X.680 39, 41; X.690 8.23.5, 11.4) -/

/-- An abstract character of a type that Table 8 defines by registration numbers. X.680 39: "the
information associated with a cell denotes a distinct abstract character", and X.690 11.4 NOTE 2:
"Each character in a character string value is associated with a particular entry in the
International Register". So a character is a cell of a registered set, and the same graphic symbol
in two sets is two characters. SPACE and DELETE (Table 8, "+ SPACE + DELETE") are the bit
combinations 2/0 and 7/15 outside every 94-character set (ISO/IEC 2022 6.3.3). -/
inductive RegChar where
  | space
  | delete
  /-- the cell at the bit combination(s) `code` of registration `no` (`SetKind.hasCell`) -/
  | cell (no : String) (code : List Nat)
  deriving DecidableEq, Repr

/-- X.680 Table 8, "TeletexString (T61String)". -/
def teletexEntries : List String :=
  ["6", "87", "102", "103", "106", "107", "126", "144", "150", "153", "156", "164", "165", "168"]

/-- X.680 Table 8, "VideotexString".

OPEN (ledger X680-19): registration 108 is NAPLPS, a coding system different from that of ISO/IEC
2022 (register 2.8.1), not a set of characters, so it contributes no cells. -/
def videotexEntries : List String :=
  ["1", "13", "72", "73", "87", "89", "102", "108", "126", "128", "129", "144", "150", "153", "164",
   "165", "168"]

/-- X.680 41, Table 8: the characters of a type defined by registration numbers.
- TeletexString and VideotexString: the cells of the listed registrations, SPACE and DELETE.
- GraphicString: "All G sets + SPACE".
- GeneralString: "All G and all C sets + SPACE + DELETE".

OPEN (ledger X680-1): "all G sets" is every graphic set the register holds; the register grows,
and this is its index as of registration 234. -/
def StrType.regAllows (k : StrType) : RegChar → Bool
  | .space => k.isRegister
  | .delete => k == .teletex || k == .videotex || k == .general
  | .cell no code =>
    match RegEntry.find? no with
    | some e => e.kind.hasCell code &&
      match k with
      | .teletex => no ∈ teletexEntries
      | .videotex => no ∈ videotexEntries
      | .graphic => e.kind.isG
      | .general => e.kind.isG || e.kind.isC
      | _ => false
    | none => false

/-- The ISO/IEC 10646 character a register character is, when it is one: the cells of registration
6 (the US version of ISO/IEC 646, 43.7) and of registration 1 (its C0 set, 43.8), SPACE and
DELETE. These are what a PATTERN (51.9, Annex A) can match: Annex A.2 writes its characters as
ISO/IEC 10646 characters. -/
def RegChar.ucs? : RegChar → Option Nat
  | .space => some 0x20
  | .delete => some 0x7F
  | .cell "6" [b] => some b
  | .cell "1" [b] => some b
  | .cell _ _ => none

/-- X.680 Table 11 (the "Permitted alphabet" and "Value range" columns) and 51.4.2: the types
whose character order is that of the code points (43.3), so that a range of characters is a range
of code points. -/
def StrType.knownOrder : StrType → Bool
  | .ia5 | .numeric | .printable | .visible | .bmp | .universal | .utf8 => true
  | _ => false

end Asn1.X680
