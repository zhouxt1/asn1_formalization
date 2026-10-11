import Asn1.X680.Semantics

/-! The character string types defined by the ISO International Register (X.680 41, Table 8). -/

open Asn1.X680

def kindFinal (no : String) : Option (SetKind × Nat) := (RegEntry.find? no).map fun e => (e.kind, e.final)

/-! ## The register agrees with X.690 Table 3

X.690 8.23.5.2 assumes these designations at the start of each string. -/

-- G0 = 6, ESC 2/8 4/2
#guard kindFinal "6" = some (.g94, cr 4 2)
-- C0 = 1, ESC 2/1 4/0
#guard kindFinal "1" = some (.c0, cr 4 0)
-- TeletexString and VideotexString: G0 = 102, ESC 2/8 7/5
#guard kindFinal "102" = some (.g94, cr 7 5)
-- TeletexString: C0 = 106, ESC 2/1 4/5; C1 = 107, ESC 2/2 4/8
#guard kindFinal "106" = some (.c0, cr 4 5)
#guard kindFinal "107" = some (.c1, cr 4 8)
-- VideotexString: C1 = 73, ESC 2/2 4/1
#guard kindFinal "73" = some (.c1, cr 4 1)

/-! ## The register is consistent -/

-- every registration number once
#guard (register.map (·.no)).Nodup
-- every registration Table 8 names is registered
#guard (teletexEntries ++ videotexEntries).all fun n => (RegEntry.find? n).isSome
-- one escape sequence per registration, except 173, which supersedes 72 with its Final byte
#guard ((register.filter (·.no != "72")).map fun e => (e.kind, e.final, e.irr)).Nodup
#guard kindFinal "72" = kindFinal "173"

/-! ## The characters of each type (Table 8) -/

def A6 : RegChar := .cell "6" [0x41]          -- LATIN CAPITAL LETTER A of ISO 646 (US)
def nbsp100 : RegChar := .cell "100" [0x20]    -- a 96-set's 2/0: NO-BREAK SPACE of Latin-1
def cr1 : RegChar := .cell "1" [0x0D]          -- CARRIAGE RETURN of the ISO 646 C0 set
def esc1 : RegChar := .cell "1" [0x1B]         -- ESCAPE, not a character
def kanji87 : RegChar := .cell "87" [0x30, 0x21] -- a two-byte character of JIS C 6226-1983

#guard StrType.teletex.regAllows A6 && StrType.teletex.regAllows kanji87
#guard StrType.teletex.regAllows .space && StrType.teletex.regAllows .delete
-- 100 is not a Teletex registration, nor is the C0 set 1 (Teletex has 106)
#guard !StrType.teletex.regAllows nbsp100 && !StrType.teletex.regAllows cr1
-- GraphicString: all G sets and SPACE, no DELETE, no C sets
#guard StrType.graphic.regAllows nbsp100 && StrType.graphic.regAllows kanji87
#guard !StrType.graphic.regAllows .delete && !StrType.graphic.regAllows cr1
-- GeneralString: G and C sets, SPACE, DELETE; ESCAPE is not a cell
#guard StrType.general.regAllows cr1 && StrType.general.regAllows .delete
#guard !StrType.general.regAllows esc1
-- a cell must exist: 94-sets have no 2/0, a two-byte set needs two bytes
#guard !StrType.general.regAllows (.cell "6" [0x20]) && !StrType.general.regAllows (.cell "87" [0x30])
-- VideotexString's 108 is a coding system, with no cells (ledger X680-19)
#guard !StrType.videotex.regAllows (.cell "108" [0x41])
-- registration 6 is not an ISO/IEC 10646 type's character: UTF8String has none of these
#guard !StrType.utf8.regAllows A6

/-! ## Constraints -/

-- 51.5: a two-byte character is one character
#guard (Val.regChars [kanji87, A6]).size? = some 2
-- 51.9, ledger X680-21: patterns see the ISO 646 characters
#guard (Val.regChars [A6, .space, cr1]).patternChars = some [0x41, 0x20, 0x0D]
#guard (Val.regChars [A6, nbsp100]).patternChars = none

/-! ## Through the semantics -/

def M : Module := { name := "M", header := ⟨.explicit, false⟩ }
def H0 : ContentsHook := fun _ _ _ _ _ => True

example (k : Nat) : (sem [M] H0 (k + 1) (.ofModule M) [] (.restricted .general)).all
    (.regChars [A6, cr1, kanji87]) := by
  simp only [sem, restrictedVSet]
  exact ⟨_, rfl, by decide⟩

/-- ObjectDescriptor is GraphicString (48.3), so a control character is not in it. -/
example (k : Nat) : ¬ (sem [M] H0 (k + 1) (.ofModule M) [] .objectDescriptor).all (.regChars [cr1]) := by
  simp only [sem, restrictedVSet]
  rintro ⟨cs, h, hc⟩
  cases h
  exact absurd (hc _ List.mem_cons_self) (by decide)
