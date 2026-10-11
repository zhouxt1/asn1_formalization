import Asn1.X680.Lexical
/-!
# Lexical items (X.680 12, X.681 7)

The front end reads ASN.1 text into the notation of `Asn1.X680.Syntax`. It is a tool, not part of
the specification: its functions are `partial`, and nothing is proved about them. What it produces
is checked by the specification itself (`Env.Valid`).

The lexer turns text into lexical items. Which reference an upper-case or lower-case name is
(type, module, class, object set; identifier, value, object) is decided by its context (12.4,
12.5; X.681 7.1–7.3), so a name is lexed only as one or the other.
-/

namespace Asn1.Parse

open Asn1.X680


/-- A lexical item and the line it starts on. -/
structure Lexeme where
  tok : Tok
  line : Nat
  deriving Repr, Inhabited

/-- X.680 12.38: the reserved words. -/
def reservedWords : List String :=
  ["ABSENT", "ABSTRACT-SYNTAX", "ALL", "APPLICATION", "AUTOMATIC", "BEGIN", "BIT", "BMPString",
   "BOOLEAN", "BY", "CHARACTER", "CHOICE", "CLASS", "COMPONENT", "COMPONENTS", "CONSTRAINED",
   "CONTAINING", "DATE", "DATE-TIME", "DEFAULT", "DEFINITIONS", "DURATION", "EMBEDDED", "ENCODED",
   "ENCODING-CONTROL", "END", "ENUMERATED", "EXCEPT", "EXPLICIT", "EXPORTS", "EXTENSIBILITY",
   "EXTERNAL", "FALSE", "FROM", "GeneralizedTime", "GeneralString", "GraphicString", "IA5String",
   "IDENTIFIER", "IMPLICIT", "IMPLIED", "IMPORTS", "INCLUDES", "INSTANCE", "INSTRUCTIONS",
   "INTEGER", "INTERSECTION", "ISO646String", "MAX", "MIN", "MINUS-INFINITY", "NOT-A-NUMBER",
   "NULL", "NumericString", "OBJECT", "ObjectDescriptor", "OCTET", "OF", "OID-IRI", "OPTIONAL",
   "PATTERN", "PDV", "PLUS-INFINITY", "PRESENT", "PrintableString", "PRIVATE", "REAL",
   "RELATIVE-OID", "RELATIVE-OID-IRI", "SEQUENCE", "SET", "SETTINGS", "SIZE", "STRING", "SYNTAX",
   "T61String", "TAGS", "TeletexString", "TIME", "TIME-OF-DAY", "TRUE", "TYPE-IDENTIFIER", "UNION",
   "UNIQUE", "UNIVERSAL", "UniversalString", "UTCTime", "UTF8String", "VideotexString",
   "VisibleString", "WITH"]

/-- X.680 12.1.6: white-space, with NO-BREAK SPACE. -/
def isSpace (c : Char) : Bool := c.toNat ∈ [9, 10, 11, 12, 13, 32, 160]

def isNewline (c : Char) : Bool := c.toNat ∈ [10, 11, 12, 13]

/-- Letters, digits and hyphens (12.2, 12.3). -/
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- 12.2.1, 12.3: a name runs over letters, digits and hyphens, but a hyphen may not be last nor
followed by another hyphen (which starts a comment). Returns the name and the rest. -/
partial def takeName (cs : List Char) (acc : List Char := []) : List Char × List Char :=
  match cs with
  | '-' :: '-' :: _ => (acc.reverse, cs)
  | '-' :: c :: rest => if isNameChar c then takeName (c :: rest) ('-' :: acc) else (acc.reverse, cs)
  | c :: rest => if isNameChar c && c != '-' then takeName rest (c :: acc) else (acc.reverse, cs)
  | [] => (acc.reverse, [])

/-- 12.6.3: a "--" comment ends at the next "--" or the end of the line. Returns the rest and the
newlines consumed. -/
partial def skipLineComment : List Char → List Char × Nat
  | '-' :: '-' :: rest => (rest, 0)
  | c :: rest => if isNewline c then (rest, if c == '\n' then 1 else 0) else skipLineComment rest
  | [] => ([], 0)

/-- 12.6.4: a "/*" comment ends at the matching "*/"; they nest. -/
partial def skipBlockComment (depth : Nat) (lines : Nat) : List Char → Except String (List Char × Nat)
  | '*' :: '/' :: rest => if depth = 1 then .ok (rest, lines) else skipBlockComment (depth - 1) lines rest
  | '/' :: '*' :: rest => skipBlockComment (depth + 1) lines rest
  | c :: rest => skipBlockComment depth (if c == '\n' then lines + 1 else lines) rest
  | [] => .error "unterminated /* comment"

/-- 12.14.1: a cstring's characters, `""` standing for one QUOTATION MARK. Spacing next to an end
of line inside it is not significant. Returns the characters, the rest, and the newlines. -/
partial def takeCString (acc : List Char) (lines : Nat) : List Char → Except String (List Char × List Char × Nat)
  | '"' :: '"' :: rest => takeCString ('"' :: acc) lines rest
  | '"' :: rest => .ok (acc.reverse, rest, lines)
  | c :: rest =>
    if isNewline c then
      let acc' := acc.dropWhile (fun d => d == ' ' || d == '\t')
      let lines' := if c == '\n' then lines + 1 else lines
      takeCString acc' lines' (rest.dropWhile (fun d => d == ' ' || d == '\t'))
    -- only graphic symbols and spacing characters: no control character but white-space (12.1.6)
    else if (c.toNat < 32 && !isSpace c) || c.toNat == 127 then
      .error s!"a control character ({c.toNat}) in a cstring (12.14.1)"
    else takeCString (c :: acc) lines rest
  | [] => .error "unterminated cstring"

/-- 12.10, 12.12: the characters of a bstring or hstring up to `'B` or `'H`, white-space ignored. -/
partial def takeQuoted (acc : List Char) (lines : Nat) : List Char → Except String (List Char × Char × List Char × Nat)
  | '\'' :: k :: rest => if k == 'B' || k == 'H' then .ok (acc.reverse, k, rest, lines)
                         else .error "a ' string ends with 'B or 'H"
  | c :: rest =>
    if isSpace c then takeQuoted acc (if c == '\n' then lines + 1 else lines) rest
    else takeQuoted (c :: acc) lines rest
  | [] => .error "unterminated ' string"

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (digitVal c)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The multi-character symbols, longest first (12.20–12.24), then the single characters (12.37). -/
def symbols : List String := ["::=", "...", "..", "[[", "]]"]

def singleSyms : List Char :=
  ['{', '}', '<', '>', ',', '.', '/', '(', ')', '[', ']', '-', ':', '=', ';', '@', '|', '!', '^', '*', '&']

/-- The lexical items of a text, with their lines. -/
partial def lex (cs : List Char) (line : Nat := 1) (acc : Array Lexeme := #[]) : Except String (Array Lexeme) :=
  let push (t : Tok) := acc.push ⟨t, line⟩
  match cs with
  | [] => .ok acc
  | '-' :: '-' :: rest =>
    let (rest', nl) := skipLineComment rest
    lex rest' (line + nl) acc
  | '/' :: '*' :: rest => do
    let (rest', nl) ← skipBlockComment 1 0 rest
    lex rest' (line + nl) acc
  | '"' :: rest => do
    let (s, rest', nl) ← takeCString [] 0 rest
    lex rest' (line + nl) (push (.cstring (s.map Char.toNat)))
  | '\'' :: rest => do
    let (s, k, rest', nl) ← takeQuoted [] 0 rest
    if k == 'B' then
      if s.all (fun c => c == '0' || c == '1') then lex rest' (line + nl) (push (.bstring (s.map (· == '1'))))
      else .error s!"line {line}: a bstring has only 0 and 1"
    else
      match s.mapM hexVal with
      | some hs => lex rest' (line + nl) (push (.hstring hs))
      | none => .error s!"line {line}: an hstring has only 0-9 and A-F"
  | '&' :: c :: rest =>
    if c.isAlpha then
      let (nm, rest') := takeName (c :: rest)
      lex rest' line (push (.field (String.ofList nm)))
    else .error s!"line {line}: & must start a field reference"
  | c :: rest =>
    if isSpace c then lex rest (if c == '\n' then line + 1 else line) acc
    else if c.isDigit then
      let ds := (c :: rest).takeWhile Char.isDigit
      let rest1 := (c :: rest).drop ds.length
      let n := ds.foldl (fun a d => 10 * a + digitVal d) 0
      -- 12.8, 12.9: no leading zero (in a realnumber, a zero before the point is alone)
      if c == '0' && ds.length > 1 then .error s!"line {line}: a number with a leading zero (12.8)" else
      -- 12.9: a decimal point followed by a digit (not ".."), and/or an exponent
      let (frac, rest2) : String × List Char := match rest1 with
        | '.' :: d :: r => if d.isDigit then
            let fs := (d :: r).takeWhile Char.isDigit
            (String.ofList fs, (d :: r).drop fs.length)
          else ("", rest1)
        | _ => ("", rest1)
      let (exp, rest3, isExp) : Int × List Char × Bool := match rest2 with
        | e :: r => if e == 'e' || e == 'E' then
            let (sgn, r') : Int × List Char := match r with
              | '-' :: r' => (-1, r')
              | '+' :: r' => (1, r')
              | _ => (1, r)
            let es := r'.takeWhile Char.isDigit
            if es = [] then (0, rest2, false)
            else (sgn * (es.foldl (fun a d => 10 * a + digitVal d) 0 : Nat), r'.drop es.length, true)
          else (0, rest2, false)
        | [] => (0, rest2, false)
      if frac = "" && !isExp then lex rest3 line (push (.number n))
      else lex rest3 line (push (.real n frac exp))
    else if c.isAlpha then
      let (nm, rest') := takeName (c :: rest)
      let s := String.ofList nm
      let t := if s ∈ reservedWords then Tok.kw s else if c.isUpper then .upper s else .lower s
      lex rest' line (push t)
    else
      match symbols.find? (fun s => s.toList.isPrefixOf (c :: rest)) with
      | some s => lex ((c :: rest).drop s.length) line (push (.sym s))
      | none =>
        if c ∈ singleSyms then lex rest line (push (.sym c.toString))
        else .error s!"line {line}: unexpected character {c} ({c.toNat})"

def lexString (s : String) : Except String (Array Lexeme) := lex s.toList

end Asn1.Parse
