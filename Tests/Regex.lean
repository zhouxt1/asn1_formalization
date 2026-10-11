import Asn1.Parse.Values
import Asn1.X680.Checker

/-! ASN.1 regular expressions (X.680 Annex A) read from text, and PATTERN in a module. -/

open Asn1.Parse Asn1.X680

private def codes (s : String) : List Nat := s.toList.map Char.toNat

private def re (s : String) : Option Regex := (parseRegex (codes s)).toOption

private def lit (c : Char) : Regex := .cls false [(c.toNat, c.toNat)]
private def dig : Regex := .cls false digitChars

-- A.1.2, A.1.3: "fred" is four literals in sequence
#guard re "fred" == some (.cat (.cat (.cat (lit 'f') (lit 'r')) (lit 'e')) (lit 'd'))

-- A.2.10 examples: "\d#3-\d#4" and "\d#(3)-\d#(4)" are the same
#guard re "\\d#3-\\d#4" == some (.cat (.cat (.rep dig 3 (some 3)) (lit '-')) (.rep dig 4 (some 4)))
#guard re "\\d#3-\\d#4" == re "\\d#(3)-\\d#(4)"

-- A.2.10: "$\d#(1,)(\.\d#(1,2))?"
#guard re "$\\d#(1,)(\\.\\d#(1,2))?" ==
  some (.cat (.cat (lit '$') (.rep dig 1 none)) (.rep (.cat (lit '.') (.rep dig 1 (some 2))) 0 (some 1)))

-- the repetition forms
#guard re "a*" == some (.rep (lit 'a') 0 none)
#guard re "a+" == some (.rep (lit 'a') 1 none)
#guard re "a?" == some (.rep (lit 'a') 0 (some 1))
#guard re "a#(2,)" == some (.rep (lit 'a') 2 none)
#guard re "a#(,3)" == some (.rep (lit 'a') 0 (some 3))

-- A.2.9, A.2.11: repetition binds tighter than concatenation, which binds tighter than |
#guard re "ab*|c" == some (.alt (.cat (lit 'a') (.rep (lit 'b') 0 none)) (lit 'c'))

-- A.2.2: "[0-9]", "[^0]", and "[\d^.-]" (a digit, a caret, a period, a hyphen)
#guard re "[0-9]" == some (.cls false [(48, 57)])
#guard re "[^0]" == some (.cls true [(48, 48)])
#guard re "[\\d^.-]" == some (.cls false [(48, 57), (94, 94), (46, 46), (45, 45)])
-- a `]` first is a literal; so is `^` not first
#guard re "[]a]" == some (.cls false [(93, 93), (97, 97)])
#guard re "[a^]" == some (.cls false [(97, 97), (94, 94)])

-- A.2.5, A.2.6, A.2.7, A.2.8
#guard re "." == some (.cls true newlineChars)
#guard re "\\w" == some (.cls false wordChars)
#guard re "\\." == some (lit '.')
#guard re "\\a" == some (lit 'a')
#guard re "\\bfred\\b" == some (.cat (.cat (.cat (.cat (.cat .boundary (lit 'f')) (lit 'r')) (lit 'e')) (lit 'd')) .boundary)
-- A.2.3: a quadruple is one code point
#guard re "{0,0,3,163}" == some (.cls false [(931, 931)])
-- A.2.4: a collection the front end knows
#guard re "\\N{BasicLatin}" == some (.cls false [(0, 127)])

-- the illegal forms of A.2.10 NOTE and A.2.12
#guard re "*a" == none
#guard re "a**" == none
#guard re "a+?" == none
#guard re "a|" == none
#guard re "a#" == none
#guard re "()" == none
#guard re "(ab" == none
#guard re "ab)" == none
#guard re "[ab" == none
#guard re "[z-a]" == none
#guard re "\\N{NoSuchCollection}" == none

/-- 51.9: a PATTERN constraint is read, and the ranges of the character set still check. -/
def patternSrc : String := "
M DEFINITIONS ::= BEGIN
  Digits ::= IA5String (FROM (\"0\"..\"9\")) (PATTERN \"[0-9]#(1,8)\")
  Phone ::= NumericString (PATTERN \"\\d#3-\\d#4\")
END
"

#guard (match parseModules patternSrc with | .ok _ => true | .error _ => false)

/-- A bad expression is a parse error with its reason, not a silent skip. -/
def badPatternSrc : String := "
M DEFINITIONS ::= BEGIN
  Bad ::= IA5String (PATTERN \"*a\")
END
"

#guard (match parseModules badPatternSrc with | .ok _ => false | .error e => (e.splitOn "repetition operator").length > 1)
