/-!
# Lexical items (X.680 12, X.681 7)

The lexical items of ASN.1 notation. The front end (`Asn1.Parse`) produces them; the notation
keeps runs of them where reading them needs more than the grammar: an object in the syntax of its
class (X.681 10, 11.6), and an actual parameter before the kind of its dummy is known (X.683 9.5).
-/

namespace Asn1.X680

/-- A lexical item. -/
inductive Tok where
  /-- 12.2, 12.5, X.681 7.1, 7.3: a name whose first letter is upper case -/
  | upper (s : String)
  /-- 12.3, 12.4, X.681 7.2: a name whose first letter is lower case -/
  | lower (s : String)
  /-- 12.38: a reserved word -/
  | kw (s : String)
  /-- X.681 7.4–7.8: `&name`, a field reference (the name without `&`) -/
  | field (s : String)
  /-- 12.8 -/
  | number (n : Nat)
  /-- 12.9: a realnumber that is not a number: integer part, fraction digits, exponent -/
  | real (int : Nat) (frac : String) (exp : Int)
  /-- 12.10 -/
  | bstring (bs : List Bool)
  /-- 12.12: the semi-octets -/
  | hstring (hs : List Nat)
  /-- 12.14 (and 12.16, 12.17, which are lexically cstrings): the characters, as code points -/
  | cstring (cs : List Nat)
  /-- 12.20–12.24, 12.37 -/
  | sym (s : String)
  deriving DecidableEq, Repr, Inhabited

end Asn1.X680
