import Asn1.X680.Chars

/-!
# ASN.1 regular expressions (X.680 51.9, Annex A)

`Regex` is the abstract syntax of an Annex A regular expression, once the string in the PATTERN
constraint has been parsed:
- every single-character notation (a literal, `.`, `\d`, `\w`, `\s`, `\n`, `\t`, `\r`, a
  bracketed list, `{g,p,r,c}`, `\N{…}`) becomes a character class of code-point ranges;
- repetition operators become bounds.

What the expression matches is a relation over positions in the string.
-/

namespace Asn1.X680

/-- X.680 Annex A, after parsing. -/
inductive Regex where
  /-- A.1.2, A.2.2–A.2.7: one character from a class: in `ranges`, or, if `negated`, not in them
  (A.2.2 "^"). The period of A.2.5 is the newline characters, negated. -/
  | cls (negated : Bool) (ranges : CharRanges)
  /-- A.2.7 `\b`: the empty string at the beginning or the end of a word -/
  | boundary
  /-- A.1.3 -/
  | cat (a b : Regex)
  /-- A.2.9 -/
  | alt (a b : Regex)
  /-- A.2.10: at least `lo` and at most `hi` (no limit if `none`) times. `*` is `0, none`, `+` is
  `1, none`, `?` is `0, some 1`, and `#n`, `#(n)`, `#(n,)`, `#(n,m)` and `#(,m)` follow. -/
  | rep (a : Regex) (lo : Nat) (hi : Option Nat)
  deriving DecidableEq, Repr

def Regex.clsMem (negated : Bool) (rs : CharRanges) (c : Nat) : Bool := rs.mem c != negated

/-- A position is inside a word if the character there is a `\w` character (A.2.6).

OPEN (ledger X680-5): A.2.7 does not define "word". We take it to mean a maximal run of `\w`
characters, as in the scripting languages A.1.1 points to. -/
def isWordAt (w : List Nat) (i : Nat) : Bool :=
  match w[i]? with
  | some c => wordChars.mem c
  | none => false

mutual
  /-- `Matches re w i j`: `re` matches the characters of `w` from position `i` up to (not
  including) `j`. -/
  inductive Matches : Regex → List Nat → Nat → Nat → Prop where
    | cls {neg rs w i c} : w[i]? = some c → Regex.clsMem neg rs c → Matches (.cls neg rs) w i (i + 1)
    /-- A.2.7: a boundary is between a word character and a non-word character (or an end). -/
    | boundary {w i} : (i = 0 ∨ isWordAt w (i - 1) = false) ≠ (isWordAt w i = false) →
        Matches .boundary w i i
    | cat {a b w i k j} : Matches a w i k → Matches b w k j → Matches (.cat a b) w i j
    | altL {a b w i j} : Matches a w i j → Matches (.alt a b) w i j
    | altR {a b w i j} : Matches b w i j → Matches (.alt a b) w i j
    | rep {a lo hi w i j n} : lo ≤ n → (∀ m, hi = some m → n ≤ m) → Times a n w i j →
        Matches (.rep a lo hi) w i j

  /-- `a`, matched `n` times in succession. -/
  inductive Times : Regex → Nat → List Nat → Nat → Nat → Prop where
    | zero {a w i} : Times a 0 w i i
    | succ {a n w i k j} : Matches a w i k → Times a n w k j → Times a (n + 1) w i j
end

/-- X.680 51.9.2: a PATTERN selects the values whose entire string matches the entire expression. -/
def Regex.Accepts (re : Regex) (cs : List Nat) : Prop := Matches re cs 0 cs.length

end Asn1.X680
