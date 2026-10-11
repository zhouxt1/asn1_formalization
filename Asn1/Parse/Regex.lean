import Asn1.X680.Pattern

/-!
# Reading an ASN.1 regular expression (X.680 Annex A)

`parseRegex` turns the characters of the cstring after `PATTERN` (51.9.1) into the abstract `Regex` of
`Asn1.X680.Pattern`. The string is the one the lexer returns, in which a pair of QUOTATION MARKs is already
one (A.2.8) and the spacing around a newline is already gone (A.2.1 NOTE 4).

Read as written in Annex A:
- a literal character matches itself (A.1.2); `\` before a character quotes it (A.2.8);
- `[ ]` lists and ranges, `^` first, `]` first, `-` first or last (A.2.2); `\d \w \s \t \n \r` and
  `{g,p,r,c}` between the brackets keep their meaning;
- `.` is any character but a newline (A.2.5); `\d \w \t \r \n \s \b` (A.2.6, A.2.7);
- `{g,p,r,c}` is one ISO/IEC 10646 character (A.2.3);
- `|`, `( )`, `* + ?`, `#n #(n) #(n,) #(n,m) #(,m)` (A.2.9–A.2.11);
- the illegal forms of A.2.10 NOTE and A.2.12: a repetition operator first or right after another one,
  `#` or `|` last, `()`.

OPEN (ledger X680-29): `\N{name}` (A.2.4) needs the characters of a named collection or of a value or type
reference of the module. Here only the restricted string types of clause 41 and `BasicLatin` are known; any
other name is an error, not a guess.
-/

namespace Asn1.Parse
open Asn1.X680

/-- The characters of a collection `\N{name}` names, where this front end knows it (A.2.4, 41). -/
def charSetByName : String → Option CharRanges
  | "BasicLatin" => some [(0, 127)]
  | "IA5String" => some ia5Chars
  | "VisibleString" | "ISO646String" => some visibleChars
  | "NumericString" => some numericChars
  | "PrintableString" => some printableChars
  | "BMPString" => some bmpChars
  | "UniversalString" | "UTF8String" => some universalChars
  | _ => none

private def ch (c : Char) : Nat := c.toNat

private def isDigit (n : Nat) : Bool := 48 ≤ n && n ≤ 57

/-- A decimal number at `i`: the value and the index after it. -/
private partial def number (s : Array Nat) (i : Nat) : Option (Nat × Nat) :=
  if i < s.size && isDigit s[i]! then
    let rec go (j acc : Nat) : Nat × Nat :=
      if j < s.size && isDigit s[j]! then go (j + 1) (acc * 10 + (s[j]! - 48)) else (acc, j)
    some (go i 0)
  else none

/-- `{group,plane,row,cell}` at `i` (which is `{`): the code point and the index after `}`. -/
private def quadruple (s : Array Nat) (i : Nat) : Except String (Nat × Nat) := do
  let some (g, i) := number s (i + 1) | throw "a quadruple {g,p,r,c} needs four numbers"
  unless s[i]? == some (ch ',') do throw "a quadruple {g,p,r,c} needs four numbers"
  let some (p, i) := number s (i + 1) | throw "a quadruple {g,p,r,c} needs four numbers"
  unless s[i]? == some (ch ',') do throw "a quadruple {g,p,r,c} needs four numbers"
  let some (r, i) := number s (i + 1) | throw "a quadruple {g,p,r,c} needs four numbers"
  unless s[i]? == some (ch ',') do throw "a quadruple {g,p,r,c} needs four numbers"
  let some (c, i) := number s (i + 1) | throw "a quadruple {g,p,r,c} needs four numbers"
  unless s[i]? == some (ch '}') do throw "a quadruple {g,p,r,c} needs four numbers"
  return (((g * 256 + p) * 256 + r) * 256 + c, i + 1)

/-- `\N{name}` at `i` (which is the `N`): the characters and the index after `}`. -/
private def namedChars (s : Array Nat) (i : Nat) : Except String (CharRanges × Nat) := do
  unless s[i + 1]? == some (ch '{') do throw "\\N must be followed by {name}"
  let rec close (j : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | f + 1 => if s[j]? == some (ch '}') then some j else if j < s.size then close (j + 1) f else none
  let some e := close (i + 2) s.size | throw "\\N{ has no closing }"
  let chars : List Char := ((s.toList.drop (i + 2)).take (e - (i + 2))).map Char.ofNat
  let name := String.ofList chars
  match charSetByName name with
  | some rs => return (rs, e + 1)
  | none => throw s!"\\N\{{name}} is not a collection this front end knows (A.2.4)"

/-- The single-character classes behind `\x` (A.2.6, A.2.7), or `none` if `c` after the backslash is not one. -/
private def escapeClass (c : Nat) : Option CharRanges :=
  if c == ch 'd' then some digitChars
  else if c == ch 'w' then some wordChars
  else if c == ch 's' then some whiteSpaceChars
  else if c == ch 't' then some [(9, 9)]
  else if c == ch 'n' then some newlineChars
  else if c == ch 'r' then some [(13, 13)]
  else none

/-- One item of a bracketed list: a set or a single character (the only kind a range can start from). -/
private inductive Item where
  | set (rs : CharRanges)
  | one (c : Nat)

/-- The item at `i` inside `[ ]`, and the index after it. -/
private def listItem (s : Array Nat) (i : Nat) : Except String (Item × Nat) := do
  let some c := s[i]? | throw "unterminated [ ]"
  if c == ch '\\' then
    let some d := s[i + 1]? | throw "a backslash at the end of the expression"
    if d == ch 'N' then
      let (rs, j) ← namedChars s (i + 1)
      return (.set rs, j)
    else if d == ch 'b' then throw "\\b cannot be used between square brackets"
    else match escapeClass d with
      | some rs => return (if d == ch 't' || d == ch 'r' then .one rs.head!.1 else .set rs, i + 2)
      | none => return (.one d, i + 2)
  else if c == ch '{' then
    let (q, j) ← quadruple s i
    return (.one q, j)
  else return (.one c, i + 1)

/-- A bracketed list at `i` (which is `[`) (A.2.2): negation, the ranges, the index after `]`. -/
private partial def bracketList (s : Array Nat) (i : Nat) : Except String (Bool × CharRanges × Nat) := do
  let neg := s[i + 1]? == some (ch '^')
  let start := if neg then i + 2 else i + 1
  -- a `]` first is a literal
  let mut rs : CharRanges := []
  let mut j := start
  if s[j]? == some (ch ']') then
    rs := rs ++ [(93, 93)]
    j := j + 1
  let mut fuel := s.size + 1
  repeat
    if fuel == 0 then throw "unterminated [ ]"
    fuel := fuel - 1
    match s[j]? with
    | none => throw "unterminated [ ]"
    | some c =>
      if c == ch ']' then return (neg, rs, j + 1)
      let (it, j') ← listItem s j
      match it with
      | .set r => rs := rs ++ r; j := j'
      | .one lo =>
        -- a range `lo-hi`, unless the hyphen is last
        if s[j']? == some (ch '-') && s[j' + 1]? != some (ch ']') && s[j' + 1]?.isSome then
          let (hit, j'') ← listItem s (j' + 1)
          match hit with
          | .one hi =>
            if hi < lo then throw "a range in [ ] runs backwards"
            rs := rs ++ [(lo, hi)]; j := j''
          | .set _ => throw "a range in [ ] must end in one character"
        else rs := rs ++ [(lo, lo)]; j := j'
  throw "unterminated [ ]"

/-- The bounds of the repetition operator at `i`, if there is one: `* + ? #n #(n) #(n,) #(n,m) #(,m)`. -/
private def repetition (s : Array Nat) (i : Nat) : Except String (Option (Nat × Option Nat × Nat)) := do
  match s[i]? with
  | some c =>
    if c == ch '*' then return some (0, none, i + 1)
    else if c == ch '+' then return some (1, none, i + 1)
    else if c == ch '?' then return some (0, some 1, i + 1)
    else if c == ch '#' then
      if s[i + 1]? == some (ch '(') then
        let lo? := number s (i + 2)
        let j := match lo? with | some (_, j) => j | none => i + 2
        let lo := match lo? with | some (n, _) => n | none => 0
        if s[j]? == some (ch ')') then
          match lo? with
          | some _ => return some (lo, some lo, j + 1)
          | none => throw "#( ) needs a number"
        else if s[j]? == some (ch ',') then
          match number s (j + 1) with
          | some (hi, k) =>
            unless s[k]? == some (ch ')') do throw "#(n,m) is not closed"
            if hi < lo then throw "#(n,m) with m below n" else return some (lo, some hi, k + 1)
          | none =>
            unless s[j + 1]? == some (ch ')') do throw "#(n,m) is not closed"
            match lo? with
            | some _ => return some (lo, none, j + 2)
            | none => throw "#(,) needs a number"
        else throw "#( is not closed"
      else
        -- `#n` takes a single digit (A.2.1)
        match s[i + 1]? with
        | some d => if isDigit d then return some (d - 48, some (d - 48), i + 2) else throw "# needs a number"
        | none => throw "# needs a number"
    else return none
  | none => return none

mutual
  /-- Alternatives up to a `)` or the end: the expression and the index where it stopped. `none` for no
  characters at all. -/
  private partial def alternation (s : Array Nat) (i : Nat) (depth : Nat) : Except String (Option Regex × Nat) := do
    let (first, i) ← sequence s i depth
    if s[i]? == some (ch '|') then
      let some a := first | throw "| needs an expression before it"
      let (rest, j) ← alternation s (i + 1) depth
      let some b := rest | throw "| cannot be the last character of an expression"
      return (some (.alt a b), j)
    else return (first, i)

  /-- A concatenation up to `|`, `)` or the end. -/
  private partial def sequence (s : Array Nat) (i : Nat) (depth : Nat) : Except String (Option Regex × Nat) := do
    let mut acc : Option Regex := none
    let mut j := i
    let mut fuel := s.size + 1
    repeat
      if fuel == 0 then break
      fuel := fuel - 1
      match s[j]? with
      | none => break
      | some c =>
        if c == ch '|' then break
        if c == ch ')' then
          if depth == 0 then throw "unmatched )"
          break
        let (a, k) ← atom s j depth
        let (a, k) ← repeated s a k
        acc := some (match acc with | none => a | some b => .cat b a)
        j := k
    return (acc, j)

  /-- A repetition operator after `a`, at most one (A.2.10 NOTE). -/
  private partial def repeated (s : Array Nat) (a : Regex) (i : Nat) : Except String (Regex × Nat) := do
    match ← repetition s i with
    | none => return (a, i)
    | some (lo, hi, j) =>
      match ← repetition s j with
      | some _ => throw "a repetition operator cannot follow another (A.2.10)"
      | none =>
        if s[j]? == some (ch '#') then throw "# cannot be the last character of an expression"
        return (.rep a lo hi, j)

  /-- One atom: a character, a class, a group. -/
  private partial def atom (s : Array Nat) (i : Nat) (depth : Nat) : Except String (Regex × Nat) := do
    let some c := s[i]? | throw "an atom was expected"
    if c == ch '*' || c == ch '+' || c == ch '?' || c == ch '#' then
      throw "a repetition operator cannot be the first character of an expression (A.2.10)"
    else if c == ch '(' then
      let (inner, j) ← alternation s (i + 1) (depth + 1)
      unless s[j]? == some (ch ')') do throw "unmatched ("
      let some r := inner | throw "the empty subexpression () is not permitted (A.2.12)"
      return (r, j + 1)
    else if c == ch '[' then
      let (neg, rs, j) ← bracketList s i
      return (.cls neg rs, j)
    else if c == ch '{' then
      let (q, j) ← quadruple s i
      return (.cls false [(q, q)], j)
    else if c == ch '.' then return (.cls true newlineChars, i + 1)
    else if c == ch '\\' then
      let some d := s[i + 1]? | throw "a backslash at the end of the expression"
      if d == ch 'N' then
        let (rs, j) ← namedChars s (i + 1)
        return (.cls false rs, j)
      else if d == ch 'b' then return (.boundary, i + 2)
      else match escapeClass d with
        | some rs => return (.cls false rs, i + 2)
        | none => return (.cls false [(d, d)], i + 2)
    else return (.cls false [(c, c)], i + 1)
end

/-- A.1–A.2: the regular expression written in `cs`. The empty string is the expression matching only the
empty string. -/
def parseRegex (cs : List Nat) : Except String Regex := do
  let s := cs.toArray
  let (r, i) ← alternation s 0 0
  if i < s.size then throw "unmatched )"
  match r with
  | some r => return r
  | none => return .rep (.cls false []) 0 (some 0)

end Asn1.Parse
