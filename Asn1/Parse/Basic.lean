import Asn1.Parse.Lexer

/-!
# The parser's state and combinators

A parser reads an array of lexical items from a position, with backtracking.
-/

namespace Asn1.Parse

open Asn1.X680

abbrev P := ReaderT (Array Lexeme) (StateT Nat (Except String))

def P.run {α : Type} (p : P α) (ls : Array Lexeme) : Except String (α × Nat) :=
  (p ls).run 0

def peekAt (k : Nat) : P (Option Tok) := do
  let ls ← read
  let i ← get
  return (ls[i + k]?).map (·.tok)

def peek : P (Option Tok) := peekAt 0

/-- X.680 13.1: the default encoding reference of the module being read is TAG unless its header
has an "EncodingReferenceDefault" (`XER INSTRUCTIONS`): found after the nearest `DEFINITIONS`
before the current position. -/
def defaultEncIsTag : P Bool := do
  let ls ← read
  let i ← get
  let tok (k : Nat) : Option Tok := ls[k]?.map (·.tok)
  let rec back : Nat → Bool
    | 0 => true
    | j + 1 => match tok j with
      | some (.kw "DEFINITIONS") => match tok (j + 1), tok (j + 2) with
        | some (.upper u), some (.kw "INSTRUCTIONS") => u == "TAG"
        | _, _ => true
      | _ => back j
  return back i

def curLine : P Nat := do
  let ls ← read
  let i ← get
  return (ls[i]?.map (·.line)).getD ((ls.back?.map (·.line)).getD 0)

def fail {α : Type} (msg : String) : P α := do
  let l ← curLine
  let t ← peek
  throw s!"line {l}: {msg} (at {repr t})"

def next : P Tok := do
  match ← peek with
  | some t => modify (· + 1); return t
  | none => fail "unexpected end of input"

def isSym (s : String) : P Bool := return (← peek) == some (.sym s)
def isKw (s : String) : P Bool := return (← peek) == some (.kw s)
def isSymAt (k : Nat) (s : String) : P Bool := return (← peekAt k) == some (.sym s)
def isKwAt (k : Nat) (s : String) : P Bool := return (← peekAt k) == some (.kw s)

def sym (s : String) : P Unit := do
  if ← isSym s then modify (· + 1) else fail s!"expected {s}"

def kw (s : String) : P Unit := do
  if ← isKw s then modify (· + 1) else fail s!"expected {s}"

/-- Consume the symbol if it is next. -/
def optSym (s : String) : P Bool := do
  if ← isSym s then modify (· + 1); return true else return false

def optKw (s : String) : P Bool := do
  if ← isKw s then modify (· + 1); return true else return false

def upper : P String := do
  match ← peek with
  | some (.upper s) => modify (· + 1); return s
  | _ => fail "expected a reference starting with an upper-case letter"

def lower : P String := do
  match ← peek with
  | some (.lower s) => modify (· + 1); return s
  | _ => fail "expected an identifier"

def number : P Nat := do
  match ← peek with
  | some (.number n) => modify (· + 1); return n
  | _ => fail "expected a number"

/-- Try a parser; on failure, restore the position and return `none`. -/
def attempt {α : Type} (p : P α) : P (Option α) := do
  let i ← get
  try
    let a ← p
    return some a
  catch _ =>
    set i
    return none

/-- The lexical items of a balanced group starting at an open bracket `o` closed by `c`, without the
brackets. -/
partial def balanced (o c : String) : P (List Tok) := do
  sym o
  let rec go (depth : Nat) (acc : Array Tok) : P (List Tok) := do
    let t ← next
    if t == .sym c then
      if depth = 0 then return acc.toList else go (depth - 1) (acc.push t)
    else if t == .sym o then go (depth + 1) (acc.push t)
    else go depth (acc.push t)
  go 0 #[]

/-- Split lexical items at the commas that are not inside brackets. -/
partial def splitTopCommas (ts : List Tok) : List (List Tok) :=
  let rec go (ts : List Tok) (depth : Nat) (cur : Array Tok) (acc : Array (List Tok)) : List (List Tok) :=
    match ts with
    | [] => (acc.push cur.toList).toList
    | t :: rest =>
      if t == .sym "," && depth = 0 then go rest depth #[] (acc.push cur.toList)
      else if t == .sym "{" || t == .sym "(" || t == .sym "[" || t == .sym "[[" then go rest (depth + 1) (cur.push t) acc
      else if t == .sym "}" || t == .sym ")" || t == .sym "]" || t == .sym "]]" then go rest (depth - 1) (cur.push t) acc
      else go rest depth (cur.push t) acc
  if ts = [] then [] else go ts 0 #[] #[]

/-- Run a parser on lexical items that are already split out, requiring it to read them all. -/
def subParse {α : Type} (p : P α) (ts : List Tok) : P α := do
  let line ← curLine
  let ls : Array Lexeme := (ts.map fun t => (⟨t, line⟩ : Lexeme)).toArray
  match (p ls).run 0 with
  | .ok (a, i) => if i = ls.size then return a else throw s!"line {line}: unexpected {repr (ls[i]?.map (·.tok))}"
  | .error e => throw e

end Asn1.Parse
