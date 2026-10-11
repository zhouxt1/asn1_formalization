import Asn1.X680.Syntax

/-!
# The numbers of an enumeration (X.680 20.3–20.6)

An enumerated value is its identifier (20.8). The integer associated with each item exists only for
encoding rules (20.3 NOTE). This file assigns those integers.
-/

namespace Asn1.X680

/-- The least integer `≥ c` not in `used`. It is found within `used.length + 1` steps. -/
def nextFree (used : List Int) (c : Int) : Int :=
  go (used.length + 1) c
where
  go : Nat → Int → Int
    | 0, c => c
    | k + 1, c => if c ∈ used then go k (c + 1) else c

/-- X.680 20.3, 20.6: each item of the root and of the additional enumeration, with its integer,
in textual order.
- A root identifier gets the next of 0, 1, 2, … not used by a "NamedNumber" of the root (20.3).
  The additions' numbers are not excluded: 20.5's example A, `{a, b, ..., c(0)}`, is invalid
  because `a` and `c` both get 0.
- An identifier among the additions gets the smallest value not used in the root that is greater
  than every preceding addition (20.6).

OPEN (ledger X680-12): 20.6 states this for "the first" identifier among the additions. Its
example C (`{a, b, ..., c(3), d}`, `d = 4`) and 20.4 apply it to every later one, as here. -/
def enumNumbers (root : List (String × Option Int)) (ext : Option (List (String × Option Int))) :
    List (String × Int) :=
  let rootNamed := root.filterMap (·.2)
  let (rootOut, _) := root.foldl (fun (acc : List (String × Int) × Int) item =>
      let (out, c) := acc
      match item.2 with
      | some k => (out ++ [(item.1, k)], c)
      | none => let v := nextFree rootNamed c; (out ++ [(item.1, v)], v + 1)) ([], 0)
  let rootVals := rootOut.map (·.2)
  let (extOut, _) := (ext.getD []).foldl (fun (acc : List (String × Int) × Option Int) item =>
      let (out, last) := acc
      match item.2 with
      | some k => (out ++ [(item.1, k)], some k)
      | none =>
        let v := nextFree rootVals (match last with | some l => max 0 (l + 1) | none => 0)
        (out ++ [(item.1, v)], some v)) ([], none)
  rootOut ++ extOut

end Asn1.X680
