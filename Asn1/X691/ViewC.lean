import Asn1.X691.Encode
import Asn1.X690.Decode

/-!
# The PER view, computed

`Visible.lean` defines the PER view of a type (`pInt`, `pSize`, `pStr`) as sets given by
predicates, and "lb", "ub" and the effective alphabet as least and greatest elements of those
sets, which is not computable. A decoder needs the numbers. This file computes the same view for
the constraints met in practice, as finite unions of intervals (`Ivs`), with the same `view`
function and the same reading of each constraint, so that each case of the proof that the two
agree (`ViewCSound.lean`) is the case of the definition it mirrors.

Each computed view is an `Option`: `none` when a part of the constraint is not one this file
evaluates (a value that is not a literal or a reference to one, a FROM that is not a union of
single values and ranges, …). Whether a constraint is PER-visible is decided exactly as `evalC`
decides it, so an unevaluated part is never mistaken for an invisible one.

Fuel is spent as the spec spends it: value notation is evaluated with `evalLit` at the fuel at
which `evalVal` reads it, and a FROM's element set at the fuel at which X.680's `eset` reads it.
-/

namespace Asn1.X691

open Asn1.X680
open Asn1.X690 (evalLit)

/-! ## Finite unions of intervals -/

/-- A finite union of intervals of integers; a `none` end is unbounded. -/
abbrev Ivs := List (Option Int × Option Int)

namespace Ivs

/-- An integer is in an interval. -/
def memI (p : Option Int × Option Int) (i : Int) : Bool := p.1.all (· ≤ i) && p.2.all (i ≤ ·)

def mem (s : Ivs) (i : Int) : Bool := s.any fun p => memI p i

def univ : Ivs := [(none, none)]

def point (i : Int) : Ivs := [(some i, some i)]

/-- The larger of two lower ends (`none` is below everything). -/
def maxLo : Option Int → Option Int → Option Int
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, b => b

/-- The smaller of two upper ends (`none` is above everything). -/
def minHi : Option Int → Option Int → Option Int
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

def inter (s t : Ivs) : Ivs := s.flatMap fun p => t.map fun q => (maxLo p.1 q.1, minHi p.2 q.2)

/-- An interval has an integer in it. -/
def nonempty (p : Option Int × Option Int) : Bool :=
  match p with
  | (some a, some b) => decide (a ≤ b)
  | _ => true

/-- The least element, if the set has one: `none` when it is empty or unbounded below. -/
def least? (s : Ivs) : Option Int :=
  let s := s.filter nonempty
  if s.any (·.1.isNone) then none else (s.filterMap (·.1)).min?

/-- The greatest element, if the set has one. -/
def greatest? (s : Ivs) : Option Int :=
  let s := s.filter nonempty
  if s.any (·.2.isNone) then none else (s.filterMap (·.2)).max?

/-- The natural numbers of the set. -/
def nats (s : Ivs) : Ivs := s.inter [(some 0, none)]

/-- The least natural number of the set (`natLeast?`). -/
def natLeast? (s : Ivs) : Option Nat := (s.nats.least?).map Int.toNat

/-- The greatest natural number of the set (`natGreatest?`). -/
def natGreatest? (s : Ivs) : Option Nat := (s.nats.greatest?).map Int.toNat

/-- The members of a list of naturals, in order. -/
def filterNat (s : Ivs) (xs : List Nat) : List Nat := xs.filter fun c => s.mem c

end Ivs

/-- A PER-visible set, computed (`PSet`): root, root with additions, extensibility. -/
structure CSet where
  r : Ivs
  a : Ivs
  ext : Bool
  deriving Repr, Inhabited

namespace CSet

def empty : CSet := ⟨[], [], false⟩
def plain (s : Ivs) : CSet := ⟨s, s, false⟩
def univ : CSet := plain Ivs.univ
def union (A B : CSet) : CSet := ⟨A.r ++ B.r, A.r ++ B.r ++ A.a ++ B.a, A.ext || B.ext⟩
def inter (A B : CSet) : CSet := ⟨A.r.inter B.r, A.r.inter B.r ++ A.a.inter B.a, A.ext || B.ext⟩
def ofSpecs (extensible : Bool) (r : CSet) (x : Option CSet) : CSet :=
  ⟨r.r, r.a ++ (match x with | some e => e.a | none => []), extensible || r.ext⟩
def rootOnly (A : CSet) : CSet := plain A.r
def within (g : Ivs) (A : CSet) : CSet := ⟨g.inter A.r, g.inter A.a, A.ext⟩

end CSet

/-- Set arithmetic on computed views that may be unknown (`none`). -/
def optAlg {β : Type} (A : Alg β) (all : Option β) : Alg (Option β) :=
  ⟨fun x y => do pure (A.union (← x) (← y)), fun x y => do pure (A.inter (← x) (← y)),
   fun e r x => do
     let r ← r
     match x with
     | some (some x) => pure (A.ofSpecs e r (some x))
     | some none => none
     | none => pure (A.ofSpecs e r none),
   all⟩

def csetAlg (all : Ivs) : Alg CSet := ⟨CSet.union, CSet.inter, CSet.ofSpecs, CSet.plain all⟩

/-- A computed view's algebra, with the governor's root `g` (unknown: `none`). -/
def cAlg (g : Option Ivs) : Alg (Option CSet) :=
  optAlg (csetAlg (g.getD [])) (g.map CSet.plain)

/-! ## Integers -/

/-- The integer value notation denotes at fuel `n`, when it is a literal or references one
(`evalLit`). -/
def intLit (E : Env) (n : Nat) (sc : Scope) (v : Val) : Option Int :=
  match evalLit E n sc v with
  | some (.int i) => some i
  | _ => none

/-- An endpoint of an integer value range, at the fuel of `EvalBound`: `some (some e)` an end
(`none` unbounded), `some none` an empty range (MAX below, MIN above), `none` unknown. -/
def loEnd (E : Env) : Nat → Scope → Bound → Bool → Option (Option (Option Int))
  | 0, _, _, _ => some none
  | _ + 1, _, .min, _ => some (some none)
  | _ + 1, _, .max, _ => some none
  | n + 1, sc, .val v, op => (intLit E n sc v).map fun l => some (some (if op then l + 1 else l))

def hiEnd (E : Env) : Nat → Scope → Bound → Bool → Option (Option (Option Int))
  | 0, _, _, _ => some none
  | _ + 1, _, .max, _ => some (some none)
  | _ + 1, _, .min, _ => some none
  | n + 1, sc, .val v, op => (intLit E n sc v).map fun h => some (some (if op then h - 1 else h))

/-- `intAtom`, computed. The outer `Option` is PER-visibility, exactly as `intAtom`'s; the inner is
whether it was evaluated. -/
def intAtomC (E : Env) (n : Nat) (sc : Scope) (g : Option Ivs) (rec : Scope → Ty → Option CSet) :
    Elem → Option (Option CSet)
  | .single v => some do
    let g ← g
    let i ← intLit E n sc v
    pure (.plain (g.inter (Ivs.point i)))
  | .range lo lo' hi hi' => some do
    let g ← g
    let l ← loEnd E n sc lo lo'
    let h ← hiEnd E n sc hi hi'
    match l, h with
    | some l, some h => pure (.plain (g.inter [(l, h)]))
    | _, _ => pure (.plain [])
  | .contained t _ => if tyDep E n sc t then none else some do
    let g ← g
    let P ← rec sc t
    pure (.plain (g.inter P.r))
  | _ => none

/-- `intCons`, computed. -/
def intConsC (E : Env) (n : Nat) (sc : Scope) (P : Option CSet) (rec : Scope → Ty → Option CSet)
    (c : Constraint) : Option (Option CSet) :=
  if consDep E n sc c then none
  else evalC (cAlg (P.map (·.r))) (intAtomC E n sc (P.map (·.r)) rec) c

/-- `pInt`, computed. -/
def pIntC (E : Env) : Nat → Scope → Ty → Option CSet :=
  view E (fun _ t => match t with
      | .integer _ => some (some CSet.univ)
      | _ => none)
    (some CSet.empty) (Option.map CSet.rootOnly) (fun n sc _ P rec c => intConsC E n sc P rec c)

/-! ## Sizes -/

/-- `sizeOf`, computed: the sizes as integers (only the naturals among them count). -/
def sizeOfC (E : Env) (n : Nat) (sc : Scope) (rec : Scope → Ty → Option CSet) (c : Constraint) :
    Option (Option CSet) :=
  intConsC E n sc (some (.plain [(some 0, none)])) rec c

def sizeAtomC (E : Env) (n : Nat) (sc : Scope) (g : Option Ivs) : Elem → Option (Option CSet)
  | .size c => (sizeOfC E n sc (pIntC E n) c).map fun P => do
    let g ← g
    let P ← P
    pure (P.within g)
  | _ => none

/-- `pSize`, computed: sets of naturals, as sets of integers whose naturals they are. -/
def pSizeC (E : Env) : Nat → Scope → Ty → Option CSet :=
  view E (fun _ t => match t with
      | .bitString _ | .octetString | .sequenceOf _ | .setOf _ => some (some CSet.univ)
      | _ => none)
    (some CSet.empty) (Option.map CSet.rootOnly)
    (fun n sc _ P _ c => if consDep E n sc c then none
      else evalC (cAlg (P.map (·.r))) (sizeAtomC E n sc (P.map (·.r))) c)

/-! ## Known-multiplier character strings -/

/-- Code points as intervals. -/
def charIvs (cs : List Nat) : Ivs := cs.map fun c => (some (c : Int), some (c : Int))

/-- A character range of a permitted alphabet as an interval. -/
def rangeIvs (rs : CharRanges) : Ivs := rs.map fun (lo, hi) => (some (lo : Int), some (hi : Int))

/-- The single character a value range's end denotes (`Val.le` orders only one-character
strings), at the fuel of `EvalBound`: `some (some e)` an end (`none` unbounded), `some none` an
empty range, `none` unknown. -/
def charEnd (E : Env) (lower : Bool) : Nat → Scope → Bound → Bool → Option (Option (Option Int))
  | 0, _, _, _ => some none
  | _ + 1, _, .min, _ => if lower then some (some none) else some none
  | _ + 1, _, .max, _ => if lower then some none else some (some none)
  | n + 1, sc, .val v, op => match evalLit E n sc v with
    | some (.chars [c]) =>
      some (some (some (if lower then (if op then c + 1 else c) else (if op then (c : Int) - 1 else c))))
    | _ => none

/-- The types whose values are one abstract value exactly when they are equal (`eqv` is `=` on
every pair of values), through references, tags and constraints: `X690.eqIsEq` without BIT STRING,
whose `eqv` holds only between bit strings. -/
def valEqIsEq (E : Env) : Nat → Scope → Ty → Bool
  | 0, _, _ => false
  | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
    | some (sc', t) => valEqIsEq E n sc' t
    | none => false
  | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => valEqIsEq E n sc' t
    | none => false
  | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
    | some (sc', t) => valEqIsEq E n sc' t
    | none => false
  | n + 1, sc, .tagged _ _ t => valEqIsEq E n sc t
  | n + 1, sc, .constrained t _ => valEqIsEq E n sc t
  | _ + 1, _, .boolean | _ + 1, _, .integer _ | _ + 1, _, .enumerated _ _ | _ + 1, _, .null
  | _ + 1, _, .objectIdentifier | _ + 1, _, .relativeOid | _ + 1, _, .octetString
  | _ + 1, _, .restricted _ | _ + 1, _, .utcTime | _ + 1, _, .generalizedTime => true
  | _ + 1, _, _ => false

mutual
  /-- The characters of the values of a FROM's element set, as X.680's `eset` reads it at fuel `k`
  among the strings over `(S, A)`, of the parent type `pt`: a union of single values and value
  ranges (each set is then fixed: its root is all its values). `none` for anything else. -/
  def fromES (E : Env) (sc : Scope) (pt : Ty) (S A : Ivs) : Nat → ElemSet → Option Ivs
    | 0, _ => some []
    | k + 1, .elem el => fromElem E sc pt S A k el
    | k + 1, .union a b => do pure ((← fromES E sc pt S A k a) ++ (← fromES E sc pt S A k b))
    | _ + 1, _ => none

  def fromElem (E : Env) (sc : Scope) (pt : Ty) (S A : Ivs) : Nat → Elem → Option Ivs
    | 0, _ => some []
    -- 51.2: a string, if it is one of the parent's
    | k + 1, .single v => match evalLit E k sc v with
      | some (.chars cs) =>
        if valEqIsEq E k sc pt then
          some (if S.mem cs.length && cs.all (fun c => A.mem c) then charIvs cs else [])
        else none
      | _ => none
    -- 51.4: the one-character strings between the ends (MIN and MAX: the parent's)
    | k + 1, .range lo lo' hi hi' => match k with
      | 0 => some []
      | k' + 1 => match charEnd E true (k' + 1) sc lo lo', charEnd E false (k' + 1) sc hi hi' with
        | some (some l), some (some h) =>
          if l.isNone && h.isNone then none
          else some (if S.mem 1 then A.inter [(l, h)] else [])
        | some none, some _ | some _, some none => some []
        | _, _ => none
    | _ + 1, _ => none
end

/-- `strAtom`'s FROM case, computed: the alphabet of the values of `c`'s root and of all its values,
and its extensibility, as X.680's `cons` reads it at fuel `n`. -/
def fromC (E : Env) (sc : Scope) (pt : Ty) (S A : Ivs) : Nat → Constraint → Option CSet
  | 0, _ => some CSet.empty
  | m + 1, .mk root ext adds => do
    let r ← fromES E sc pt S A m root
    let x ← (adds.map (fromES E sc pt S A m)).getD (some [])
    pure ⟨A.inter r, A.inter (r ++ x), ext || structExt E m sc pt⟩
  | _ + 1, _ => none

def strAtomC (E : Env) (n : Nat) (sc : Scope) (pt : Ty) (P : Option (Ivs × Ivs))
    (rec : Scope → Ty → Option (CSet × CSet)) : Elem → Option (Option (CSet × CSet))
  | .size c => (sizeOfC E n sc (pIntC E n) c).map fun Q => do
    let (S, A) ← P
    let Q ← Q
    pure (Q.within S, .plain A)
  | .from_ c =>
    if consDep E n sc c then none else some do
    let (S, A) ← P
    let V ← fromC E sc pt S A n c
    pure (.plain S, V)
  | .contained t _ =>
    if tyDep E n sc t then none else some do
    let (S, A) ← P
    let Q ← rec sc t
    pure (.plain (S.inter Q.1.r), .plain (A.inter Q.2.r))
  | _ => none

def pairAlgC (sizes alpha : Ivs) : Alg (CSet × CSet) :=
  ⟨fun x y => (x.1.union y.1, x.2.union y.2), fun x y => (x.1.inter y.1, x.2.inter y.2),
   fun e r x => (CSet.ofSpecs e r.1 (x.map (·.1)), CSet.ofSpecs e r.2 (x.map (·.2))),
   (CSet.plain sizes, CSet.plain alpha)⟩

/-- `pStr`, computed. -/
def pStrC (E : Env) : Nat → Scope → Ty → Option (CSet × CSet) :=
  view E (fun _ t => match t with
      | .restricted k => if k.knownMultiplier then some (some (CSet.univ, .plain (rangeIvs k.chars)))
        else none
      | _ => none)
    (some (CSet.empty, CSet.empty)) (Option.map fun P => (P.1.rootOnly, P.2.rootOnly))
    (fun n sc pt P rec c => if consDep E n sc c then none else
      let g := P.map fun P => (P.1.r, P.2.r)
      evalC (optAlg (pairAlgC ((g.map (·.1)).getD []) ((g.map (·.2)).getD []))
          (g.map fun (S, A) => (CSet.plain S, CSet.plain A)))
        (strAtomC E n sc pt g rec) c)

/-- Adjacent duplicates removed: `eraseDups` on a sorted list, in one pass (`dedupAdj_eq`). -/
def dedupAdj : List Nat → List Nat
  | a :: b :: l => if a = b then dedupAdj (b :: l) else a :: dedupAdj (b :: l)
  | l => l

/-- `effAlphabet`, computed (the sorted alphabet deduplicated in one pass, not by `eraseDups`, which
is quadratic: 63K characters for BMPString). -/
def effAlphabetC (k : StrType) (A : CSet) : List Nat :=
  let all := dedupAdj ((k.chars.flatMap fun (lo, hi) => List.range' lo (hi + 1 - lo)).mergeSort
    (fun a b => decide (a ≤ b)))
  if A.ext then all else A.r.filterNat all

end Asn1.X691
