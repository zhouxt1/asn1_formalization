import Asn1.X680.Tags
import Asn1.X691.Procedures

/-!
# PER-visible constraints and the effective constraints (X.691 3.7, 10.3)

PER does not encode against a type's value set (X.680 `sem`): it encodes against the type with the
constraints that are not PER-visible removed (10.3, 10.4.1). This file computes that *PER view* of a
type, for the four kinds of type whose encoding a constraint can change:
- integers (10.3.18): the root values, all values and extensibility (`pInt`), from which "lb" and
  "ub" are the least and greatest root values (3.7.7, 3.7.24, 11.5.2);
- bit strings, octet strings and the sequence-of and set-of types (10.3.9, 16.1, 17.1, 20.1): the
  sizes (`pSize`);
- the known-multiplier character string types (10.3.7, 10.3.10–10.3.12): a pair of an effective size
  constraint and an effective permitted-alphabet constraint (`pStr`);
- the time types (10.3.13): the time values the property settings allow (`pTime`).
SEQUENCE, SET, CHOICE and ENUMERATED are extensible for PER exactly when their notation has an
extension marker, whatever constraints they have (10.3.22, B.1.9); constraints on every other type
are not PER-visible (10.3.14–10.3.18).

## How a constraint is read

Every constraint is set arithmetic over atoms (X.680 50, 51). An atom is PER-visible or not
(10.3.1–10.3.18), and 10.3.21 says what set arithmetic does with the parts that are not:
- `V UNION I` is not PER-visible;
- `V INTERSECTION I` is the PER-visible part;
- `A EXCEPT B` is `A`: the EXCEPT and its value set are ignored;
- an "ElementSetSpecs" with an ellipsis is PER-visible only if its root and its additions both are
  (Annex B.2.2.10, `V, ..., I => I`).
A constraint that is not PER-visible, serially applied, leaves the parent's root values and removes
its extensibility (10.3.20, X.680 50.11).

For the known-multiplier strings, PER evaluates each constraint to an effective size constraint and an
effective permitted-alphabet constraint (B.2.3): a SIZE atom constrains only the first, a FROM atom
only the second, union and intersection act on each separately (B.2.3.8), and an ellipsis makes both
extensible. An extensible permitted-alphabet constraint is not PER-visible (10.3.11): the alphabet is
then that of the unconstrained type (B.2.3.9).

The PER view is computed with `anyHook` for contents constraints: a contents constraint is never
PER-visible (10.3.18), so what it means does not change the view.
-/

namespace Asn1.X691

open Asn1.X680
open Classical

/-- A contents hook that admits everything. CONTAINING is not PER-visible (10.3.18), so the PER view
of a type does not depend on the encoding rules' hook. -/
def anyHook : ContentsHook := fun _ _ _ _ _ => True

/-! ## Sets with a root, as X.680 50.5 evaluates them -/

/-- A PER-visible set: its root, its root together with its extension additions, and whether it is
extensible (X.680 50.4, 50.5; X.691 3.7.11). -/
structure PSet (α : Type) where
  r : α → Prop
  a : α → Prop
  ext : Bool

namespace PSet

variable {α : Type}

def empty : PSet α := ⟨fun _ => False, fun _ => False, false⟩

/-- A set with no extension additions, not extensible. -/
def plain (s : α → Prop) : PSet α := ⟨s, s, false⟩

def univ : PSet α := plain fun _ => True

/-- X.680 50.2 b), 50.4 b), 50.5 -/
def union (A B : PSet α) : PSet α :=
  ⟨fun v => A.r v ∨ B.r v, fun v => A.r v ∨ B.r v ∨ A.a v ∨ B.a v, A.ext || B.ext⟩

/-- X.680 50.2 c), 50.4 c), 50.5 -/
def inter (A B : PSet α) : PSet α :=
  ⟨fun v => A.r v ∧ B.r v, fun v => (A.r v ∧ B.r v) ∨ (A.a v ∧ B.a v), A.ext || B.ext⟩

/-- X.680 49.6, 50.4 a), 50.5: a root, an ellipsis, and additions. -/
def ofSpecs (extensible : Bool) (r : PSet α) (x : Option (PSet α)) : PSet α :=
  ⟨r.r, fun v => r.a v ∨ ∃ e, x = some e ∧ e.a v, extensible || r.ext⟩

/-- X.680 51.3.3, 52.4, 52.5 and X.691 10.3.20: the root values only, not extensible. -/
def rootOnly (A : PSet α) : PSet α := plain A.r

/-- The values of `A` among those of the governor `g` (X.680 50.8: the parent's root). -/
def within (g : α → Prop) (A : PSet α) : PSet α :=
  ⟨fun v => g v ∧ A.r v, fun v => g v ∧ A.a v, A.ext⟩

end PSet

/-- What set arithmetic does on a kind of PER view. -/
structure Alg (β : Type) where
  union : β → β → β
  inter : β → β → β
  ofSpecs : Bool → β → Option β → β
  /-- the governor's root: what `ALL EXCEPT …` is once its EXCEPT is ignored -/
  all : β

/-- X.691 10.3.21, X.680 50: an "ElementSetSpec", given what each atom is (`none` when it is not
PER-visible). -/
def evalES {β : Type} (A : Alg β) (atom : Elem → Option β) : ElemSet → Option β
  | .elem e => atom e
  -- `V UNION I => I`
  | .union a b => match evalES A atom a, evalES A atom b with
    | some x, some y => some (A.union x y)
    | _, _ => none
  -- `V INTERSECTION I => V`
  | .inter a b => match evalES A atom a, evalES A atom b with
    | some x, some y => some (A.inter x y)
    | some x, none => some x
    | none, some y => some y
    | none, none => none
  -- "the EXCEPT and the following value set is completely ignored"
  | .except a _ => evalES A atom a
  -- OPEN (ledger X691-5): `ALL EXCEPT b` with its EXCEPT ignored is ALL: the governor's values, a
  -- PER-visible constraint that excludes nothing.
  | .allExcept _ => some A.all

/-- X.691 10.3.3–10.3.5, 10.3.20, 10.3.21: a constraint, if it is PER-visible. A table constraint, a
component relation constraint, a user-defined constraint and a contents constraint are not. An
ellipsis keeps the constraint PER-visible only if root and additions both are (B.2.2.10). -/
def evalC {β : Type} (A : Alg β) (atom : Elem → Option β) : Constraint → Option β
  | .mk root ext adds =>
    match evalES A atom root, adds.map (evalES A atom) with
    | some r, none => some (A.ofSpecs ext r none)
    | some r, some (some x) => some (A.ofSpecs ext r (some x))
    | _, _ => none
  | _ => none

def psetAlg {α : Type} (all : α → Prop) : Alg (PSet α) :=
  ⟨PSet.union, PSet.inter, PSet.ofSpecs, PSet.plain all⟩

/-- B.2.3.8: the pair of an effective size constraint and an effective permitted-alphabet
constraint, componentwise; an ellipsis makes both extensible. -/
def pairAlg (sizes alpha : Nat → Prop) : Alg (PSet Nat × PSet Nat) :=
  ⟨fun x y => (x.1.union y.1, x.2.union y.2), fun x y => (x.1.inter y.1, x.2.inter y.2),
   fun e r x => (PSet.ofSpecs e r.1 (x.map (·.1)), PSet.ofSpecs e r.2 (x.map (·.2))),
   (PSet.plain sizes, PSet.plain alpha)⟩

/-! ## Textual dependence on a table constraint (10.3.6, 3.7.26) -/

mutual
  /-- X.691 10.3.6, 3.7.26: the notation of a type refers, through references and the constraints
  it meets on the way, to a type constrained by a table or component relation constraint.

  OPEN (ledger X691-15): dependence through value references (a value whose governor has a table
  constraint) is not followed, and variable constraints (10.3.2, X.683 10.3–10.4) are not
  represented, since abstract syntax parameters are not (ledger X683-1). -/
  def tyDep (E : Env) : Nat → Scope → Ty → Bool
    | 0, _, _ => false
    | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
      | some (sc', t) => tyDep E n sc' t
      | none => false
    | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
      | some (sc', t) => tyDep E n sc' t
      | none => false
    | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
      | some (sc', t) => tyDep E n sc' t
      | none => false
    | n + 1, sc, .tagged _ _ t => tyDep E n sc t
    | n + 1, sc, .constrained t c => tyDep E n sc t || consDep E n sc c
    | _ + 1, _, _ => false

  /-- A constraint that is, or refers to, a table or component relation constraint. -/
  def consDep (E : Env) : Nat → Scope → Constraint → Bool
    | 0, _, _ => false
    | _ + 1, _, .table _ _ => true
    | n + 1, sc, .mk r _ adds => esDep E n sc r || (match adds with
      | some a => esDep E n sc a
      | none => false)
    | _ + 1, _, _ => false

  def esDep (E : Env) : Nat → Scope → ElemSet → Bool
    | 0, _, _ => false
    | n + 1, sc, .elem e => elDep E n sc e
    | n + 1, sc, .union a b | n + 1, sc, .inter a b | n + 1, sc, .except a b =>
      esDep E n sc a || esDep E n sc b
    | n + 1, sc, .allExcept b => esDep E n sc b

  def elDep (E : Env) : Nat → Scope → Elem → Bool
    | 0, _, _ => false
    | n + 1, sc, .contained t _ => tyDep E n sc t
    | n + 1, sc, .size c | n + 1, sc, .from_ c | n + 1, sc, .withComponent c => consDep E n sc c
    | n + 1, sc, .typeC t => tyDep E n sc t
    | _ + 1, _, _ => false
end

/-! ## Following a type one step -/

/-- One step towards the built-in type, for the notations that are neither tagged nor constrained:
references (X.680 13.19, 14), selections (10.6.2), fixed-type fields of classes (X.681 14.3), value
sets from objects (X.681 15.7) and INSTANCE OF (X.681 C.7). `none` for a built-in type. -/
def stepTy (E : Env) (n : Nat) (sc : Scope) : Ty → Option (Scope × Ty)
  | .ref name => resolveTy E n sc none name []
  | .extRef mn name => resolveTy E n sc (some mn) name []
  | .paramRef mn name args => resolveTy E n sc mn name args
  | .selection nm t => match builtin E n sc t with
    | some (sc', .choice root ext) => (findAlt (choiceAlts root ext) nm).map fun a => (sc', a.ty)
    | _ => none
  | .classField cls path => match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
    | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => some (sc', t)
    | _ => none
  | .fromObjects src path => match objSetClass E n sc src with
    | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => some (sc', t)
      | _ => none
    | none => none
  | .instanceOf cls => some (sc, instanceOfTy cls)
  | _ => none

/-- The PER view of a type, by fuel: tags are invisible (10.6.3), references are followed, and a
constraint is applied to its parent's view by `cons` if it is PER-visible; otherwise the parent's
root is kept and its extensibility removed (10.3.20). `base` is the view of a built-in type. -/
def view {β : Type} (E : Env) (base : Scope → Ty → Option β) (empty : β) (rootOnly : β → β)
    (cons : Nat → Scope → Ty → β → (Scope → Ty → β) → Constraint → Option β) :
    Nat → Scope → Ty → β
  | 0, _, _ => empty
  | n + 1, sc, .tagged _ _ t => view E base empty rootOnly cons n sc t
  | n + 1, sc, .constrained t c =>
    let P := view E base empty rootOnly cons n sc t
    (cons n sc t P (view E base empty rootOnly cons n) c).getD (rootOnly P)
  | n + 1, sc, t => match stepTy E n sc t with
    | some (sc', t') => view E base empty rootOnly cons n sc' t'
    | none => (base sc t).getD empty

/-! ## Integers (10.3.18, 13) -/

/-- X.691 10.3.18, X.680 51.2–51.4: an atom of a constraint on an integer type, among the governor
`g` (the parent's root, X.680 50.8). Single values, value ranges and contained subtypes are
PER-visible unless they depend textually on a table constraint (10.3.6). `rec` is the PER view of a
contained type; X.680 51.3.2 and 52.4 take its root values, not its extensibility. -/
def intAtom (E : Env) (n : Nat) (sc : Scope) (g : Int → Prop) (rec : Scope → Ty → PSet Int) :
    Elem → Option (PSet Int)
  | .single v => some (.plain fun i => g i ∧ evalVal E n sc v (.int i))
  | .range lo lo' hi hi' => some (.plain fun i => g i ∧
      ∃ l h, EvalBound E n sc lo l ∧ EvalBound E n sc hi h ∧ RangeHas l lo' h hi' (.int i))
  | .contained t _ => if tyDep E n sc t then none else some (.plain fun i => g i ∧ (rec sc t).r i)
  | _ => none

/-- A constraint on an integer type with view `P`. -/
def intCons (E : Env) (n : Nat) (sc : Scope) (P : PSet Int) (rec : Scope → Ty → PSet Int)
    (c : Constraint) : Option (PSet Int) :=
  if consDep E n sc c then none
  else evalC (psetAlg P.r) (intAtom E n sc P.r rec) c

/-- The PER view of an integer type (10.3.18): its root values, all values, and extensibility. -/
def pInt (E : Env) : Nat → Scope → Ty → PSet Int :=
  view E (fun _ t => match t with
      | .integer _ => some PSet.univ
      | _ => none)
    PSet.empty PSet.rootOnly (fun n sc _ P rec c => intCons E n sc P rec c)

/-- X.691 3.7.7, 11.5.2: "lb", the least root value, if there is one. -/
noncomputable def least? (S : Int → Prop) : Option Int :=
  if h : ∃ l, IsLeast {x | S x} l then some h.choose else none

/-- X.691 3.7.7, 11.5.2: "ub", the greatest root value, if there is one. -/
noncomputable def greatest? (S : Int → Prop) : Option Int :=
  if h : ∃ u, IsGreatest {x | S x} u then some h.choose else none

/-! ## Sizes (10.3.9, 16, 17, 20) -/

/-- X.680 51.5, X.691 10.3.9: a size constraint, as the PER view of its constraint on
INTEGER (0..MAX). -/
def sizeOf (E : Env) (n : Nat) (sc : Scope) (rec : Scope → Ty → PSet Int) (c : Constraint) :
    Option (PSet Nat) :=
  (intCons E n sc (.plain fun i => 0 ≤ i) rec c).map fun P =>
    ⟨fun k => P.r (k : Int), fun k => P.a (k : Int), P.ext⟩

/-- An atom of a constraint on a bit string, octet string, sequence-of or set-of type: only a size
constraint is PER-visible (10.3.9, 10.3.18, 16.1, 17.1, 20.1). -/
def sizeAtom (E : Env) (n : Nat) (sc : Scope) (g : Nat → Prop) : Elem → Option (PSet Nat)
  | .size c => (sizeOf E n sc (pInt E n) c).map (PSet.within g)
  | _ => none

/-- The PER view of the sizes of a bit string, octet string, sequence-of or set-of type. -/
def pSize (E : Env) : Nat → Scope → Ty → PSet Nat :=
  view E (fun _ t => match t with
      | .bitString _ | .octetString | .sequenceOf _ | .setOf _ => some PSet.univ
      | _ => none)
    PSet.empty PSet.rootOnly
    (fun n sc _ P _ c => if consDep E n sc c then none else evalC (psetAlg P.r) (sizeAtom E n sc P.r) c)

/-- X.691 3.7.8, 10.3.10, 16.4, 17.2, 20.2, 30.3: the least size of a root value ("lb", "alb"; zero
when nothing constrains the minimum). -/
noncomputable def natLeast? (S : Nat → Prop) : Option Nat :=
  if h : ∃ l, IsLeast {x | S x} l then some h.choose else none

/-- X.691 16.4, 17.2, 20.2, 30.2: the greatest size of a root value ("ub", "aub"), if there is one. -/
noncomputable def natGreatest? (S : Nat → Prop) : Option Nat :=
  if h : ∃ u, IsGreatest {x | S x} u then some h.choose else none

/-! ## Known-multiplier character strings (10.3.7, 10.3.10–10.3.12, 30) -/

/-- X.691 3.7.16, 30.1: the known-multiplier character string types. -/
def _root_.Asn1.X680.StrType.knownMultiplier : StrType → Bool
  | .numeric | .printable | .visible | .ia5 | .bmp | .universal => true
  | _ => false

/-- The strings of characters in `A` whose lengths are in `S`: the values of a parent type whose
PER view is `(S, A)`, which a permitted-alphabet constraint is evaluated among. -/
def stringsOver (S A : Nat → Prop) : Val → Prop :=
  fun w => ∃ cs, w = .chars cs ∧ S cs.length ∧ ∀ c ∈ cs, A c

/-- An atom of a constraint on a known-multiplier character string type with parent view
`(S, A)`, as a pair of an effective size and an effective permitted-alphabet constraint (B.2.3):
- SIZE (10.3.9): the sizes, any character of the parent;
- FROM (10.3.11, X.680 51.7): the characters of the root values of the parent type that the
  constraint allows, any size; extensible if that constraint is;
- a contained subtype (X.680 51.3): the root of its view (52.4);
- single values (10.3.17) and PATTERN (10.3.8) are not PER-visible. -/
def strAtom (E : Env) (n : Nat) (sc : Scope) (pt : Ty) (S A : Nat → Prop)
    (rec : Scope → Ty → PSet Nat × PSet Nat) : Elem → Option (PSet Nat × PSet Nat)
  | .size c => (sizeOf E n sc (pInt E n) c).map fun P => (P.within S, .plain A)
  -- OPEN (ledger X691-14): X.680 51.7.3: the sub-alphabet is the characters of "the values of the
  -- parent string type which are allowed by the Constraint", so the parent's sizes count:
  -- `IA5String (SIZE (1)) (FROM ("AB"))` has an empty alphabet, as X.680's `elem` has it.
  | .from_ c =>
    if consDep E n sc c then none else
    let g := stringsOver S A
    let V := cons E anyHook n sc [] pt ⟨g, g, false⟩ c
    some (.plain S, ⟨fun ch => A ch ∧ ∃ s, V.root s ∧ ch ∈ s.charList,
                     fun ch => A ch ∧ ∃ s, V.all s ∧ ch ∈ s.charList, V.ext⟩)
  | .contained t _ =>
    if tyDep E n sc t then none else
    let P := rec sc t
    some (.plain fun k => S k ∧ P.1.r k, .plain fun ch => A ch ∧ P.2.r ch)
  | _ => none

/-- The PER view of a known-multiplier character string type: its effective size constraint and its
effective permitted-alphabet constraint, each with its root, additions and extensibility.

OPEN (ledger X691-6): 3.7.8, 3.7.9, 10.3.10 and 10.3.12 define the effective constraints by the
values of the constrained type. B.2.3.8 computes them componentwise, which is the same unless a
component is empty (an empty alphabet allows only the empty string, whatever the size constraint
says). We compute componentwise, as B.2.3 and implementations do.

OPEN (ledger X691-13): 10.3.11 makes a permitted-alphabet constraint PER-visible if it is "not
extensible after application of X.680 52.3 to 52.5", which does not say whether an ellipsis around
`FROM (…) ^ SIZE (…)` makes the FROM extensible. We follow B.2.3.8–B.2.3.9 and B.3 (A12, A13, A15,
A16, A17): the alphabet is extensible exactly when the effective permitted-alphabet constraint is,
by the pair arithmetic above, after serial application (which removes extensibility, X.680 50.11);
an extensible alphabet is then the whole alphabet, not a constraint that is not PER-visible (which
in a union would make the size invisible too, contradicting B.3 A15). -/
def pStr (E : Env) : Nat → Scope → Ty → PSet Nat × PSet Nat :=
  view E (fun _ t => match t with
      | .restricted k => if k.knownMultiplier then some (PSet.univ, .plain fun c => k.chars.mem c)
        else none
      | _ => none)
    (PSet.empty, PSet.empty) (fun P => (P.1.rootOnly, P.2.rootOnly))
    (fun n sc pt P rec c => if consDep E n sc c then none else
      evalC (pairAlg P.1.r P.2.r) (strAtom E n sc pt P.1.r P.2.r rec) c)

/-- X.691 10.3.12, 30.5.1: the effective permitted alphabet of a known-multiplier type `k` with view
`A`, as code points in ascending (canonical, X.680 43.3) order. An extensible effective
permitted-alphabet constraint is not PER-visible (10.3.11, B.2.3.9): the whole alphabet of the type. -/
noncomputable def effAlphabet (k : StrType) (A : PSet Nat) : List Nat :=
  let all := ((k.chars.flatMap fun (lo, hi) => List.range' lo (hi + 1 - lo)).mergeSort
    (fun a b => decide (a ≤ b))).eraseDups
  if A.ext then all else all.filter fun c => decide (A.r c)

/-! ## Time types (10.3.13, 32.1.1) -/

/-- X.691 10.3.13: on a time type only property settings (X.680 51.10) are PER-visible. -/
def timeAtom (g : TimeV → Prop) : Elem → Option (PSet TimeV)
  | .settings ps => some (.plain fun t => g t ∧ t.satisfies ps)
  | _ => none

/-- X.680 38: the values of the time types, by their property settings (38.4). -/
def timeBase : Ty → Option (PSet TimeV)
  | .time => some (.plain fun t => t.Wf)
  | .date => some (.plain fun t => t.Wf ∧ t.satisfies dateSettings)
  | .timeOfDay => some (.plain fun t => t.Wf ∧ t.satisfies timeOfDaySettings)
  | .dateTime => some (.plain fun t => t.Wf ∧ t.satisfies dateTimeSettings)
  | .duration => some (.plain fun t => t.Wf ∧ t.satisfies durationSettings)
  | _ => none

/-- X.691 10.3.13, 32.1.1: the time values of a time type under its PER-visible constraints.
"Property setting constraints … which are extensible … are not PER-visible": a constraint whose
evaluation is extensible is dropped like any other that is not PER-visible. -/
def pTime (E : Env) : Nat → Scope → Ty → PSet TimeV :=
  view E (fun _ t => timeBase t) PSet.empty PSet.rootOnly
    (fun n sc _ P _ c => if consDep E n sc c then none else
      match evalC (psetAlg P.r) (timeAtom P.r) c with
      | some Q => if Q.ext then none else some Q
      | none => none)

end Asn1.X691
