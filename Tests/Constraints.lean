import Asn1.X680.Semantics

/-! The semantics of constraints, checked against X.680's own examples (Annex I.4, informative). -/

open Asn1.X680

def rng (a b : Int) : ElemSet := .elem (.range (.val (.int a)) false (.val (.int b)) false)
def cRoot (s : ElemSet) : Constraint := .mk s false none
def cExt (s x : ElemSet) : Constraint := .mk s true (some x)

def M : Module := { name := "M", header := ⟨.explicit, false⟩ }
def Es : Env := [M]
/-- No contents constraints here, so the encoding rules do not matter. -/
def H0 : ContentsHook := fun _ _ _ _ _ => True

/-- I.4.2: `A1 ::= INTEGER (1..32, ... , 33..128)` -/
def A1 : Ty := .constrained (.integer []) (cExt (rng 1 32) (rng 33 128))
/-- I.4.2: `B2 ::= A1 (1..16)` -/
def B2 : Ty := .constrained A1 (cRoot (rng 1 16))
/-- I.4.2: `A3 ::= INTEGER ((1..32) INTERSECTION (MIN..63))`, which contains 1 to 32. -/
def A3 : Ty := .constrained (.integer [])
  (cRoot (.inter (rng 1 32) (.elem (.range .min false (.val (.int 63)) false))))
/-- I.4.4: a contained subtype is not extensible and loses its additions: `INTEGER (A1)`. -/
def C1 : Ty := .constrained (.integer []) (cRoot (.elem (.contained A1 false)))
/-- I.4.3.8, "N1 EXCEPT E2 => N, Root: R1 EXCEPT R2": `INTEGER ((1..10) EXCEPT E)` with
`E ::= INTEGER (1..3, ..., 4..5)`. -/
def E : Ty := .constrained (.integer []) (cExt (rng 1 3) (rng 4 5))
def NE : Ty := .constrained (.integer [])
  (cRoot (.except (rng 1 10) (.elem (.contained E false))))
/-- An extensible size constraint: `OCTET STRING (SIZE (1..4, ...))`. -/
def OS : Ty := .constrained .octetString (cRoot (.elem (.size (.mk (rng 1 4) true none))))

attribute [local simp] sem cons eset elem EvalBound evalVal InRange RangeHas Val.le Val.lt VSet.plain ESet.fixed sizeParent VSet.keepExt structExt builtin
  VSet.ofSpecs ESet.union ESet.inter ESet.except ESet.allExcept ESet.bySize
  Val.size? rng cRoot cExt A1 B2 A3 C1 E NE OS

/-- Unfold the semantics at every fuel from `N` on. -/
macro "unfold_sem" N:num : tactic =>
  `(tactic| (refine ⟨$N, fun n hn => ?_⟩; obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hn; subst hk; simp))


/-- Refute at one large fuel. -/
macro "refute_sem" N:num : tactic =>
  `(tactic| (rintro ⟨N, h⟩; have := h (N + $N) (by omega); simp at this))

-- "A1 is extensible, and contains values 1 to 128 with 1 to 32 in the root and 33 to 128 as
-- extension additions."
example : Extensible Es H0 M A1 := by unfold_sem 11
example : InRoot Es H0 M A1 (.int 32) := by unfold_sem 11
example : Has Es H0 M A1 (.int 128) := by unfold_sem 11
example : ¬ InRoot Es H0 M A1 (.int 33) := by refute_sem 11
example : ¬ Has Es H0 M A1 (.int 129) := by refute_sem 11
-- "B2 is not extensible, and contains 1 to 16."
example : ¬ Extensible Es H0 M B2 := by refute_sem 11
example : Has Es H0 M B2 (.int 16) := by unfold_sem 12
example : ¬ Has Es H0 M B2 (.int 17) := by refute_sem 12
-- "MIN is minus infinity and A3 contains 1 to 32"
example : Has Es H0 M A3 (.int 32) := by unfold_sem 11
example : ¬ Has Es H0 M A3 (.int 33) := by refute_sem 11
example : ¬ Has Es H0 M C1 (.int 33) := by refute_sem 16
example : ¬ Extensible Es H0 M C1 := by refute_sem 16
example : InRoot Es H0 M NE (.int 4) := by unfold_sem 18
example : ¬ Extensible Es H0 M NE := by refute_sem 18
-- `SIZE (1..4, ...)` is extensible but has no extension additions: a 7-octet value is not one of its
-- values. It is in its abstract syntax only as a value of an extension-related type (X.680 6).
example : Extensible Es H0 M OS := by unfold_sem 15
example : ¬ Has Es H0 M OS (.octets (List.replicate 7 0)) := by refute_sem 15
example : ¬ InRoot Es H0 M OS (.octets (List.replicate 7 0)) := by refute_sem 15
example : InRoot Es H0 M OS (.octets (List.replicate 4 0)) := by unfold_sem 15
