import Asn1.X680.Validity

/-! The extension marker (X.680 52): extensibility under constraints, and the conceptually-added
element's tag. -/

open Asn1.X680

def M : Module := { name := "M", header := ⟨.explicit, false⟩ }
def H0 : ContentsHook := fun _ _ _ _ _ => True
def sc : Scope := .ofModule M

/-! ## 52.8: the conceptually-added element of a nested CHOICE

With `A`, `C`, `D` and `E` as INTEGER, BOOLEAN, NULL and REAL (four distinct tags). -/

def ext1 (alts : List Alt) : Ty := .choice alts (some [])

/-- 52.8.1: `SET { a A, b CHOICE { c C, d D, ... } }` is legal. -/
def ex1 : Ty := .set [.mk "a" (.integer []) .mandatory,
                      .mk "b" (ext1 [.mk "c" .boolean, .mk "d" .null]) .mandatory] none []

/-- 52.8.2: `SET { a A, b CHOICE { c C, d D, ... }, ..., d D }` is illegal: added material may be
part of b, or at the outer level. -/
def ex2 : Ty := .set [.mk "a" (.integer []) .mandatory,
                      .mk "b" (ext1 [.mk "c" .boolean, .mk "d" .null]) .mandatory] (some [])
                     [.mk "d" .null .mandatory]

/-- 52.8.3: `SET { a A, b CHOICE { c C, ... }, d CHOICE { e E, ... } }` is illegal: added material
may be part of b or d. -/
def ex3 : Ty := .set [.mk "a" (.integer []) .mandatory,
                      .mk "b" (ext1 [.mk "c" .boolean]) .mandatory,
                      .mk "d" (ext1 [.mk "e" .real]) .mandatory] none []

example : TagsOk [M] H0 8 sc ex1 := by
  simp only [TagsOk, ex1, TagsDistinct]; decide +kernel

example : ¬ TagsOk [M] H0 8 sc ex2 := by
  simp only [TagsOk, ex2, TagsDistinct]; decide +kernel

example : ¬ TagsOk [M] H0 8 sc ex3 := by
  simp only [TagsOk, ex3, TagsDistinct]; decide +kernel

/-- In an AUTOMATIC TAGS module, each component is tagged, so ex3 is legal there. -/
def MA : Module := { name := "MA", header := ⟨.automatic, false⟩ }

example : TagsOk [MA] H0 8 (.ofModule MA) ex3 := by
  simp only [TagsOk, ex3, TagsDistinct]; decide +kernel

/-! ## X.681 14.2 b): an open type's tag is indeterminate -/

def openCls : ClassRef := .defn [.typeField "&T" none]

/-- `CHOICE { a C.&T, b INTEGER }`: the open type's tag is not distinct from INTEGER's. -/
example : ¬ TagsOk [M] H0 8 sc (.choice [.mk "a" (.classField openCls ["&T"]), .mk "b" (.integer [])] none) := by
  simp only [TagsOk, TagsDistinct]; decide +kernel

/-! ## 52.6: inner subtyping keeps the type's extensibility

`A ::= SEQUENCE { a INTEGER, b BOOLEAN OPTIONAL, ... }`, `B ::= A (WITH COMPONENTS {b ABSENT})`:
"B is extensible". -/

def A : Ty := .sequence [.mk "a" (.integer []) .mandatory, .mk "b" .boolean .optional] (some []) []
def B : Ty := .constrained A (.mk (.elem (.withComponents true [("b", none, .absent)])) false none)

example (k : Nat) : (sem [M] H0 (k + 3) sc [] B).ext = true := by
  simp [sem, cons, VSet.keepExt, structExt, builtin, B, A]

/-- 52.5: a constraint's own extensibility is not inherited: `A' ::= INTEGER (0..10, ...)`,
`B' ::= A' (2..5)` is inextensible. -/
def A' : Ty := .constrained (.integer []) (.mk (.elem (.range (.val (.int 0)) false (.val (.int 10)) false)) true none)
def B' : Ty := .constrained A' (.mk (.elem (.range (.val (.int 2)) false (.val (.int 5)) false)) false none)

example (k : Nat) : (sem [M] H0 (k + 6) sc [] B').ext = false := by
  simp [sem, cons, VSet.keepExt, VSet.ofSpecs, structExt, builtin, B', A', eset, elem, ESet.fixed]
