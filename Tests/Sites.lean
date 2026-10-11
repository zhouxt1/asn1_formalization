import Asn1.X680.Checker

/-! Where `Module.ValidAt` applies its rules (`Module.Site`, `ParamAssign.Has`), and how it reads a
parameterized body (X.683 8.5): with its dummies standing for actual parameters. -/

open Asn1.X680

def H0 : ContentsHook := fun _ _ _ _ _ => True

def tParam : List Param := [⟨none, "T"⟩]

/-- `Seq {T} ::= SEQUENCE { a T }` -/
def seqAssign : ParamAssign := .type "Seq" tParam (.sequence [.mk "a" (.ref "T") .mandatory] none [])

/-- `C ::= CLASS { &id INTEGER UNIQUE, &Type }`, `Objs C ::= { { &id 1, &Type BOOLEAN } }`,
`v BOOLEAN ::= TRUE` -/
def cls : ClassRef := .defn [.fixedValue "&id" (.integer []) true none, .typeField "&Type" none]

def obj1 : Obj := .defn [("&id", .value (.int 1)), ("&Type", .type .boolean)]

def M : Module where
  name := "M"
  header := ⟨.automatic, false⟩
  values := [("v", .boolean, .bool true)]
  classes := [("C", cls)]
  objectSets := [("Objs", .ref none "C" [], .spec (some (.obj obj1)) false none)]
  params := [seqAssign]

-- the types of value governors, class fields and object settings are sites
example : M.Site "v" .boolean := .valueGov (v := .bool true) (by simp [M])
example : M.Site "C" (.integer []) := .classDef (c := cls) (by simp [M]) (by simp [classTypes, cls])
example : M.Site "Objs" .boolean :=
  .objectSet (cls := .ref none "C" []) (os := .spec (some (.obj obj1)) false none) (by simp [M])
    (.root (.obj (.type (f := "&Type") (by simp [obj1]))))

-- a type written as an actual parameter occurs in the reference
example : Occurs (.paramRef none "Seq" [.type .boolean]) .boolean := .paramArg (by simp) (.self _)

-- with `T` standing for INTEGER, the reference `T` in the body resolves (X.683 8.5, 9.7) ...
example (k : Nat) : RefsOk [M] H0 (k + 2) (bindParams M tParam [.type (.integer [])] (.ofModule M))
    (.ref "T") := by simp [RefsOk]; rfl

-- ... and a type is an actual parameter `T` can stand for
example (k : Nat) : ArgFits [M] H0 k (.ofModule M) none (.type (.integer [])) := trivial

-- bound to nothing, as the checker reads a body, it does not: the spec needs the actual parameters
example (k : Nat) : ¬ RefsOk [M] H0 (k + 2) (Scope.withDummies M tParam) (.ref "T") := by
  simp [RefsOk]; rfl

-- X.683 8.4: a dummy reference is not itself parameterized
example (k : Nat) : ¬ RefsOk [M] H0 (k + 2) (bindParams M tParam [.type (.integer [])] (.ofModule M))
    (.paramRef none "T" [.type .boolean]) := by
  simp [RefsOk, bindParams, Scope.bound, Scope.binds, tParam]

/-! Rules added from the checker (SPEC-GAP.md section 2, 3) -/

-- 31.2.5
example : ¬ UniversalTagOk (.tagged ⟨.universal, 3⟩ .explicit .boolean) := by simp [UniversalTagOk]

-- 13.7, 13.10: two modules named M, told apart by their definitive identifiers, or not
example : ModuleNamesOk [{ M with oid := some [1, 2, 3] }, { M with oid := some [1, 2, 4] }] := by
  simp [ModuleNamesOk]
example : ¬ ModuleNamesOk [M, M] := by simp [ModuleNamesOk, M]

-- X.681 10.9: WITH SYNTAX that leaves out the field &Type
example : ¬ ClassSyntaxOk (.defn [.fixedValue "&id" (.integer []) true none, .typeField "&Type" none]
    (some [.literal "ID", .field "&id"])) := by
  rintro ⟨-, h, -⟩
  have := (h _ _ rfl).2 "&Type" (by simp [FieldSpec.name])
  simp [synFields] at this

-- X.681 9.6: UNIQUE with DEFAULT
example : ¬ ClassSyntaxOk (.defn [.fixedValue "&id" (.integer []) true (some (some (.int 1)))] none) := by
  rintro ⟨h, -, -⟩
  exact h _ none rfl "&id" (.integer []) (some (.int 1)) (by simp)
