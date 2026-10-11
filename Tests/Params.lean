import Asn1.X680.Semantics

/-! Parameterized types (X.683) and extensible object sets (X.681 12.9), in the shape 3GPP uses for
protocol IEs. -/

open Asn1.X680

/-- `PROTOCOL-IES ::= CLASS { &id INTEGER (0..65535) UNIQUE, &Value }` -/
def ProtocolIEs : ClassRef := .defn
  [.fixedValue "&id" (.constrained (.integer [])
      (.mk (.elem (.range (.val (.int 0)) false (.val (.int 65535)) false)) false none)) true none,
   .typeField "&Value" none]

def pies : ClassRef := .ref none "PROTOCOL-IES" []

/-- `ProtocolIE-Field {PROTOCOL-IES : IEsSetParam} ::= SEQUENCE {
  id PROTOCOL-IES.&id ({IEsSetParam}), value PROTOCOL-IES.&Value ({IEsSetParam}{@id}) }` -/
def fieldAssign : ParamAssign := .type "ProtocolIE-Field" [⟨some (.cls pies), "IEsSetParam"⟩]
  (.sequence
    [.mk "id" (.constrained (.classField pies ["&id"]) (.table (.ref none "IEsSetParam" []) [])) .mandatory,
     .mk "value" (.constrained (.classField pies ["&Value"])
        (.table (.ref none "IEsSetParam" []) [⟨none, ["id"]⟩])) .mandatory] none [])

/-- `MyIEs PROTOCOL-IES ::= { { ID 1 TYPE INTEGER }, ... }` -/
def MyIEs : ObjSet :=
  .spec (some (.obj (.defn [("&id", .value (.int 1)), ("&Value", .type (.integer []))]))) true none

def M : Module where
  name := "M"
  header := ⟨.automatic, false⟩
  classes := [("PROTOCOL-IES", ProtocolIEs)]
  objectSets := [("MyIEs", pies, MyIEs)]
  params := [fieldAssign]

def H0 : ContentsHook := fun _ _ _ _ _ => True

/-- `ProtocolIE-Field {{MyIEs}}` opens a scope in which `IEsSetParam` stands for `MyIEs`. -/
def callScope : Scope := bindParams M [⟨some (.cls pies), "IEsSetParam"⟩] [.objSet (.ref none "MyIEs" [])]
  (.ofModule M)

example (k : Nat) : resolveTy [M] (k + 5) (.ofModule M) none "ProtocolIE-Field"
    [.objSet (.ref none "MyIEs" [])] = some (callScope, match fieldAssign with
      | .type _ _ b => b | _ => .null) := rfl

-- X.683 8.4: inside it, the dummy reference `IEsSetParam` names MyIEs, read in the caller's scope
example (k : Nat) : resolveObjSet [M] (k + 5) callScope none "IEsSetParam" [] =
    some (.ofModule M, none, .ref none "MyIEs" []) := rfl

def ieFields : List FieldSpec := match ProtocolIEs with | .defn fs _ => fs | _ => []

theorem ies_rows (k : Nat) (o : ObjV) :
    (evalObjSet [M] (k + 10) callScope (some (.ofModule M, ieFields)) (.ref none "IEsSetParam" [])).a o ↔
      o = ⟨.ofModule M, [("&id", .value (.int 1)), ("&Value", .type (.integer []))], .ofModule M, ieFields⟩ := by
  have h1 : resolveObjSet [M] (k + 9) callScope none "IEsSetParam" [] =
      some (.ofModule M, none, .ref none "MyIEs" []) := rfl
  have h2 : resolveObjSet [M] (k + 8) (.ofModule M) none "MyIEs" [] =
      some (.ofModule M, some pies, MyIEs) := rfl
  have h3 : classFields [M] (k + 8) (.ofModule M) pies = some (.ofModule M, ieFields) := rfl
  simp [evalObjSet, h1, h2, h3, MyIEs, OSet.ofSpecs, oelems, evalObj]

theorem ies_ext (k : Nat) :
    (evalObjSet [M] (k + 10) callScope (some (.ofModule M, ieFields)) (.ref none "IEsSetParam" [])).ext = true := by
  have h1 : resolveObjSet [M] (k + 9) callScope none "IEsSetParam" [] =
      some (.ofModule M, none, .ref none "MyIEs" []) := rfl
  have h2 : resolveObjSet [M] (k + 8) (.ofModule M) none "MyIEs" [] =
      some (.ofModule M, some pies, MyIEs) := rfl
  simp [evalObjSet, h1, h2, MyIEs, OSet.ofSpecs]

/-- The enclosing value of `value` in `{ id i, value v }`. -/
def framesFor (i : Int) (v : Val) : List Frame :=
  [⟨.seq, .seq [("id", .int i), ("value", v)],
    [("id", callScope, .constrained (.classField pies ["&id"]) (.table (.ref none "IEsSetParam" []) [])),
     ("value", callScope, .openType)]⟩]

/-- X.681 12.9: MyIEs is extensible, so an IE with id 7, which no object of the set has, may carry
a value of any type. -/
example (k : Nat) : TableOk [M] H0 (k + 30) callScope (framesFor 7 (.open_ .boolean (.bool true)))
    (.ofModule M, ieFields) (evalObjSet [M] (k + 10) callScope (some (.ofModule M, ieFields))
      (.ref none "IEsSetParam" [])) ["&Value"] [⟨none, ["id"]⟩] (.open_ .boolean (.bool true)) := by
  have hr : [(⟨none, ["id"]⟩ : AtRef)].map (fun r => ((r.resolve [M] (k + 29) (framesFor 7 (.open_ .boolean (.bool true)))).bind
      fun (v, rsc, rt) => (classFieldOf [M] (k + 29) rsc rt).map fun (_, _, p) => (v, p))) =
      [some (.int 7, ["&id"])] := rfl
  simp only [TableOk]
  rw [hr, ies_ext]
  refine ⟨by simp, Or.inr ⟨⟨rfl, ?_⟩, ?_⟩⟩
  · intro u hu
    simp [uniqueFields, ieFields, ProtocolIEs] at hu
    subst hu
    change ¬ ∃ row, _
    rintro ⟨row, hrow, sc', st, hcell, hadm⟩
    rw [ies_rows] at hrow
    subst hrow
    simp +decide [cell, ObjV.setting] at hcell
    obtain ⟨rfl, rfl⟩ := hcell
    simp +decide [fieldAt, ieFields, ProtocolIEs, evalVal, eqv] at hadm
  · simp +decide [sem, classFields, fieldAt, VSet.plain]
    refine ⟨_, _, rfl, .ofModule M, ?_⟩
    simp [sem, VSet.plain]
