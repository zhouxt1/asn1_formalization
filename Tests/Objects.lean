import Asn1.X680.Semantics

/-! Information objects and table constraints, checked against X.682 clause 10's own example. -/

open Asn1.X680

/-- `"A"` and so on, as abstract character strings. -/
def str (s : String) : Val := .chars (s.toList.map Char.toNat)

/-- `ERROR-CLASS ::= CLASS { &category PrintableString (SIZE(1)), &code INTEGER, &Type }` -/
def ErrorClass : ClassRef := .defn
  [.fixedValue "&category" (.constrained (.restricted .printable)
      (.mk (.elem (.size (.mk (.elem (.single (.int 1))) false none))) false none)) false none,
   .fixedValue "&code" (.integer []) false none,
   .typeField "&Type" none]

def row (c : String) (k : Int) (t : Ty) : Obj :=
  .defn [("&category", .value (str c)), ("&code", .value (.int k)), ("&Type", .type t)]

/-- `ErrorSet ERROR-CLASS ::= { {"A" 1 INTEGER} | {"A" 2 REAL} | {"B" 1 CHARACTER STRING} |
{"B" 2 GeneralString} }` -/
def ErrorSet : ObjSet := .spec (some (.union (.union (.obj (row "A" 1 (.integer [])))
    (.obj (row "A" 2 .real))) (.union (.obj (row "B" 1 .characterString))
    (.obj (row "B" 2 (.restricted .general)))))) false none

/-- `ErrorReturn ::= SEQUENCE { errorCategory ERROR-CLASS.&category ({ErrorSet}) OPTIONAL,
errors SEQUENCE OF SEQUENCE { errorCode ERROR-CLASS.&code ({ErrorSet}{@errorCategory}),
errorInfo ERROR-CLASS.&Type ({ErrorSet}{@errorCategory,@.errorCode}) } OPTIONAL }` -/
def ErrorReturn : Ty := .sequence
  [.mk "errorCategory" (.constrained (.classField (.ref none "ERROR-CLASS" []) ["&category"])
      (.table (.ref none "ErrorSet" []) [])) .optional,
   .mk "errors" (.sequenceOf (.sequence
      [.mk "errorCode" (.constrained (.classField (.ref none "ERROR-CLASS" []) ["&code"])
          (.table (.ref none "ErrorSet" []) [⟨none, ["errorCategory"]⟩])) .mandatory,
       .mk "errorInfo" (.constrained (.classField (.ref none "ERROR-CLASS" []) ["&Type"])
          (.table (.ref none "ErrorSet" []) [⟨none, ["errorCategory"]⟩, ⟨some 0, ["errorCode"]⟩]))
          .mandatory] none [])) .optional] none []

def M : Module where
  name := "M"
  header := ⟨.explicit, false⟩
  classes := [("ERROR-CLASS", ErrorClass)]
  objectSets := [("ErrorSet", .ref none "ERROR-CLASS" [], ErrorSet)]
  types := [("ErrorReturn", ErrorReturn)]

def H0 : ContentsHook := fun _ _ _ _ _ => True

def err (cat : Option String) (es : List (Int × Val)) : Val :=
  .seq ((cat.map fun c => [("errorCategory", str c)]).getD [] ++
    [("errors", .seqOf (es.map fun (k, info) => .seq [("errorCode", .int k), ("errorInfo", info)]))])

-- AtNotation: `@errorCategory` reaches the outermost SEQUENCE, `@.errorCode` the innermost one
def innerV : Val := .seq [("errorCode", .int 1), ("errorInfo", .open_ (.integer []) (.int 7))]
def outerV : Val := err (some "A") [(1, .open_ (.integer []) (.int 7))]
def frames : List Frame :=
  [⟨.seq, innerV, [("errorCode", .ofModule M, .integer []), ("errorInfo", .ofModule M, .openType)]⟩,
   ⟨.seqOf, .seqOf [innerV], []⟩,
   ⟨.seq, outerV, [("errorCategory", .ofModule M, .restricted .printable), ("errors", .ofModule M, .null)]⟩]

example : ((⟨none, ["errorCategory"]⟩ : AtRef).resolve [M] 5 frames).map (·.1) = some (str "A") := rfl

example : ((⟨some 0, ["errorCode"]⟩ : AtRef).resolve [M] 5 frames).map (·.1) = some (.int 1) := rfl

-- resolving the object set and its class
example : resolveObjSet [M] 5 (.ofModule M) none "ErrorSet" [] =
    some (.ofModule M, some (.ref none "ERROR-CLASS" []), ErrorSet) := rfl
example : (classFields [M] 5 (.ofModule M) (.ref none "ERROR-CLASS" [])).map (·.2) = some
    [.fixedValue "&category" (.constrained (.restricted .printable)
      (.mk (.elem (.size (.mk (.elem (.single (.int 1))) false none))) false none)) false none,
     .fixedValue "&code" (.integer []) false none, .typeField "&Type" none] := rfl

def ecFields : List FieldSpec :=
  [.fixedValue "&category" (.constrained (.restricted .printable)
      (.mk (.elem (.size (.mk (.elem (.single (.int 1))) false none))) false none)) false none,
   .fixedValue "&code" (.integer []) false none, .typeField "&Type" none]

-- the object set has the row {"A" 1 INTEGER}
example (k : Nat) : (evalObjSet [M] (k + 10) (.ofModule M) none (.ref none "ErrorSet" [])).a
    ⟨.ofModule M, [("&category", .value (str "A")), ("&code", .value (.int 1)),
      ("&Type", .type (.integer []))], .ofModule M, ecFields⟩ := by
  have hr : resolveObjSet [M] (k + 9) (.ofModule M) none "ErrorSet" [] =
      some (.ofModule M, some (.ref none "ERROR-CLASS" []), ErrorSet) := rfl
  have hc : classFields [M] (k + 9) (.ofModule M) (.ref none "ERROR-CLASS" []) =
      some (.ofModule M, ecFields) := rfl
  simp [evalObjSet, hr, hc, ErrorSet, OSet.ofSpecs, oelems, OSet.union, evalObj, row]

/-! ### The table constraint on `errorInfo` (X.682 10.19–10.20) -/

def ecRef : ClassRef := .ref none "ERROR-CLASS" []
def setRef : ObjSet := .ref none "ErrorSet" []
def catTy : Ty := .constrained (.classField ecRef ["&category"]) (.table setRef [])
def codeTy : Ty := .constrained (.classField ecRef ["&code"]) (.table setRef [⟨none, ["errorCategory"]⟩])
def infoRefs : List AtRef := [⟨none, ["errorCategory"]⟩, ⟨some 0, ["errorCode"]⟩]

/-- The enclosing values of `errorInfo` inside `err (some c) [(k, info)]`: the inner SEQUENCE, the
SEQUENCE OF, ErrorReturn. -/
def framesFor (c : Option String) (k : Int) (info : Val) : List Frame :=
  let inn : Val := .seq [("errorCode", .int k), ("errorInfo", info)]
  [⟨.seq, inn, [("errorCode", .ofModule M, codeTy), ("errorInfo", .ofModule M, .openType)]⟩,
   ⟨.seqOf, .seqOf [inn], []⟩,
   ⟨.seq, err c [(k, info)], [("errorCategory", .ofModule M, catTy), ("errors", .ofModule M, .null)]⟩]

/-- The rows of ErrorSet, as evaluated objects. -/
def rowV (c : String) (k : Int) (t : Ty) : ObjV :=
  ⟨.ofModule M, [("&category", .value (str c)), ("&code", .value (.int k)), ("&Type", .type t)],
    .ofModule M, ecFields⟩

theorem rows_a (k : Nat) (o : ObjV) :
    (evalObjSet [M] (k + 10) (.ofModule M) (some (.ofModule M, ecFields)) ErrorSet).a o ↔
      o = rowV "A" 1 (.integer []) ∨ o = rowV "A" 2 .real ∨ o = rowV "B" 1 .characterString ∨
        o = rowV "B" 2 (.restricted .general) := by
  simp [evalObjSet, ErrorSet, OSet.ofSpecs, oelems, OSet.union, evalObj, row, rowV]
  tauto

-- the referenced components, resolved with their fields
theorem refd_for (k : Nat) (c : String) (code : Int) (info : Val) :
    infoRefs.map (fun r => ((r.resolve [M] (k + 20) (framesFor (some c) code info)).bind
      fun (v, rsc, rt) => (classFieldOf [M] (k + 20) rsc rt).map fun (_, _, p) => (v, p))) =
    [some (str c, ["&category"]), some (.int code, ["&code"])] := by
  rfl

theorem rows_ext (k : Nat) :
    (evalObjSet [M] (k + 11) (.ofModule M) (some (.ofModule M, ecFields)) ErrorSet).ext = false := by
  simp [evalObjSet, ErrorSet, OSet.ofSpecs, oelems, OSet.union]

def info1 : Val := .open_ (.integer []) (.int 7)
def infoR : Val := .open_ .real (.real .plusZero)

/-- `{ errorCategory "A", errors { { errorCode 1, errorInfo INTEGER: 7 } } }` satisfies the
component relation constraint on `errorInfo`: the row {"A" 1 INTEGER} is selected. -/
example (k : Nat) : TableOk [M] H0 (k + 30) (.ofModule M) (framesFor (some "A") 1 info1)
    (.ofModule M, ecFields) (evalObjSet [M] (k + 11) (.ofModule M) (some (.ofModule M, ecFields)) ErrorSet)
    ["&Type"] infoRefs info1 := by
  have hr := refd_for (k + 9) "A" 1 info1
  simp only [show k + 9 + 20 = k + 29 by omega] at hr
  have hrow := (rows_a (k + 1) (rowV "A" 1 (.integer []))).2 (Or.inl rfl)
  simp only [show k + 1 + 10 = k + 11 by omega] at hrow
  simp only [TableOk]
  rw [hr]
  refine ⟨by simp, Or.inl ⟨_, hrow, ?_, ?_⟩⟩
  · simp +decide [cell, rowV, ObjV.setting, fieldAt, ecFields, evalVal, eqv, str]
  · simp +decide [cell, rowV, ObjV.setting, fieldAt, ecFields, sem, info1, VSet.plain]

/-- `errorInfo REAL: 0` with category "A" and code 1 does not: that row's type is INTEGER, and
ErrorSet is not extensible (X.681 12.8). -/
example (k : Nat) : ¬ TableOk [M] H0 (k + 30) (.ofModule M) (framesFor (some "A") 1 infoR)
    (.ofModule M, ecFields) (evalObjSet [M] (k + 11) (.ofModule M) (some (.ofModule M, ecFields)) ErrorSet)
    ["&Type"] infoRefs infoR := by
  have hr := refd_for (k + 9) "A" 1 infoR
  simp only [show k + 9 + 20 = k + 29 by omega] at hr
  simp only [TableOk]
  rw [hr, rows_ext]
  rintro ⟨-, ⟨row, hrow, hsel, hadm⟩ | ⟨h, -⟩⟩
  · rw [show k + 11 = k + 1 + 10 by omega, rows_a] at hrow
    rcases hrow with rfl | rfl | rfl | rfl <;>
      simp +decide [cell, rowV, ObjV.setting, fieldAt, ecFields, evalVal, eqv, str, infoR] at hsel hadm
  · simp at h

/-- X.682 10.18: with `errorCategory` absent, `errorInfo` fails its constraint. -/
example (k : Nat) : ¬ TableOk [M] H0 (k + 30) (.ofModule M) (framesFor none 1 info1)
    (.ofModule M, ecFields) (evalObjSet [M] (k + 11) (.ofModule M) (some (.ofModule M, ecFields)) ErrorSet)
    ["&Type"] infoRefs info1 := by
  have hr : infoRefs.map (fun r => ((r.resolve [M] (k + 29) (framesFor none 1 info1)).bind
      fun (v, rsc, rt) => (classFieldOf [M] (k + 29) rsc rt).map fun (_, _, p) => (v, p))) =
      [none, some (.int 1, ["&code"])] := rfl
  simp only [TableOk]
  rw [hr]
  simp
