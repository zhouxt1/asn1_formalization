import Asn1.X680.Syntax
import Asn1.X680.Pattern

/-!
# The values of a type (X.680 6, 20–48, 49–52)

A type denotes three things, all needed by X.680 itself:
- its **root** values;
- **all** its values, root values and extension additions together;
- whether it is **extensible** (3.8.41, 50.4).

Constraints are applied to the root of their parent (50.7, 50.8, 50.11, 51.3.2), and set arithmetic
is done twice (50.5): once over root values only, and once over root values with their extension
additions. Annex I.4.3.8 tabulates the outcome, and `Tests/Constraints.lean` checks it.

## Why there is fuel

References make types recursive, and `EXCEPT` makes the definition of a value set non-monotone,
so it cannot be an inductive predicate. Every definition here takes a natural number, the fuel, and
recurses structurally on it. The value set of a type is then what holds for *every large enough*
fuel (`Eventually`).
- For a module whose references are well-founded (every cycle passes through a component or an
  element type, as X.680 requires of a module with finite values), each question stabilizes once
  the fuel exceeds the depth of the value times the size of the module.
- For a circular definition such as `T ::= INTEGER (ALL EXCEPT T)`, membership may never stabilize,
  and `Has` is then false.

## Values as written, and their equality

A `Val` records components exactly as written: a DEFAULT component may be present or absent, and a
SET OF value keeps an order. `Equiv` is the equality of abstract values:
- omitting a DEFAULT component is "exactly equivalent" to inserting its value (25.12);
- SET OF values are unordered (28);
- for a bit string with named bits, trailing 0 bits are not significant (22.7).
-/

namespace Asn1.X680


/-- Where the associated types (36.5, 37.5, 44.5) and the built-in classes (X.681 Annexes A, B) are
interpreted: they are defined by X.680, not written in any
module, so no module's EXTENSIBILITY IMPLIED applies to them, and their tags are automatic. -/
def assocModule : Module := { name := "", header := ⟨.automatic, false⟩ }

/-! ## Scopes (X.683 8.4)

A notation is read in a scope:
- the module it is written in;
- if it is inside a parameterized assignment, the actual parameters bound to that assignment's dummy
  references, each with the scope the actual parameter was written in.

A dummy reference hides every other reference with its name (X.683 8.4). Binding parameters this
way, rather than substituting them into the text, gives the same meaning, and keeps recursive
parameterized types finite. -/

inductive Scope where
  | mk (mod : Module) (binds : List (String × Arg × Option ParamGov × Scope))

def Scope.mod : Scope → Module | .mk m _ => m
def Scope.binds : Scope → List (String × Arg × Option ParamGov × Scope) | .mk _ b => b
def Scope.ofModule (m : Module) : Scope := .mk m []

/-- X.683 8.4: the actual parameter a dummy reference stands for, if `name` is one. -/
def Scope.bound (sc : Scope) (name : String) : Option (Arg × Option ParamGov × Scope) :=
  (sc.binds.find? (·.1 == name)).map (·.2)

/-- X.683 9.2, 9.5: a parameterized reference opens a scope in the module of its assignment, with
the dummy references bound to the actual parameters, in the caller's scope. -/
def bindParams (m : Module) (ps : List Param) (args : List Arg) (caller : Scope) : Scope :=
  .mk m ((ps.zip args).map fun (p, a) => (p.name, a, p.governor, caller))

/-! ## References -/

/-- How a reference (`moduleName.name {args}`, any part absent) is resolved in a scope, for one
kind of thing: first as a dummy reference (X.683 8.4), then as an assignment of the module or one
it imports (X.680 13.16, 13.19, 14.6), then as a parameterized assignment (X.683 9.3). -/
def resolveIn {α : Type} (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg)
    (fromArg : Arg → Option ParamGov → Scope → Option (Scope × α))
    (fromModule : Module → Option α)
    (fromParam : ParamAssign → Option (List Param × α)) : Option (Scope × α) :=
  let viaModule : Option (Module × α) := match mn with
    | some mn => E.resolveExtWith fromModule name n sc.mod mn
    | none => E.resolveWith fromModule name n sc.mod
  let getParam (m : Module) : Option (List Param × α) := (m.params.find? (·.name == name)).bind fromParam
  let viaParam : Option (Module × List Param × α) := match mn with
    | some mn => E.resolveExtWith getParam name n sc.mod mn
    | none => E.resolveWith getParam name n sc.mod
  match mn, args, sc.bound name with
  | none, [], some (a, g, sc') => fromArg a g sc'
  | _, [], _ => viaModule.map fun (m, x) => (Scope.ofModule m, x)
  | _, _, _ => viaParam.map fun (m, ps, x) => (bindParams m ps args sc, x)

/-- A type reference. A dummy that stands for a value set is a type (X.680 16.8): its governor,
constrained by the value set. -/
def resolveTy (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg) : Option (Scope × Ty) :=
  resolveIn E n sc mn name args
    (fun a g sc' => match a, g with
      | .type t, _ => some (sc', t)
      | .valueSet c, some (.type gt) => some (sc', .constrained gt c)
      | _, _ => none)
    (·.lookup name)
    (fun | .type _ ps body => some (ps, body)
         | .valueSet _ ps t c => some (ps, .constrained t c)
         | _ => none)

/-- A class reference (X.681 9.2). -/
def resolveClass (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg) : Option (Scope × ClassRef) :=
  resolveIn E n sc mn name args
    (fun a _ sc' => match a with | .cls c => some (sc', c) | _ => none)
    (fun m => (m.classes.find? (·.1 == name)).map (·.2))
    (fun | .cls _ ps c => some (ps, c) | _ => none)

/-- An object reference (X.681 11.3), with the object's class when an assignment says it. -/
def resolveObj (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg) : Option (Scope × Option ClassRef × Obj) :=
  resolveIn E n sc mn name args
    (fun a _ sc' => match a with | .obj o => some (sc', none, o) | _ => none)
    (fun m => (m.objects.find? (·.1 == name)).map fun (_, c, o) => (some c, o))
    (fun | .obj _ ps c o => some (ps, some c, o) | _ => none)

/-- An object set reference (X.681 12.3). -/
def resolveObjSet (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg) : Option (Scope × Option ClassRef × ObjSet) :=
  resolveIn E n sc mn name args
    (fun a _ sc' => match a with | .objSet s => some (sc', none, s) | _ => none)
    (fun m => (m.objectSets.find? (·.1 == name)).map fun (_, c, s) => (some c, s))
    (fun | .objSet _ ps c s => some (ps, some c, s) | _ => none)

/-- A value reference (X.680 14.1, 16.2), with its governing type when an assignment says it. -/
def resolveVal (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg) : Option (Scope × Val) :=
  resolveIn E n sc mn name args
    (fun a _ sc' => match a with | .value v => some (sc', v) | _ => none)
    (fun m => (m.values.find? (·.1 == name)).map (·.2.2))
    (fun | .value _ ps _ v => some (ps, v) | _ => none)

/-! ## Classes (X.681 9) -/

def FieldSpec.name : FieldSpec → String
  | .typeField n _ | .fixedValue n _ _ _ | .varValue n _ _ | .fixedValueSet n _ _
  | .varValueSet n _ _ | .objectField n _ _ | .objectSetField n _ _ => n

/-- X.681 Annex A.2: TYPE-IDENTIFIER ::= CLASS { &id OBJECT IDENTIFIER UNIQUE, &Type } -/
def typeIdentifierFields : List FieldSpec :=
  [.fixedValue "&id" .objectIdentifier true none, .typeField "&Type" none]

/-- X.681 Annex B.2: ABSTRACT-SYNTAX ::= CLASS { &id OBJECT IDENTIFIER UNIQUE, &Type,
&property BIT STRING {handles-invalid-encodings(0)} DEFAULT {} } -/
def abstractSyntaxFields : List FieldSpec :=
  [.fixedValue "&id" .objectIdentifier true none, .typeField "&Type" none,
   .fixedValue "&property" (.bitString [("handles-invalid-encodings", 0)]) false (some (some (.bits [])))]

/-- The field specifications of a class (X.681 9.2, 9.3), with the scope they are written in. -/
def classFields (E : Env) : Nat → Scope → ClassRef → Option (Scope × List FieldSpec)
  | 0, _, _ => none
  | _ + 1, sc, .defn fs _ => some (sc, fs)
  | _ + 1, _, .typeIdentifier => some (Scope.ofModule assocModule, typeIdentifierFields)
  | _ + 1, _, .abstractSyntax => some (Scope.ofModule assocModule, abstractSyntaxFields)
  | n + 1, sc, .ref mn name args => match resolveClass E n sc mn name args with
    | some (sc', c) => classFields E n sc' c
    | none => none

/-- X.681 9.14 "FieldName": the field specification a path of field names reaches, following the
classes of object and object set fields. -/
def fieldAt (E : Env) : Nat → Scope × List FieldSpec → List String → Option (Scope × FieldSpec)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, (sc, fs), [f] => (fs.find? (·.name == f)).map (sc, ·)
  | n + 1, (sc, fs), f :: rest =>
    match fs.find? (·.name == f) with
    | some (.objectField _ c _) | some (.objectSetField _ c _) =>
      (classFields E n sc c).bind fun cf => fieldAt E n cf rest
    | _ => none

/-- An information object, evaluated: its settings with the scope they are written in, and its
class (X.681 11). Object and object set settings stay as notation, evaluated when a path goes
through them. -/
structure ObjV where
  sc : Scope
  settings : List (String × Setting)
  clsSc : Scope
  fields : List FieldSpec

/-- X.681 9.5–9.12, 11.5: a field's setting, or the class's DEFAULT for it if it is omitted. -/
def ObjV.setting (o : ObjV) (f : String) : Option (Scope × Setting) :=
  match o.settings.find? (·.1 == f) with
  | some (_, s) => some (o.sc, s)
  | none => match o.fields.find? (·.name == f) with
    | some (.typeField _ (some (some t))) => some (o.clsSc, .type t)
    | some (.fixedValue _ _ _ (some (some v))) | some (.varValue _ _ (some (some v))) =>
      some (o.clsSc, .value v)
    | some (.fixedValueSet _ _ (some (some c))) | some (.varValueSet _ _ (some (some c))) =>
      some (o.clsSc, .valueSet c)
    | some (.objectField _ _ (some (some ob))) => some (o.clsSc, .object ob)
    | some (.objectSetField _ _ (some (some s))) => some (o.clsSc, .objectSet s)
    | _ => none

/-- An information object set during set arithmetic, as `ESet` is for values: root objects, root
and additional objects, extensibility (X.681 12.4, 12.5; X.680 50). -/
structure OSet where
  r : ObjV → Prop
  a : ObjV → Prop
  ext : Bool

def OSet.empty : OSet := ⟨fun _ => False, fun _ => False, false⟩
def OSet.union (A B : OSet) : OSet :=
  ⟨fun v => A.r v ∨ B.r v, fun v => A.r v ∨ B.r v ∨ A.a v ∨ B.a v, A.ext || B.ext⟩
def OSet.inter (A B : OSet) : OSet :=
  ⟨fun v => A.r v ∧ B.r v, fun v => (A.r v ∧ B.r v) ∨ (A.a v ∧ B.a v), A.ext || B.ext⟩
def OSet.except (A B : OSet) : OSet :=
  ⟨fun v => A.r v ∧ ¬ B.r v, fun v => (A.r v ∧ ¬ B.r v) ∨ (A.a v ∧ ¬ B.a v), A.ext⟩
/-- X.681 12.3: an object set from its root, an ellipsis, and its additions. -/
def OSet.ofSpecs (extensible : Bool) (r : Option OSet) (x : Option OSet) : OSet :=
  let r := r.getD .empty
  ⟨r.r, fun v => r.a v ∨ ∃ e, x = some e ∧ e.a v, extensible || r.ext⟩

/-! ## Contents constraints (X.682 11.4, 11.6)

The values of `OCTET STRING (CONTAINING T)` are the encodings of `T`'s values "produced by the
encoding rules that are applied to the octet string". So the value sets of X.680 depend on which
encoding rules are in use. The semantics takes them as a parameter: given the contained type (in
its scope), the encoding rules named by ENCODED BY (if any), and the contained type's values, which
octet or bit string values are encodings of them. Each encoding rules specification instantiates
it with itself. -/
abbrev ContentsHook := Scope → Option Ty → Option Val → (Val → Prop) → Val → Prop


/-! ## Following a type down to its built-in type -/

def Alt.name : Alt → String | .mk n _ => n
def Alt.ty : Alt → Ty | .mk _ t => t
def AltAdd.alts : AltAdd → List Alt | .one a => [a] | .group _ as => as

/-- X.680 29.1: the root alternatives, then the extension addition alternatives, in order. -/
def choiceAlts (root : List Alt) (ext : Option (List AltAdd)) : List Alt :=
  root ++ (ext.getD []).flatMap AltAdd.alts

/-- The alternative of a CHOICE with a given name. -/
def findAlt (alts : List Alt) (nm : String) : Option Alt := alts.find? (·.name == nm)

/-- The class of an object set (or object) that is a reference to an assignment, which names its
class (X.681 11.1, 12.1), with the scope that class is read in. -/
def objSetClass (E : Env) (n : Nat) (sc : Scope) : ObjSet → Option (Scope × ClassRef)
  | .ref mn name args => match resolveObjSet E n sc mn name args with
    | some (sc', some c, _) => some (sc', c)
    | _ => none
  | .spec (some (.obj (.ref mn name args))) false none => match resolveObj E n sc mn name args with
    | some (sc', some c, _) => some (sc', c)
    | _ => none
  | _ => none

/-- X.681 Annex C.7: INSTANCE OF a class is `SEQUENCE { type-id C.&id, value [0] C.&Type }`, in an
environment of EXPLICIT TAGS (C.6). -/
def instanceOfTy (cls : ClassRef) : Ty :=
  .sequence [.mk "type-id" (.classField cls ["&id"]) .mandatory,
             .mk "value" (.tagged ⟨.context, 0⟩ .explicit (.classField cls ["&Type"])) .mandatory]
    none []

/-- X.682 A.2: INSTANCE OF a class constrained by a simple table constraint with object set `os`
is `SEQUENCE { type-id C.&id ({os}), value [0] C.&Type ({os}{@.type-id}) }`. -/
def instanceOfTable (cls : ClassRef) (os : ObjSet) : Ty :=
  .sequence [.mk "type-id" (.constrained (.classField cls ["&id"]) (.table os [])) .mandatory,
             .mk "value" (.tagged ⟨.context, 0⟩ .explicit
               (.constrained (.classField cls ["&Type"]) (.table os [⟨some 0, ["type-id"]⟩]))) .mandatory]
    none []

/-- A class reference written in scope `isc`, as it is read from scope `sc`: a reference to a
class assigned in another module becomes an external reference to it. -/
def ClassRef.from (isc sc : Scope) : ClassRef → ClassRef
  | .ref none name args =>
    if isc.mod.name ≠ sc.mod.name ∧ (isc.bound name).isNone then .ref (some isc.mod.name) name args
    else .ref none name args
  | c => c

/-- The built-in type a type notation denotes, after following references (X.680 13.19, 14.1,
14.6; X.683 9), tags (31), constraints (49), selections (30), INSTANCE OF (X.681 Annex C) and
fixed-type fields of classes (X.681 14.3), with the scope it is written in. A type field of a class
(14.2, 14.4) is an open type. -/
def builtin (E : Env) : Nat → Scope → Ty → Option (Scope × Ty)
  | 0, _, _ => none
  | n + 1, sc, .ref name => (resolveTy E n sc none name []).bind fun (sc', t) => builtin E n sc' t
  | n + 1, sc, .extRef mn name =>
    (resolveTy E n sc (some mn) name []).bind fun (sc', t) => builtin E n sc' t
  | n + 1, sc, .paramRef mn name args =>
    (resolveTy E n sc mn name args).bind fun (sc', t) => builtin E n sc' t
  | n + 1, sc, .tagged _ _ t => builtin E n sc t
  | n + 1, sc, .constrained t _ => builtin E n sc t
  | n + 1, sc, .selection nm t =>
    match builtin E n sc t with
    | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
      | some a => builtin E n sc' a.ty
      | none => none
    | _ => none
  | n + 1, sc, .classField cls path =>
    match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
    | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => builtin E n sc' t
    | some (_, .typeField _ _) | some (_, .varValue _ _ _) | some (_, .varValueSet _ _ _) =>
      some (sc, .openType)
    | _ => none
  | n + 1, sc, .instanceOf cls => builtin E n sc (instanceOfTy cls)
  -- X.681 15.7, 15.8: a value set from objects is the fixed-type field's type, constrained
  | n + 1, sc, .fromObjects src path => match objSetClass E n sc src with
    | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => builtin E n sc' t
      | _ => none
    | none => none
  | _ + 1, sc, t => some (sc, t)

/-- The class and field path an "ObjectClassFieldType" names (X.681 14.1), through references,
tags and constraints. -/
def classFieldOf (E : Env) : Nat → Scope → Ty → Option (Scope × ClassRef × List String)
  | 0, _, _ => none
  | _ + 1, sc, .classField cls path => some (sc, cls, path)
  | n + 1, sc, .ref name => (resolveTy E n sc none name []).bind fun (sc', t) => classFieldOf E n sc' t
  | n + 1, sc, .extRef mn name =>
    (resolveTy E n sc (some mn) name []).bind fun (sc', t) => classFieldOf E n sc' t
  | n + 1, sc, .paramRef mn name args =>
    (resolveTy E n sc mn name args).bind fun (sc', t) => classFieldOf E n sc' t
  | n + 1, sc, .tagged _ _ t => classFieldOf E n sc t
  | n + 1, sc, .constrained t _ => classFieldOf E n sc t
  | _ + 1, _, _ => none

/-- X.680 52.6: a type whose own notation has an extension marker (or gets one from EXTENSIBILITY
IMPLIED, 13.4): SEQUENCE, SET, CHOICE and ENUMERATED. Constraints do not take that away. -/
def structExt (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Bool :=
  match builtin E n sc t with
  | some (sc', .sequence _ e _) | some (sc', .set _ e _) => e.isSome || sc'.mod.header.extImplied
  | some (sc', .choice _ e) => e.isSome || sc'.mod.header.extImplied
  | some (sc', .enumerated _ e) => e.isSome || sc'.mod.header.extImplied
  | _ => false

/-- The class an "InstanceOfType" names (X.681 C.2), through references, tags and constraints, with
the scope it is written in. -/
def instanceOfOf (E : Env) : Nat → Scope → Ty → Option (Scope × ClassRef)
  | 0, _, _ => none
  | _ + 1, sc, .instanceOf cls => some (sc, cls)
  | n + 1, sc, .ref name => (resolveTy E n sc none name []).bind fun (sc', t) => instanceOfOf E n sc' t
  | n + 1, sc, .extRef mn name =>
    (resolveTy E n sc (some mn) name []).bind fun (sc', t) => instanceOfOf E n sc' t
  | n + 1, sc, .paramRef mn name args =>
    (resolveTy E n sc mn name args).bind fun (sc', t) => instanceOfOf E n sc' t
  | n + 1, sc, .tagged _ _ t => instanceOfOf E n sc t
  | n + 1, sc, .constrained t _ => instanceOfOf E n sc t
  | _ + 1, _, _ => none


/-! ## The components of a SEQUENCE or SET -/

/-- X.680 25.5 (and 27.2 for SET): COMPONENTS OF a sequence (or set) type stands for the root
components of that type, both root lists, without its extension additions and ignoring its
constraints. That the type is a sequence type in a SEQUENCE and a set type in a SET is a validity
rule (`ComponentsOk`). Each
component keeps the scope it is written in, which its own references are resolved in. -/
def expand (E : Env) : Nat → Scope → List Comp → List (Scope × String × Ty × Presence)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | n + 1, sc, .mk nm t p :: rest => (sc, nm, t, p) :: expand E n sc rest
  | n + 1, sc, .componentsOf t :: rest =>
    (match builtin E n sc t with
     | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expand E n sc' (r ++ r2)
     | _ => []) ++ expand E n sc rest

/-- A component, and which extension addition it belongs to, if it is not a root component.
Every component of a "[[ … ]]" group belongs to the same addition. -/
structure Entry where
  /-- the scope the component is written in -/
  scope : Scope
  name : String
  ty : Ty
  presence : Presence
  addition : Option Nat
  /-- the addition is an "ExtensionAdditionGroup" -/
  group : Bool := false

def Presence.isMandatory : Presence → Bool
  | .mandatory => true
  | _ => false

def ExtAdd.comps : ExtAdd → List Comp
  | .one c => [c]
  | .group _ cs => cs

def ExtAdd.isGroup : ExtAdd → Bool
  | .one _ => false
  | .group .. => true

/-- The components of a SEQUENCE or SET type in textual order: the root, the extension additions,
the trailing root (25.1). This is also the order of a `Val.seq` of the type (25.20). -/
def entries (E : Env) (n : Nat) (sc : Scope) (root : List Comp) (ext : Option (List ExtAdd))
    (root2 : List Comp) : List Entry :=
  let mk (a : Option Nat) (g : Bool) (x : Scope × String × Ty × Presence) : Entry :=
    ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, a, g⟩
  (expand E n sc root).map (mk none false) ++
  ((ext.getD []).zipIdx.flatMap fun (e, i) => (expand E n sc e.comps).map (mk (some i) e.isGroup)) ++
  (expand E n sc root2).map (mk none false)

/-- The shape of a SEQUENCE (`isSeq`) or SET value: which components may be present (25.11, 25.13,
25.15). `cs` lists the components present, in the order of `es`. -/
def SeqShape (isSeq : Bool) (es : List Entry) (cs : List (String × Val)) : Prop :=
  let present (e : Entry) : Prop := e.name ∈ cs.map (·.1)
  let adds := es.filter (·.addition.isSome)
  (cs.map (·.1)).Sublist (es.map (·.name)) ∧
  -- 25.11: only components marked OPTIONAL or DEFAULT may be omitted from the root
  (∀ e ∈ es, e.addition = none → e.presence.isMandatory → present e) ∧
  -- 25.13: if any component of an addition group is present, so are its mandatory components
  (∀ e ∈ es, ∀ i, e.addition = some i → e.presence.isMandatory →
    (∃ f ∈ es, f.addition = some i ∧ present f) → present e) ∧
  -- 25.15, for SEQUENCE only (27.4 does not extend it to SET): an extension addition is present
  -- only if every extension addition type between it and the root that is not marked OPTIONAL or
  -- DEFAULT is present. An addition group is optional as a whole (25.13), so this concerns the
  -- additions that are single components (ledger X680-25).
  (isSeq = true → ∀ (j k : Nat) (e f : Entry), j < k → adds[j]? = some e → adds[k]? = some f →
    present f → e.group = false → e.presence.isMandatory → present e)


/-! ## Order, size and characters, as constraints use them -/

/-- X.680 51.4.2 NOTE: the order of REAL values for subtyping. MINUS-INFINITY first, then the
negative numbers, minus zero, plus zero, the positive numbers, PLUS-INFINITY and NOT-A-NUMBER. -/
def RealVal.key : RealVal → Nat × ℚ
  | .minusInfinity => (0, 0)
  | .num _ q => if q < 0 then (1, q) else (4, q)
  | .minusZero => (2, 0)
  | .plusZero => (3, 0)
  | .plusInfinity => (5, 0)
  | .notANumber => (6, 0)

def RealVal.le (a b : RealVal) : Prop :=
  a.key.1 < b.key.1 ∨ (a.key.1 = b.key.1 ∧ a.key.2 ≤ b.key.2)

/-- The order a value range uses (51.4): integers, reals, and single characters in a permitted
alphabet, by their canonical order (43.3: the code point). -/
def Val.le : Val → Val → Prop
  | .int a, .int b => a ≤ b
  | .real a, .real b => a.le b
  | .chars [a], .chars [b] => a ≤ b
  | _, _ => False

def Val.lt (a b : Val) : Prop := a.le b ∧ ¬ b.le a

/-- X.680 51.4: `w` lies between the endpoints. An open endpoint (`<`) is excluded, and MIN and
MAX extend as far as the parent allows (51.4.4). -/
def InRange (lo : Bound) (loOpen : Bool) (hi : Bound) (hiOpen : Bool) (w : Val) : Prop :=
  (match lo with
   | .min => True
   | .max => False
   | .val v => if loOpen then v.lt w else v.le w) ∧
  (match hi with
   | .max => True
   | .min => False
   | .val v => if hiOpen then w.lt v else w.le v)

/-- X.680 51.13, 51.13.3: a number of recurrences (`none`, Unlimited, is above every number) is at
or above a lower endpoint. -/
def RecAbove : Bound → Bool → Option Nat → Prop
  | .min, _, _ => True
  | .val (.int _), _, none => True
  | .val (.int a), loOpen, some k => if loOpen then a < k else a ≤ k
  | _, _, _ => False

/-- ... and at or below an upper endpoint. -/
def RecBelow : Bound → Bool → Option Nat → Prop
  | .max, _, _ => True
  | .val (.int b), hiOpen, some k => if hiOpen then k < b else k ≤ b
  | _, _, _ => False

/-- X.680 51.11–51.13: a value range over TIME values. Which of the three it is depends on the
endpoints: integers for a recurrence range, durations for a duration range, time points for a time
point range.

OPEN (ledger X680-16): 51.13.4 selects values whose "number of recurrence digits" is in the range,
while 51.13.3 orders "Recurrence=Unlimited" as an "infinite number of repetitions". We take the
range to be over the number of recurrences, as 51.13.3 and X.691 32.8 (which encodes that number)
do. -/
def TimeInRange (lo : Bound) (loOpen : Bool) (hi : Bound) (hiOpen : Bool) : TimeV → Prop
  | .recurring k _ => RecAbove lo loOpen k ∧ RecBelow hi hiOpen k
  -- 51.11
  | .interval (.d x) =>
    match lo, hi with
    | .val (.time (.interval (.d a))), .val (.time (.interval (.d b))) => a.between loOpen b hiOpen x
    | _, _ => False
  -- 51.12
  | .point p =>
    match lo, hi with
    | .val (.time (.point a)), .val (.time (.point b)) => a.between loOpen b hiOpen p
    | _, _ => False
  | _ => False

/-- X.680 51.4, and 51.11–51.13 for TIME values. -/
def RangeHas (lo : Bound) (loOpen : Bool) (hi : Bound) (hiOpen : Bool) : Val → Prop
  | .time x => TimeInRange lo loOpen hi hiOpen x
  | w => InRange lo loOpen hi hiOpen w

/-- X.680 51.5.4: the size of a value, in bits, octets, characters or component values. -/
def Val.size? : Val → Option Nat
  | .bits bs => some bs.length
  | .octets os => some os.length
  | .chars cs => some cs.length
  | .regChars cs => some cs.length
  | .seqOf vs => some vs.length
  | .setOf vs => some vs.length
  | _ => none

def Val.charList : Val → List Nat
  | .chars cs => cs
  | _ => []

def Val.regList : Val → List RegChar
  | .regChars cs => cs
  | _ => []

/-- The characters a PATTERN (51.9) matches against: ISO/IEC 10646 code points.

OPEN (ledger X680-21): Annex A writes the characters of a regular expression as ISO/IEC 10646
characters, but Table 11 allows PATTERN on every restricted character string type. A string of
register characters is matched as the ISO/IEC 646 characters it is (`RegChar.ucs?`), and one with
any other register character matches no pattern. -/
def Val.patternChars : Val → Option (List Nat)
  | .chars cs => some cs
  | .regChars cs => cs.mapM RegChar.ucs?
  | _ => none

def Val.elems : Val → List Val
  | .seqOf vs => vs
  | .setOf vs => vs
  | _ => []

/-- X.660 (to which X.680 32.11 refers): an object identifier value has at least two arcs, its
first arc is 0, 1 or 2, and under 0 and 1 the second arc is at most 39. -/
def OidWf (arcs : List Nat) : Prop :=
  2 ≤ arcs.length ∧ arcs.head? ∈ [some 0, some 1, some 2] ∧
    (arcs.head? ≠ some 2 → ∀ a, arcs[1]? = some a → a ≤ 39)

/-! ## The associated types (36.5, 37.5, 44.5)

Written as the text writes them. The text assumes an automatic tagging environment, which affects
tags only, not values. -/

def identificationAlts : List Alt :=
  [.mk "syntaxes" (.sequence [.mk "abstract" .objectIdentifier .mandatory,
                              .mk "transfer" .objectIdentifier .mandatory] none []),
   .mk "syntax" .objectIdentifier,
   .mk "presentation-context-id" (.integer []),
   .mk "context-negotiation" (.sequence [.mk "presentation-context-id" (.integer []) .mandatory,
                                         .mk "transfer-syntax" .objectIdentifier .mandatory] none []),
   .mk "transfer-syntax" .objectIdentifier,
   .mk "fixed" .null]

def pdvLike (dataName : String) : Ty :=
  .sequence [.mk "identification" (.choice identificationAlts none) .mandatory,
             .mk "data-value-descriptor" .objectDescriptor .optional,
             .mk dataName .octetString .mandatory] none []

/-- `WITH COMPONENTS { ..., a ABSENT, b ABSENT }` -/
def absentC (names : List String) : Constraint :=
  .mk (.elem (.withComponents true (names.map fun nm => (nm, none, .absent)))) false none

/-- X.680 36.5 -/
def embeddedPdvAssoc : Ty := .constrained (pdvLike "data-value") (absentC ["data-value-descriptor"])

/-- X.680 37.5.

OPEN (ledger X680-6): 37.4 says the associated type gives "precision to the definition of the
abstract values", yet the NOTE to 37.7 says encoding rules can transfer EXTERNAL values whose
data is not a whole number of octets, which this type cannot represent. We take the abstract values
to be those of the associated type. -/
def externalAssoc : Ty :=
  .constrained (pdvLike "data-value")
    (.mk (.elem (.withComponents true
      [("identification", some (absentC ["syntaxes", "transfer-syntax", "fixed"]), .unspecified)]))
      false none)

/-- X.680 44.5 -/
def characterStringAssoc : Ty :=
  .constrained (pdvLike "string-value") (absentC ["data-value-descriptor"])

/-- X.680 21.5: REAL's associated type, `SEQUENCE { mantissa INTEGER, base INTEGER (2|10),
exponent INTEGER }`. -/
def realAssoc : Ty :=
  .sequence [.mk "mantissa" (.integer []) .mandatory,
             .mk "base" (.constrained (.integer [])
               (.mk (.union (.elem (.single (.int 2))) (.elem (.single (.int 10)))) false none))
               .mandatory,
             .mk "exponent" (.integer []) .mandatory] none []

/-- X.680 21.3, 21.5: the values of the associated type that denote a numeric REAL value: `M`, `B`,
`E` with `M × B^E` its number, `M ≠ 0`. -/
def RealVal.Denotes : RealVal → Val → Prop
  | .num b q, w => ∃ m e : Int, m ≠ 0 ∧
      let bv : Int := match b with | .two => 2 | .ten => 10
      q = m * (bv : ℚ) ^ e ∧ w = .seq [("mantissa", .int m), ("base", .int bv), ("exponent", .int e)]
  | _, _ => False

/-- `INTEGER (lo..MAX)` -/
def intFrom (lo : Int) : Ty :=
  .constrained (.integer []) (.mk (.elem (.range (.val (.int lo)) false .max false)) false none)

def durationElemNames : List String :=
  ["years", "months", "weeks", "days", "hours", "minutes", "seconds"]

/-- X.680 38.4.4.2: the components of DURATION-EQUIVALENT. -/
def durationEquivComps : List Comp :=
  durationElemNames.map (fun nm => .mk nm (intFrom 0) .optional) ++
  [.mk "fractional-part" (.sequence [.mk "number-of-digits" (intFrom 1) .mandatory,
                                     .mk "fractional-value" (intFrom 0) .mandatory] none [])
     .optional]

/-- X.680 38.4.4.2, 38.4.4.3: the DURATION-EQUIVALENT value whose components are the time elements
of a duration, with the fractional part of the least significant one (NOTE 2).

OPEN (ledger X680-17): a zero element above the least significant one may be included or omitted
without changing the abstract value (38.2.3), so whether its component is present in the
equivalent sequence value is not determined. We take the normal form, which omits it, as X.691
32.6.3 does for the encoding. -/
def DurationV.equiv (d : DurationV) : Val :=
  let d := d.norm
  .seq ((durationElemNames.zip d.elems).filterMap (fun (nm, o) => o.map fun x => (nm, .int x)) ++
        if d.frac = [] then []
        else [("fractional-part", .seq [("number-of-digits", .int d.frac.length),
                                         ("fractional-value", .int d.frac.val)])])





/-! ## Equality of abstract values -/

/-- X.680 22.7: trailing 0 bits removed. -/
def stripTrailingZeros (bs : Bits) : Bits := (bs.reverse.dropWhile (· == false)).reverse

/-- X.680 38.2.3: two time values are the same abstract value if their normal forms are equal. -/
def timeEqv : Val → Val → Prop
  | .time a, .time b => a.norm = b.norm
  | _, _ => False

/-- Component `en` of two SEQUENCE or SET values `cs` and `ds` is the same: both leave it out, or
both have it and the values are equal (`eq`), or one leaves out a DEFAULT component and the other
has its default value, the value its notation `d` denotes (`ev`). -/
def SeqEntry (ev : Scope → Val → Val → Prop) (eq : Scope → Ty → Val → Val → Prop)
    (cs ds : List (String × Val)) (en : Entry) : Prop :=
  match cs.lookup en.name, ds.lookup en.name with
  | none, none => True
  | some x, some y => eq en.scope en.ty x y
  | some x, none => match en.presence with
    | .default_ d => ∃ d', ev en.scope d d' ∧ eq en.scope en.ty x d'
    | _ => False
  | none, some y => match en.presence with
    | .default_ d => ∃ d', ev en.scope d d' ∧ eq en.scope en.ty d' y
    | _ => False

/-- Two SEQUENCE or SET values are the same abstract value: component by component, an omitted
DEFAULT component counting as its default value (25.12: omitting it is "exactly equivalent" to
inserting that value, which its notation denotes, `evalVal`). `eq` is the equality of each
component type. -/
def SeqEqv (ev : Scope → Val → Val → Prop) (es : List Entry) (eq : Scope → Ty → Val → Val → Prop)
    (cs ds : List (String × Val)) : Prop :=
  (∀ p ∈ cs, p.1 ∈ es.map (·.name)) ∧ (∀ p ∈ ds, p.1 ∈ es.map (·.name)) ∧
  ∀ en ∈ es, SeqEntry ev eq cs ds en


/-! ## Enclosing values (X.682 10.10) -/

/-- The kinds of construction an "AtNotation" climbs through (X.682 10.10). -/
inductive FrameKind where
  | seq | set | choice | seqOf | setOf
  deriving DecidableEq

/-- A textually enclosing value, with the components its type offers to an "AtNotation": each
component's (or alternative's) name, scope and type. -/
structure Frame where
  kind : FrameKind
  val : Val
  comps : List (String × Scope × Ty)

def Frame.isSetSeq (f : Frame) : Bool := f.kind == .seq || f.kind == .set
def Frame.isSetSeqChoice (f : Frame) : Bool := f.isSetSeq || f.kind == .choice

/-- X.682 10.8: the value an "identifier" names in a set, sequence or choice value: the
component, if present, or the chosen alternative, if it is that one. -/
def Val.component : Val → String → Option Val
  | .seq cs, nm => cs.lookup nm
  | .choice a x, nm => if a = nm then some x else none
  | _, _ => none

/-- The components a set, sequence or choice type offers to an "AtNotation". -/
def structComps (E : Env) (n : Nat) (sc : Scope) (t : Ty) : List (String × Scope × Ty) :=
  match builtin E n sc t with
  | some (sc', .sequence r e r2) | some (sc', .set r e r2) =>
    (entries E n sc' r e r2).map fun en => (en.name, en.scope, en.ty)
  | some (sc', .choice r e) => (choiceAlts r e).map fun a => (a.name, sc', a.ty)
  | _ => []

/-- X.682 10.8: follow a "ComponentIdList" from a value whose type offers `comps`: the value
reached, with its scope and type. `none` if a component on the way is absent. -/
def navigate (E : Env) (n : Nat) : List (String × Scope × Ty) → Val → List String →
    Option (Val × Scope × Ty)
  | _, _, [] => none
  | comps, v, [nm] => match comps.find? (·.1 == nm), v.component nm with
    | some (_, sc, t), some x => some (x, sc, t)
    | _, _ => none
  | comps, v, nm :: rest => match comps.find? (·.1 == nm), v.component nm with
    | some (_, sc, t), some x => navigate E n (structComps E n sc t) x rest
    | _, _ => none

/-- X.682 10.10: the component an "AtNotation" refers to, given the textually enclosing values,
innermost first. -/
def AtRef.resolve (E : Env) (n : Nat) (r : AtRef) (outer : List Frame) : Option (Val × Scope × Ty) :=
  let base : Option Frame := match r.level with
    -- 10.10 a): the outermost textually enclosing set, sequence or choice type
    | none => (outer.filter Frame.isSetSeqChoice).getLast?
    -- 10.10 b): up from the innermost textually enclosing set or sequence type by `k` levels
    | some k => (outer.findIdx? Frame.isSetSeq).bind fun i => outer[i + k]?
  base.bind fun f => navigate E n f.comps f.val r.path

/-! ## Value sets, and the set arithmetic of X.680 50 -/

/-- A type's values: its root values, all its values, and whether it is extensible. -/
structure VSet where
  root : Val → Prop
  all : Val → Prop
  ext : Bool

def VSet.empty : VSet := ⟨fun _ => False, fun _ => False, false⟩

/-- The same values, not extensible. -/
def VSet.noExt (s : VSet) : VSet := ⟨s.root, s.all, false⟩

/-- The same values, extensible if `b`. -/
def VSet.keepExt (b : Bool) (s : VSet) : VSet := ⟨s.root, s.all, s.ext || b⟩

/-- A set of values with no extension additions and no extensibility. -/
def VSet.plain (s : Val → Prop) : VSet := ⟨s, s, false⟩

/-- An element set during set arithmetic (50.5): its root values, its root values together with
its extension additions, and whether it is extensible (50.4). -/
structure ESet where
  r : Val → Prop
  a : Val → Prop
  ext : Bool

def ESet.empty : ESet := ⟨fun _ => False, fun _ => False, false⟩
def ESet.fixed (s : Val → Prop) : ESet := ⟨s, s, false⟩

/-- 50.2 b), 50.4 b), 50.5 -/
def ESet.union (A B : ESet) : ESet :=
  ⟨fun v => A.r v ∨ B.r v, fun v => A.r v ∨ B.r v ∨ A.a v ∨ B.a v, A.ext || B.ext⟩

/-- 50.2 c), 50.4 c), 50.5 -/
def ESet.inter (A B : ESet) : ESet :=
  ⟨fun v => A.r v ∧ B.r v, fun v => (A.r v ∧ B.r v) ∨ (A.a v ∧ B.a v), A.ext || B.ext⟩

/-- 50.2 d), 50.4 d), 50.5 -/
def ESet.except (A B : ESet) : ESet :=
  ⟨fun v => A.r v ∧ ¬ B.r v, fun v => (A.r v ∧ ¬ B.r v) ∨ (A.a v ∧ ¬ B.a v), A.ext⟩

/-- 50.2 a): every value of the governor `g` except those of the exclusions. -/
def ESet.allExcept (g : Val → Prop) (B : ESet) : ESet :=
  ⟨fun v => g v ∧ ¬ B.r v, fun v => g v ∧ ¬ B.r v, false⟩

/-- 49.6, 50.4 a), 50.5: the constrained type, from its root element set and, after an ellipsis,
its additional element set. -/
def VSet.ofSpecs (extensible : Bool) (r : ESet) (x : Option ESet) : VSet :=
  ⟨r.r, fun v => r.a v ∨ ∃ e, x = some e ∧ e.a v, extensible || r.ext⟩

/-- `INTEGER (0..MAX)`, the parent type of a size constraint (51.5.3). -/
def sizeParent : VSet := .plain fun v => ∃ k : Nat, v = .int k

/-- 51.5: the values of `g` whose size the constraint (as `S`) allows.
OPEN (ledger X680-8): 50.4 does not make SIZE extensible when its constraint is; we do, as 51.7.4
does for FROM, and as X.691 10.3 presumes. -/
def ESet.bySize (g : Val → Prop) (S : VSet) : ESet :=
  ⟨fun w => g w ∧ ∃ k : Nat, w.size? = some k ∧ S.root (.int k),
   fun w => g w ∧ ∃ k : Nat, w.size? = some k ∧ S.all (.int k),
   S.ext⟩

/-- 51.7.3, 51.7.4: the strings of `g` whose characters all appear in some value the constraint
(as `S`) allows. -/
def ESet.byAlphabet (g : Val → Prop) (S : VSet) : ESet :=
  ⟨fun w => g w ∧ (∀ ch ∈ w.charList, ∃ s, S.root s ∧ ch ∈ s.charList) ∧
     ∀ ch ∈ w.regList, ∃ s, S.root s ∧ ch ∈ s.regList,
   fun w => g w ∧ (∀ ch ∈ w.charList, ∃ s, S.all s ∧ ch ∈ s.charList) ∧
     ∀ ch ∈ w.regList, ∃ s, S.all s ∧ ch ∈ s.regList,
   S.ext⟩

/-- 51.8.4: the values of `g` whose every element is in the element type's subtype `S`. -/
def ESet.byElems (g : Val → Prop) (S : VSet) : ESet :=
  ⟨fun w => g w ∧ ∀ x ∈ w.elems, S.root x, fun w => g w ∧ ∀ x ∈ w.elems, S.all x, S.ext⟩

/-- A "ComponentConstraint" as written (51.8.8), looked up by component name. -/
def lookupNC (ncs : List (String × Option Constraint × PresenceC)) (nm : String) :
    Option (Option Constraint × PresenceC) :=
  (ncs.find? (·.1 == nm)).map (·.2)

/-- 51.8.7, 51.8.10.1, 51.8.10.3: what the presence constraint on a SEQUENCE or SET component
demands, given whether the component is `present`. -/
def SeqPresenceOk (isPartial : Bool) (p : Presence) :
    Option (Option Constraint × PresenceC) → Prop → Prop
  | some (_, .present), present => present
  | some (_, .absent), present => ¬ present
  -- 51.8.10.3 a): in a full specification, empty means PRESENT for an OPTIONAL component
  | some (_, .unspecified), present => isPartial = false → p = .optional → present
  | some (_, .optional), _ => True
  -- 51.8.7: in a full specification, a component not listed is ABSENT if it can be, that is,
  -- if it is marked OPTIONAL (51.8.10.1)
  | none, present => isPartial = false → p = .optional → ¬ present

/-- 51.8.10.2, 51.8.7: the same for a CHOICE alternative, given whether it is `used`. -/
def AltPresenceOk (isPartial : Bool) :
    Option (Option Constraint × PresenceC) → Prop → Prop
  | some (_, .present), used => used
  | some (_, .absent), used => ¬ used
  | some _, _ => True
  | none, used => isPartial = false → ¬ used

/-- 51.8.9: the component's value is in the subtype of its type the value constraint selects.
`inner sc t c` is that subtype. Root values only, if `isRoot`. -/
def ValueOk (inner : Scope → Ty → Constraint → VSet) (isRoot : Bool) (sc : Scope) (t : Ty) :
    Option (Option Constraint × PresenceC) → Option Val → Prop
  | some (some c, _), some x => if isRoot then (inner sc t c).root x else (inner sc t c).all x
  | _, _ => True

/-- X.680 25.12: `w` is the value of a DEFAULT component `en` that is omitted, as `ev` evaluates the
DEFAULT's value notation. -/
def DefaultIs (ev : Scope → Val → Val → Prop) (en : Entry) (w : Val) : Prop :=
  match en.presence with
  | .default_ d => ev en.scope d w
  | _ => False

/-- 51.8.5–51.8.10, on a SEQUENCE or SET parent with components `es`. -/
def ESet.byComponents (g : Val → Prop) (es : List Entry) (isPartial : Bool)
    (ncs : List (String × Option Constraint × PresenceC)) (inner : Scope → Ty → Constraint → VSet)
    (dflt : Entry → Val → Prop := fun _ _ => False) : ESet :=
  let ok (isRoot : Bool) : Val → Prop
    | .seq cs => ∀ en ∈ es,
        SeqPresenceOk isPartial en.presence (lookupNC ncs en.name) (en.name ∈ cs.map (·.1)) ∧
        ValueOk inner isRoot en.scope en.ty (lookupNC ncs en.name) (cs.lookup en.name) ∧
        -- 51.8.9 with 25.12: an omitted DEFAULT component has its default value
        (cs.lookup en.name = none → ∀ w, dflt en w →
          ValueOk inner isRoot en.scope en.ty (lookupNC ncs en.name) (some w))
    | _ => False
  ⟨fun w => g w ∧ ok true w, fun w => g w ∧ ok false w, false⟩

/-- 51.8.5–51.8.10, on a CHOICE parent, read in scope `asc`, with alternatives `alts`. -/
def ESet.byAlternatives (g : Val → Prop) (asc : Scope) (alts : List Alt) (isPartial : Bool)
    (ncs : List (String × Option Constraint × PresenceC)) (inner : Scope → Ty → Constraint → VSet) :
    ESet :=
  let ok (isRoot : Bool) : Val → Prop
    | .choice chosen x => ∀ a ∈ alts,
        AltPresenceOk isPartial (lookupNC ncs a.name) (a.name = chosen) ∧
        ValueOk inner isRoot asc a.ty (lookupNC ncs a.name) (if a.name = chosen then some x else none)
    | _ => False
  ⟨fun w => g w ∧ ok true w, fun w => g w ∧ ok false w, false⟩

/-- X.680 25, 27: the values of a SEQUENCE or SET type with components `es`. `comp sc t whole x`:
`x` is a value of component type `t` within the value `whole`. The root values are those with no
extension addition present (50.8). -/
def seqVSet (isSeq : Bool) (es : List Entry) (extensible : Bool) (comp : Scope → Ty → Val → Val → Prop) :
    VSet :=
  let ok (whole : Val) (cs : List (String × Val)) : Prop :=
    SeqShape isSeq es cs ∧ ∀ p ∈ cs, ∃ en ∈ es, en.name = p.1 ∧ comp en.scope en.ty whole p.2
  ⟨fun v => ∃ cs, v = .seq cs ∧ ok v cs ∧ ∀ p ∈ cs, ∀ en ∈ es, en.name = p.1 → en.addition = none,
   fun v => ∃ cs, v = .seq cs ∧ ok v cs,
   extensible⟩

/-- X.680 29: the values of a CHOICE type. -/
def choiceVSet (root alts : List Alt) (extensible : Bool) (alt : Ty → Val → Val → Prop) : VSet :=
  ⟨fun v => ∃ a ∈ root, ∃ w, v = .choice a.name w ∧ alt a.ty v w,
   fun v => ∃ a ∈ alts, ∃ w, v = .choice a.name w ∧ alt a.ty v w,
   extensible⟩

/-- X.680 38: the values of TIME with the given property settings (51.10). -/
def timeVSet (ps : List (String × String)) : VSet :=
  .plain fun v => ∃ t, v = .time t ∧ t.Wf ∧ t.satisfies ps

/-- X.680 46.3, 47.3: VisibleString values in a format. -/
def formatVSet (ok : List Char → Bool) : VSet :=
  .plain fun v => ∃ cs, v = .chars cs ∧ (∀ c ∈ cs, visibleChars.mem c) ∧ ok (cs.map Char.ofNat)

/-- X.680 21.5: an inner subtyping constraint on REAL, as `S` on the associated type's values.
NOTE 2: only numeric values other than zero can be selected.

OPEN (ledger X680-23): a numeric value has many representations `M × B^E` (21.3). We take it to be
selected when one of them is. -/
def ESet.byReal (g : Val → Prop) (S : ESet) : ESet :=
  ⟨fun w => g w ∧ ∃ r, w = .real r ∧ ∃ x, r.Denotes x ∧ S.r x,
   fun w => g w ∧ ∃ r, w = .real r ∧ ∃ x, r.Denotes x ∧ S.a x,
   S.ext⟩

/-- X.680 38.4.4.1: an inner subtyping constraint on a duration subtype, as `S` on the equivalent
sequence values. -/
def ESet.byDuration (g : Val → Prop) (S : ESet) : ESet :=
  ⟨fun w => g w ∧ ∃ d, w = .time (.interval (.d d)) ∧ S.r d.equiv,
   fun w => g w ∧ ∃ d, w = .time (.interval (.d d)) ∧ S.a d.equiv,
   S.ext⟩

/-- 41: the strings of characters in a collection. -/
def charsVSet (rs : CharRanges) : VSet := .plain fun v => ∃ cs, v = .chars cs ∧ ∀ c ∈ cs, rs.mem c

/-- 41, Table 8: the values of a restricted character string type. -/
def restrictedVSet (k : StrType) : VSet :=
  if k.isRegister then .plain fun v => ∃ cs, v = .regChars cs ∧ ∀ c ∈ cs, k.regAllows c
  else charsVSet k.chars

/-- X.682 9: a user-defined constraint is specified in comments only.
OPEN (ledger X682-1): it does not restrict the value set here. -/
def ESet.userDefined (g : Val → Prop) : ESet := .fixed g

/-- The class that governs a field that is an object or object set field. -/
def fieldClass (E : Env) (n : Nat) (o : ObjV) (f : String) : Option (Scope × List FieldSpec) :=
  match o.fields.find? (·.name == f) with
  | some (.objectField _ c _) | some (.objectSetField _ c _) => classFields E n o.clsSc c
  | _ => none

/-- X.681 13.4: the class that governs the objects at the end of a path of link fields. -/
def classAt (E : Env) (n : Nat) (cf : Scope × List FieldSpec) (path : List String) :
    Option (Scope × List FieldSpec) :=
  match fieldAt E n cf path with
  | some (sc, .objectField _ c _) | some (sc, .objectSetField _ c _) => classFields E n sc c
  | _ => none

/-- UNIQUE fields of a class (X.681 9.6). -/
def uniqueFields (fs : List FieldSpec) : List (String × Ty) :=
  fs.filterMap fun | .fixedValue nm t true _ => some (nm, t) | _ => none

mutual
  /-- `eqv E n sc t v w`: `v` and `w` are the same abstract value of `t`, read in scope `sc`. -/
  def eqv (E : Env) : Nat → Scope → Ty → Val → Val → Prop
    | 0, _, _, _, _ => False
    | n + 1, sc, .ref name, v, w => match resolveTy E n sc none name [] with
      | some (sc', t) => eqv E n sc' t v w
      | none => False
    | n + 1, sc, .extRef mn name, v, w => match resolveTy E n sc (some mn) name [] with
      | some (sc', t) => eqv E n sc' t v w
      | none => False
    | n + 1, sc, .paramRef mn name args, v, w => match resolveTy E n sc mn name args with
      | some (sc', t) => eqv E n sc' t v w
      | none => False
    | n + 1, sc, .tagged _ _ t, v, w => eqv E n sc t v w
    | n + 1, sc, .constrained t _, v, w => eqv E n sc t v w
    | n + 1, sc, .selection nm t, v, w => match builtin E n sc t with
      | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
        | some a => eqv E n sc' a.ty v w
        | none => False
      | _ => False
    | n + 1, sc, .classField cls path, v, w => match builtin E n sc (.classField cls path) with
      | some (sc', t) => eqv E n sc' t v w
      | none => False
    | n + 1, sc, .instanceOf cls, v, w => eqv E n sc (instanceOfTy cls) v w
    | n + 1, sc, .sequence r e r2, v, w | n + 1, sc, .set r e r2, v, w => match v, w with
      | .seq cs, .seq ds => SeqEqv (evalVal E n) (entries E n sc r e r2) (eqv E n) cs ds
      | _, _ => False
    | n + 1, sc, .sequenceOf e, v, w => match v, w with
      | .seqOf xs, .seqOf ys => List.Forall₂ (eqv E n sc e) xs ys
      | _, _ => False
    -- 28: a SET OF value is unordered
    | n + 1, sc, .setOf e, v, w => match v, w with
      | .setOf xs, .setOf ys => ∃ ys', ys'.Perm ys ∧ List.Forall₂ (eqv E n sc e) xs ys'
      | _, _ => False
    | n + 1, sc, .choice root ext, v, w => match v, w with
      | .choice a x, .choice b y =>
        a = b ∧ ∃ alt ∈ choiceAlts root ext, alt.name = a ∧ eqv E n sc alt.ty x y
      | _, _ => False
    | _ + 1, _, .bitString named, v, w => match v, w with
      | .bits xs, .bits ys => if named = [] then xs = ys
        -- 22.7
        else stripTrailingZeros xs = stripTrailingZeros ys
      | _, _ => False
    -- X.681 14.6: the same type, and the same value of it
    | n + 1, sc, .openType, v, w => match v, w with
      | .open_ t1 x, .open_ t2 y => t1 = t2 ∧ eqv E n sc t1 x y
      | _, _ => False
    | n + 1, _, .embeddedPdv, v, w => eqv E n (.ofModule assocModule) embeddedPdvAssoc v w
    | n + 1, _, .external, v, w => eqv E n (.ofModule assocModule) externalAssoc v w
    | n + 1, _, .characterString, v, w => eqv E n (.ofModule assocModule) characterStringAssoc v w
    -- 38.2.3
    | _ + 1, _, .time, v, w | _ + 1, _, .date, v, w | _ + 1, _, .timeOfDay, v, w
    | _ + 1, _, .dateTime, v, w | _ + 1, _, .duration, v, w => timeEqv v w
    | _ + 1, _, _, v, w => v = w

  /-- `evalVal E n sc v w`: value notation `v`, read in scope `sc`, denotes the abstract value `w`.
  References are replaced by what they name (X.680 14.1, 16.2; X.683 9; X.681 15). -/
  def evalVal (E : Env) : Nat → Scope → Val → Val → Prop
    | 0, _, _, _ => False
    | n + 1, sc, .ref mn name args, w => match resolveVal E n sc mn name args with
      | some (sc', v) => evalVal E n sc' v w
      | none => False
    | n + 1, sc, .fromObject src path, w =>
      ∃ o, (evalObjSet E n sc none src).a o ∧ ∃ sc' v, cell E n o path (sc', .value v) ∧ evalVal E n sc' v w
    | n + 1, sc, .seq cs, w =>
      ∃ ds, w = .seq ds ∧ List.Forall₂ (fun a b => a.1 = b.1 ∧ evalVal E n sc a.2 b.2) cs ds
    | n + 1, sc, .seqOf vs, w => ∃ ws, w = .seqOf ws ∧ List.Forall₂ (evalVal E n sc) vs ws
    | n + 1, sc, .setOf vs, w => ∃ ws, w = .setOf ws ∧ List.Forall₂ (evalVal E n sc) vs ws
    | n + 1, sc, .choice a x, w => ∃ y, w = .choice a y ∧ evalVal E n sc x y
    | n + 1, sc, .open_ t x, w => ∃ y, w = .open_ t y ∧ evalVal E n sc x y
    -- notation the front end has not read denotes no value
    | _ + 1, _, .raw _, _ => False
    | _ + 1, _, v, w => w = v

  /-- X.681 11: the objects an "Object" notation denotes, governed by class `cf` if known. -/
  def evalObj (E : Env) : Nat → Scope → Option (Scope × List FieldSpec) → Obj → ObjV → Prop
    | 0, _, _, _, _ => False
    | _ + 1, sc, cf, .defn settings, o =>
      let (csc, fs) := cf.getD (sc, [])
      o = ⟨sc, settings, csc, fs⟩
    | _ + 1, _, _, .raw _, _ => False
    | n + 1, sc, cf, .ref mn name args, o => match resolveObj E n sc mn name args with
      | some (sc', c, ob) =>
        evalObj E n sc' ((c.bind fun c => classFields E n sc' c).or cf) ob o
      | none => False
    -- 15 "ObjectFromObject"
    | n + 1, sc, cf, .fromObject src path, o =>
      ∃ o0, evalObj E n sc cf src o0 ∧ ∃ sc' ob, cell E n o0 path (sc', .object ob) ∧
        evalObj E n sc' (classAt E n (o0.clsSc, o0.fields) path) ob o

  /-- X.681 13.2–13.4: a cell of an object's associated table, named by a path of field names. A
  link field that is an object set field gives one row per object of the set, so there can be
  several cells for one path. -/
  def cell (E : Env) : Nat → ObjV → List String → Scope × Setting → Prop
    | 0, _, _, _ => False
    | _ + 1, _, [], _ => False
    | _ + 1, o, [f], x => o.setting f = some x
    | n + 1, o, f :: rest, x => match o.setting f with
      | some (sc', .object ob) => ∃ o', evalObj E n sc' (fieldClass E n o f) ob o' ∧ cell E n o' rest x
      | some (sc', .objectSet s) =>
        ∃ o', (evalObjSet E n sc' (fieldClass E n o f) s).a o' ∧ cell E n o' rest x
      | _ => False

  /-- X.681 12: the objects of an object set, governed by class `cf` if known. -/
  def evalObjSet (E : Env) : Nat → Scope → Option (Scope × List FieldSpec) → ObjSet → OSet
    | 0, _, _, _ => .empty
    | n + 1, sc, cf, .ref mn name args => match resolveObjSet E n sc mn name args with
      | some (sc', c, s) => evalObjSet E n sc' ((c.bind fun c => classFields E n sc' c).or cf) s
      | none => .empty
    | n + 1, sc, cf, .spec root ext adds =>
      OSet.ofSpecs ext (root.map (oelems E n sc cf)) (adds.map (oelems E n sc cf))

  /-- X.680 50 over objects (X.681 12.10). -/
  def oelems (E : Env) : Nat → Scope → Option (Scope × List FieldSpec) → OElems → OSet
    | 0, _, _, _ => .empty
    | n + 1, sc, cf, .obj o => ⟨fun x => evalObj E n sc cf o x, fun x => evalObj E n sc cf o x, false⟩
    -- 12.5: an extensible object set referenced in another passes on its extensibility
    | n + 1, sc, cf, .set s => evalObjSet E n sc cf s
    | n + 1, sc, cf, .union a b => (oelems E n sc cf a).union (oelems E n sc cf b)
    | n + 1, sc, cf, .inter a b => (oelems E n sc cf a).inter (oelems E n sc cf b)
    | n + 1, sc, cf, .except a b => (oelems E n sc cf a).except (oelems E n sc cf b)
    -- 15 "ObjectSetFromObjects": the objects in a column of object or object set fields
    | n + 1, sc, _, .fromObjects src path =>
      let S := evalObjSet E n sc none src
      let col (row : ObjV) (x : ObjV) : Prop :=
        ∃ sc' st, cell E n row path (sc', st) ∧
          match st with
          | .object ob => evalObj E n sc' (classAt E n (row.clsSc, row.fields) path) ob x
          | .objectSet s => (evalObjSet E n sc' (classAt E n (row.clsSc, row.fields) path) s).a x
          | _ => False
      ⟨fun x => ∃ row, S.r row ∧ col row x, fun x => ∃ row, S.a row ∧ col row x, S.ext⟩

  /-- The values of a type written in scope `sc`, inside the textually enclosing values `outer`
  (innermost first; X.682 10.10). `H` is the encoding rules' answer for contents constraints
  (X.682 11.4). -/
  def sem (E : Env) (H : ContentsHook) : Nat → Scope → List Frame → Ty → VSet
    | 0, _, _, _ => .empty
    -- 18
    | _ + 1, _, _, .boolean => .plain fun v => ∃ b, v = .bool b
    -- 19.3: named numbers do not restrict the values
    | _ + 1, _, _, .integer _ => .plain fun v => ∃ i, v = .int i
    -- 20; 13.4 EXTENSIBILITY IMPLIED also makes an enumeration extensible
    | _ + 1, sc, _, .enumerated root ext =>
      ⟨fun v => ∃ p ∈ root, v = .enum p.1,
       fun v => ∃ p ∈ root ++ ext.getD [], v = .enum p.1,
       ext.isSome || sc.mod.header.extImplied⟩
    -- 21.3
    | _ + 1, _, _, .real => .plain fun v => ∃ r, v = .real r ∧ r.Wf
    -- 22.6: named bits do not restrict the values
    | _ + 1, _, _, .bitString _ => .plain fun v => ∃ bs, v = .bits bs
    -- 23
    | _ + 1, _, _, .octetString => .plain fun v => ∃ os, v = .octets os
    -- 24
    | _ + 1, _, _, .null => .plain (· = .null)
    -- 25, 27
    | n + 1, sc, outer, .sequence r e r2 =>
      let es := entries E n sc r e r2
      seqVSet true es (e.isSome || sc.mod.header.extImplied) fun sc' t whole x =>
        (sem E H n sc' (⟨.seq, whole, es.map fun en => (en.name, en.scope, en.ty)⟩ :: outer) t).all x
    | n + 1, sc, outer, .set r e r2 =>
      let es := entries E n sc r e r2
      seqVSet false es (e.isSome || sc.mod.header.extImplied) fun sc' t whole x =>
        (sem E H n sc' (⟨.set, whole, es.map fun en => (en.name, en.scope, en.ty)⟩ :: outer) t).all x
    -- 26, 28
    | n + 1, sc, outer, .sequenceOf el => .plain fun v => ∃ vs, v = .seqOf vs ∧
        ∀ x ∈ vs, (sem E H n sc (⟨.seqOf, v, [("", sc, el)]⟩ :: outer) el).all x
    | n + 1, sc, outer, .setOf el => .plain fun v => ∃ vs, v = .setOf vs ∧
        ∀ x ∈ vs, (sem E H n sc (⟨.setOf, v, [("", sc, el)]⟩ :: outer) el).all x
    -- 29
    | n + 1, sc, outer, .choice root ext =>
      let alts := choiceAlts root ext
      choiceVSet root alts (ext.isSome || sc.mod.header.extImplied) fun t whole x =>
        (sem E H n sc (⟨.choice, whole, alts.map fun a => (a.name, sc, a.ty)⟩ :: outer) t).all x
    -- 30.2: the selected alternative's type; a constraint on the selection is ignored (49.3)
    | n + 1, sc, _, .selection nm t =>
      match builtin E n sc t with
      | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
        | some a => sem E H n sc' [] a.ty
        | none => .empty
      | _ => .empty
    -- 32, X.660
    | _ + 1, _, _, .objectIdentifier => .plain fun v => ∃ arcs, v = .oid arcs ∧ OidWf arcs
    -- 33.3: one or more arcs
    | _ + 1, _, _, .relativeOid => .plain fun v => ∃ arcs, v = .oid arcs ∧ arcs ≠ []
    -- 34, 35
    | _ + 1, _, _, .oidIri => .plain fun v => ∃ ls, v = .iri ls ∧ ls ≠ []
    | _ + 1, _, _, .relativeOidIri => .plain fun v => ∃ ls, v = .iri ls ∧ ls ≠ []
    -- 36.5, 37.5, 44.5
    | n + 1, _, _, .embeddedPdv => sem E H n (.ofModule assocModule) [] embeddedPdvAssoc
    | n + 1, _, _, .external => sem E H n (.ofModule assocModule) [] externalAssoc
    | n + 1, _, _, .characterString => sem E H n (.ofModule assocModule) [] characterStringAssoc
    -- 41
    | _ + 1, _, _, .restricted k => restrictedVSet k
    -- 38.2
    | _ + 1, _, _, .time => timeVSet []
    -- 38.4.1–38.4.4: TIME with property settings
    | _ + 1, _, _, .date => timeVSet dateSettings
    | _ + 1, _, _, .timeOfDay => timeVSet timeOfDaySettings
    | _ + 1, _, _, .dateTime => timeVSet dateTimeSettings
    | _ + 1, _, _, .duration => timeVSet durationSettings
    -- 46.3, 47.3: VisibleString values in a format
    | _ + 1, _, _, .generalizedTime => formatVSet Notation.generalizedTimeOk
    | _ + 1, _, _, .utcTime => formatVSet Notation.utcTimeOk
    -- 48: GraphicString values
    | _ + 1, _, _, .objectDescriptor => restrictedVSet .graphic
    -- X.680 13.19, 14.1, 14.6; X.683 9. A referenced type's text is elsewhere, so no enclosing
    -- values are visible from it (X.682 10.10).
    | n + 1, sc, _, .ref name => match resolveTy E n sc none name [] with
      | some (sc', t) => sem E H n sc' [] t
      | none => .empty
    | n + 1, sc, _, .extRef mn name => match resolveTy E n sc (some mn) name [] with
      | some (sc', t) => sem E H n sc' [] t
      | none => .empty
    | n + 1, sc, _, .paramRef mn name args => match resolveTy E n sc mn name args with
      | some (sc', t) => sem E H n sc' [] t
      | none => .empty
    -- 31: tagging does not change the values
    | n + 1, sc, outer, .tagged _ _ t => sem E H n sc outer t
    -- 49
    | n + 1, sc, outer, .constrained t c => cons E H n sc outer t (sem E H n sc outer t) c
    -- X.681 14.2, 14.6: a value of any type, with that type
    | n + 1, _, _, .openType => .plain fun v => ∃ t w, v = .open_ t w ∧ ∃ sc', (sem E H n sc' [] t).all w
    -- X.681 14.2–14.5: a type field is an open type; a fixed-type field is its type
    | n + 1, sc, _, .classField cls path =>
      match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => sem E H n sc' [] t
      | some (_, .typeField _ _) | some (_, .varValue _ _ _) | some (_, .varValueSet _ _ _) =>
        .plain fun v => ∃ t w, v = .open_ t w ∧ ∃ sc', (sem E H n sc' [] t).all w
      -- 14.5: not a type
      | _ => .empty
    -- X.681 15: a column of the associated table, as a type. 12.6: a value set from an extensible
    -- object set is not extensible.
    | n + 1, sc, _, .fromObjects src path =>
      let S := evalObjSet E n sc none src
      .plain fun v => ∃ row, S.a row ∧ ∃ sc' st, cell E n row path (sc', st) ∧
        match st with
        | .type t => (sem E H n sc' [] t).all v
        | .value w => evalVal E n sc' w v
        | .valueSet c => match fieldAt E n (row.clsSc, row.fields) path with
          | some (fsc, .fixedValueSet _ ft _) => (cons E H n sc' [] ft (sem E H n fsc [] ft) c).all v
          | _ => False
        | _ => False
    -- X.681 Annex C
    -- X.681 C.6: in an environment of EXPLICIT TAGS, so not EXTENSIBILITY IMPLIED
    | n + 1, sc, outer, .instanceOf cls => (sem E H n sc outer (instanceOfTy cls)).noExt

  /-- X.680 49–52 and X.682: constraint `c` applied to a parent type `pt` whose values are
  `parent`. Only the parent's root takes part (50.7, 50.8, 50.11).
  - A subtype constraint: the result does not inherit the extensibility of the parent's
    constraints (50.11, 52.5), but a type with an extension marker stays extensible (52.6 and its
    NOTE: "Inner type constraints have no effect on extensibility").
  - A general constraint (X.682) does not affect the parent's extensibility (50.11 NOTE). -/
  def cons (E : Env) (H : ContentsHook) : Nat → Scope → List Frame → Ty → VSet → Constraint → VSet
    | 0, _, _, _, _, _ => .empty
    | n + 1, sc, outer, pt, parent, .mk root extensible adds =>
      (VSet.ofSpecs extensible (eset E H n sc outer pt parent.root root)
        (adds.map (eset E H n sc outer pt parent.root))).keepExt (structExt E n sc pt)
    -- X.682 10
    | n + 1, sc, outer, pt, parent, .table os refs =>
      match classFieldOf E n sc pt with
      | some (csc, cls, path) =>
        match classFields E n csc cls with
        | some cf =>
          let rows := evalObjSet E n sc (some cf) os
          let ok := TableOk E H n sc outer cf rows path refs
          -- 12.7: the type does not inherit the object set's extensibility
          (VSet.plain fun x => parent.root x ∧ ok x).keepExt parent.ext
        | none => .empty
      -- X.682 A.2: on INSTANCE OF, the equivalent constrained sequence type
      | none => match instanceOfOf E n sc pt with
        | some (isc, cls) =>
          (VSet.plain fun x => parent.root x ∧
            (sem E H n sc outer (instanceOfTable (cls.from isc sc) os)).all x).keepExt parent.ext
        | none => .empty
    -- X.682 11.4, 11.6
    | n + 1, sc, _, _, parent, .contents t enc =>
      let tvals : Val → Prop := match t with
        | some t => (sem E H n sc [] t).all
        | none => fun _ => True
      (VSet.plain fun x => parent.root x ∧
        match enc with
        | some e => ∃ w, evalVal E n sc e w ∧ H sc t (some w) tvals x
        | none => H sc t none tvals x).keepExt parent.ext
    | _ + 1, _, _, _, parent, .userDefined =>
      (VSet.ofSpecs false (ESet.userDefined parent.root) none).keepExt parent.ext

  /-- X.682 10.5–10.6, 10.17–10.21, and X.681 12.9: whether `x`, a value of the field `path` of
  class `cf`, satisfies a table constraint with object set `rows`, and, for a component relation
  constraint, the referenced components `refs` among the enclosing values `outer`. -/
  def TableOk (E : Env) (H : ContentsHook) : Nat → Scope → List Frame → Scope × List FieldSpec →
      OSet → List String → List AtRef → Val → Prop
    | 0, _, _, _, _, _, _, _ => False
    | n + 1, _, outer, cf, rows, path, refs, x =>
      -- 10.6: what a cell of the column admits, for the kind of field it is
      let admits (row : ObjV) (p : List String) (v : Val) : Prop :=
        ∃ sc' st, cell E n row p (sc', st) ∧
          match fieldAt E n cf p, st with
          | some (_, .typeField _ _), .type t =>
            ∃ y, v = .open_ t y ∧ (sem E H n sc' [] t).all y
          | some (fsc, .fixedValue _ ft _ _), .value w => ∃ w', evalVal E n sc' w w' ∧ eqv E n fsc ft v w'
          | some (fsc, .fixedValueSet _ ft _), .valueSet c =>
            (cons E H n sc' [] ft (sem E H n fsc [] ft) c).all v
          | some (_, .varValue _ tf _), .value w =>
            ∃ tsc t y, cell E n row tf (tsc, .type t) ∧ v = .open_ t y ∧ evalVal E n sc' w y
          | some (_, .varValueSet _ tf _), .valueSet c =>
            ∃ tsc t y, cell E n row tf (tsc, .type t) ∧ v = .open_ t y ∧
              (cons E H n sc' [] t (sem E H n tsc [] t) c).all y
          | _, _ => False
      -- the referenced components (10.11), each a field of the same class (10.15)
      let refd : List (Option (Val × List String)) := refs.map fun r =>
        (r.resolve E n outer).bind fun (v, rsc, rt) =>
          (classFieldOf E n rsc rt).map fun (_, _, p) => (v, p)
      -- 10.19: a selected row agrees with every referenced component
      let selected (row : ObjV) : Prop := ∀ r ∈ refd, ∃ v p, r = some (v, p) ∧ admits row p v
      -- X.681 12.9: an extensible object set also admits any object of the class whose UNIQUE
      -- fields differ from those of every object in the set
      let fresh : Prop :=
        rows.ext = true ∧ ∀ u ∈ uniqueFields cf.2,
          match refd.find? (fun r => r.map (·.2) == some [u.1]) with
          | some (some (v, _)) => ¬ ∃ row, rows.a row ∧ admits row [u.1] v
          | _ => ∃ w, (sem E H n cf.1 [] u.2).all w ∧ ¬ ∃ row, rows.a row ∧ admits row [u.1] w
      let anyValue : Prop := (sem E H n cf.1 [] (.classField (.defn cf.2) path)).all x
      -- 10.18: every referenced component is present
      (∀ r ∈ refd, r.isSome) ∧
        ((∃ row, rows.a row ∧ selected row ∧ admits row path x) ∨ (fresh ∧ anyValue))

  /-- X.680 50.2, evaluated as 50.5 says. `g` is the governor's root (50.8). -/
  def eset (E : Env) (H : ContentsHook) : Nat → Scope → List Frame → Ty → (Val → Prop) → ElemSet →
      ESet
    | 0, _, _, _, _, _ => .empty
    | n + 1, sc, outer, pt, g, .elem el => elem E H n sc outer pt g el
    | n + 1, sc, outer, pt, g, .union a b => (eset E H n sc outer pt g a).union (eset E H n sc outer pt g b)
    | n + 1, sc, outer, pt, g, .inter a b => (eset E H n sc outer pt g a).inter (eset E H n sc outer pt g b)
    | n + 1, sc, outer, pt, g, .except a b =>
      (eset E H n sc outer pt g a).except (eset E H n sc outer pt g b)
    | n + 1, sc, outer, pt, g, .allExcept b => ESet.allExcept g (eset E H n sc outer pt g b)

  /-- X.680 51: the values one subtype element specifies, among the governor's root `g`. -/
  def elem (E : Env) (H : ContentsHook) : Nat → Scope → List Frame → Ty → (Val → Prop) → Elem → ESet
    | 0, _, _, _, _, _ => .empty
    -- 51.2: the single abstract value written
    | n + 1, sc, _, pt, g, .single v => .fixed fun w => g w ∧ ∃ v', evalVal E n sc v v' ∧ eqv E n sc pt w v'
    -- 51.3.2, 51.3.3: the root values of the type, and none of its extensibility
    | n + 1, sc, _, _, g, .contained t _ => .fixed fun w => g w ∧ (sem E H n sc [] t).root w
    -- 51.4
    | n + 1, sc, _, _, g, .range lo lo' hi hi' =>
      .fixed fun w => g w ∧ ∃ l h, EvalBound E n sc lo l ∧ EvalBound E n sc hi h ∧ RangeHas l lo' h hi' w
    -- 51.5: the constraint applies to INTEGER (0..MAX)
    | n + 1, sc, outer, _, g, .size c => ESet.bySize g (cons E H n sc outer (.integer []) sizeParent c)
    -- 51.6
    | n + 1, _, _, _, g, .typeC t =>
      .fixed fun w => g w ∧ ∃ x, w = .open_ t x ∧ ∃ sc', (sem E H n sc' [] t).all x
    -- 51.7: the constraint applies to the parent type
    | n + 1, sc, outer, pt, g, .from_ c => ESet.byAlphabet g (cons E H n sc outer pt ⟨g, g, false⟩ c)
    -- 51.8.4
    | n + 1, sc, _, pt, g, .withComponent c =>
      match builtin E n sc pt with
      | some (sc', .sequenceOf et) | some (sc', .setOf et) =>
        ESet.byElems g (cons E H n sc' [] et (sem E H n sc' [] et) c)
      | _ => .empty
    -- 51.8.5–51.8.10
    | n + 1, sc, _, pt, g, .withComponents isPartial ncs =>
      match builtin E n sc pt with
      | some (sc', .sequence r e r2) | some (sc', .set r e r2) =>
        ESet.byComponents g (entries E n sc' r e r2) isPartial ncs
          (fun sc'' t c => cons E H n sc'' [] t (sem E H n sc'' [] t) c) (DefaultIs (evalVal E n))
      | some (sc', .choice root ext) =>
        ESet.byAlternatives g sc' (choiceAlts root ext) isPartial ncs
          fun sc'' t c => cons E H n sc'' [] t (sem E H n sc'' [] t) c
      -- 36.5, 37.5, 44.5: through the associated type, whose values these values are
      | some (_, .embeddedPdv) =>
        elem E H n (.ofModule assocModule) [] embeddedPdvAssoc g (.withComponents isPartial ncs)
      | some (_, .external) =>
        elem E H n (.ofModule assocModule) [] externalAssoc g (.withComponents isPartial ncs)
      | some (_, .characterString) =>
        elem E H n (.ofModule assocModule) [] characterStringAssoc g (.withComponents isPartial ncs)
      -- 21.5: through the associated type, whose values denote these values
      | some (_, .real) =>
        ESet.byReal g (elem E H n (.ofModule assocModule) [] realAssoc (fun _ => True)
          (.withComponents isPartial ncs))
      -- 38.4.4.1: on a duration subtype, through DURATION-EQUIVALENT
      | some (_, .time) | some (_, .duration) =>
        ESet.byDuration g (ESet.byComponents (fun _ => True)
          (entries E n (.ofModule assocModule) durationEquivComps none []) isPartial ncs
          fun sc'' t c => cons E H n sc'' [] t (sem E H n sc'' [] t) c)
      | _ => .empty
    -- 51.9
    | _ + 1, _, _, _, g, .pattern re => .fixed fun w => g w ∧ ∃ cs, w.patternChars = some cs ∧ re.Accepts cs
    -- 51.10.5
    | _ + 1, _, _, _, g, .settings ps => .fixed fun w => g w ∧ ∃ t, w = .time t ∧ t.satisfies ps

  /-- An endpoint of a value range, with its value notation evaluated. -/
  def EvalBound (E : Env) : Nat → Scope → Bound → Bound → Prop
    | 0, _, _, _ => False
    | n + 1, sc, .val v, b => ∃ w, evalVal E n sc v w ∧ b = .val w
    | _ + 1, _, b, b' => b' = b
end

/-! ## The definitions the rest of the spec uses

Each takes the encoding rules' contents hook `H` (X.682 11.4). -/

/-- `P` holds for every large enough fuel. -/
def Eventually (P : Nat → Prop) : Prop := ∃ N, ∀ n, N ≤ n → P n

/-- `v` is a value of type `t`, written in module `m` of `E`: a root value or an extension
addition. -/
def Has (E : Env) (H : ContentsHook) (m : Module) (t : Ty) (v : Val) : Prop :=
  Eventually fun n => (sem E H n (.ofModule m) [] t).all v

/-- `v` is a value in the extension root of `t` (50.8). -/
def InRoot (E : Env) (H : ContentsHook) (m : Module) (t : Ty) (v : Val) : Prop :=
  Eventually fun n => (sem E H n (.ofModule m) [] t).root v

/-- `t` is an extensible type (3.8.41). -/
def Extensible (E : Env) (H : ContentsHook) (m : Module) (t : Ty) : Prop :=
  Eventually fun n => (sem E H n (.ofModule m) [] t).ext = true

/-- `v` and `w` are the same abstract value of `t`. -/
def Equiv (E : Env) (m : Module) (t : Ty) (v w : Val) : Prop :=
  Eventually fun n => eqv E n (.ofModule m) t v w

end Asn1.X680
