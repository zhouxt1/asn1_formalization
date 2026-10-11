import Asn1.Parse.Grammar
import Asn1.X680.Semantics

/-!
# From parsed modules to the notation (X.681 7.1, 9–12, X.683 8–9)

The grammar leaves undecided what depends on other modules. This settles it:
1. which names are classes, across modules and their imports;
2. what each assignment is: a type, class, value, value set, object or object set;
3. `X.&f`: a field of a class (X.681 14) or of an object set (15);
4. a field whose type is a class: an object or object set field (X.681 9.11, 9.12);
5. an actual parameter, from its dummy (X.683 9.5);
6. an object in braces, through its class's syntax (X.681 11.5, 11.6, 10).

Value notation is read against its governor afterwards (`Asn1.Parse.Values`), once the modules are
assembled. What cannot be read is left as it is, with a diagnostic.
-/

namespace Asn1.Parse

open Asn1.X680

instance : Inhabited Ty := ⟨.boolean⟩
instance : Inhabited Comp := ⟨.componentsOf .boolean⟩
instance : Inhabited ExtAdd := ⟨.group none []⟩
instance : Inhabited Alt := ⟨.mk "" .boolean⟩
instance : Inhabited AltAdd := ⟨.group none []⟩
instance : Inhabited Constraint := ⟨.userDefined⟩
instance : Inhabited Elem := ⟨.contained .boolean false⟩
instance : Inhabited ElemSet := ⟨.elem default⟩
instance : Inhabited ClassRef := ⟨.typeIdentifier⟩
instance : Inhabited FieldSpec := ⟨.typeField "" none⟩
instance : Inhabited Obj := ⟨.defn []⟩
instance : Inhabited ObjSet := ⟨.spec none false none⟩
instance : Inhabited OElems := ⟨.set default⟩
instance : Inhabited Arg := ⟨.type .boolean⟩
instance : Inhabited Setting := ⟨.type .boolean⟩
instance : Inhabited Val := ⟨.null⟩

/-- X.681 7.1: an "objectclassreference" has no lower-case letters. -/
def allCaps (s : String) : Bool := s.all fun c => !c.isLower

/-! ## 1. Which names are classes -/

/-- The modules, with the class names each assigns. -/
structure Classes where
  mods : List PreModule
  local_ : List (String × List String)

def Classes.mod? (C : Classes) (m : String) : Option PreModule := C.mods.find? (·.name == m)

/-- X.680 13.10, 13.11: the name of the module that module `fromMod` means by `mn`: the one whose
object identifier its import gives, if any has it, otherwise `mn`. -/
def Classes.target (C : Classes) (fromMod : String) (mn : String) : String :=
  match (C.mod? fromMod).bind (fun pm => pm.importOids.find? (·.1 == mn)) with
  | some (_, o) => match C.mods.find? (·.oid == some o) with
    | some pm' => pm'.name
    | none => mn
  | none => mn

/-- Whether `name`, referenced in module `m`, is a class: assigned as one there, or imported from a
module where it is (13.16). -/
def Classes.isClass (C : Classes) : Nat → String → String → Bool
  | 0, _, _ => false
  | k + 1, m, name =>
    -- X.681 Annexes A, B: available without import
    name == "TYPE-IDENTIFIER" || name == "ABSTRACT-SYNTAX" ||
    ((C.local_.find? (·.1 == m)).map (fun (_, ns) => ns.contains name)).getD false ||
    match (C.mod? m).bind (fun pm => pm.imports.find? (·.1 == name)) with
    | some (_, m') => C.isClass k (C.target m m') name
    | none => false

/-- A type notation that is a reference to a class, in module `m`. -/
def Classes.tyIsClass (C : Classes) (m : String) : Ty → Bool
  | .ref n => C.isClass 20 m n
  | .extRef m' n => C.isClass 20 m' n
  | .paramRef none n _ => C.isClass 20 m n
  | .paramRef (some m') n _ => C.isClass 20 m' n
  | _ => false

/-- The class assignments, to a fixed point: `.cls`, and `NAME ::= OTHER` where OTHER is a class. -/
def classesOf (mods : List PreModule) : Classes := Id.run do
  let mut C : Classes := ⟨mods, mods.map fun pm =>
    (pm.name, pm.assigns.filterMap fun a => match a with | .cls n .. => some n | _ => none)⟩
  for _ in [0:10] do
    C := { C with local_ := mods.map fun pm =>
      (pm.name, pm.assigns.filterMap fun a => match a with
        | .cls n .. => some n
        | .type n _ t => if C.tyIsClass pm.name t then some n else none
        | _ => none) }
  return C

/-! ## 2–6. Resolving the notation -/

/-- What a dummy reference stands for (X.683 8.3). -/
inductive DummyKind where
  | type | cls | value | valueSet | obj | objSet
  deriving DecidableEq, Repr

structure RCtx where
  C : Classes
  /-- the module being read -/
  mod : String
  /-- the dummy references in scope -/
  dummies : List (String × DummyKind)
  /-- the classes, resolved: module, name, fields, WITH SYNTAX -/
  classDefs : List (String × String × List FieldSpec × Option (List SynItem))

abbrev R := ReaderT RCtx (StateT (Array String) Id)

def warn (msg : String) : R Unit := do
  let c ← read
  modify (·.push s!"{c.mod}: {msg}")

def R.isClassName (name : String) : R Bool := do
  let c ← read
  match c.dummies.find? (·.1 == name) with
  | some (_, k) => return k == .cls
  | none => return c.C.isClass 20 c.mod name

def R.isClassRef (mn : Option String) (name : String) : R Bool := do
  let c ← read
  match mn with
  | some m => return c.C.isClass 20 m name
  | none => R.isClassName name

/-- The definition of a class reference: its fields and WITH SYNTAX. -/
def R.classDef (cr : ClassRef) : R (Option (String × List FieldSpec × Option (List SynItem))) := do
  let c ← read
  match cr with
  | .defn fs syn => return some (c.mod, fs, syn)
  | .typeIdentifier => return some (c.mod, [.fixedValue "&id" .objectIdentifier true none, .typeField "&Type" none],
      some [.field "&Type", .literal "IDENTIFIED", .literal "BY", .field "&id"])
  | .abstractSyntax => return some (c.mod, abstractSyntaxFields,
      some [.field "&Type", .literal "IDENTIFIED", .literal "BY", .field "&id",
            .optional [.literal "HAS", .literal "PROPERTY", .field "&property"]])
  | .ref mn name _ =>
    -- follow imports to the module that assigns it; the class is that module's
    let rec find (k : Nat) (m : String) : Option (String × List FieldSpec × Option (List SynItem)) :=
      match k with
      | 0 => none
      | k + 1 =>
        match c.classDefs.find? (fun (m', n', _) => m' == m && n' == name) with
        | some (m', _, fs, syn) => some (m', fs, syn)
        | none => match (c.C.mod? m).bind (fun pm => pm.imports.find? (·.1 == name)) with
          | some (_, m') => find k (c.C.target m m')
          | none => none
    return find 20 ((mn.map (c.C.target c.mod)).getD c.mod)

/-- The parameters of a parameterized assignment `name`, referenced from module `m` (with the module
it is in). -/
def R.paramsOf (mn : Option String) (name : String) : R (Option (String × List PreParam)) := do
  let c ← read
  let rec find (k : Nat) (m : String) : Option (String × List PreParam) :=
    match k with
    | 0 => none
    | k + 1 =>
      match (c.C.mod? m).bind (fun pm => pm.assigns.find? (·.name == name)) with
      | some a =>
        let ps := match a with
          | .type _ ps _ | .cls _ ps _ | .valueOrObject _ ps _ _ | .setOrObjectSet _ ps _ _ => ps
        some (m, ps)
      | none => match (c.C.mod? m).bind (fun pm => pm.imports.find? (·.1 == name)) with
        | some (_, m') => find k (c.C.target m m')
        | none => none
  return find 20 ((mn.map (c.C.target c.mod)).getD c.mod)

/-- Run a parser on lexical items inside the resolver. -/
def R.sub {α : Type} (p : P α) (ts : List Tok) : R (Option α) := do
  match (subParse p ts).run #[] with
  | .ok (a, _) => return some a
  | .error e => warn e; return none

/-- X.683 8.3: what a parameter's dummy stands for, from its governor. A dummy with no governor is a
type or a class (X.681 7.1: a class's name has no lower-case letters). -/
def R.paramKind (pp : PreParam) (others : List PreParam) : R DummyKind := do
  match pp.governor with
  | none => return match pp.usage with
    | some true => .cls
    | some false => .type
    -- the body not read as a type: by the spelling a class reference has (X.681 7.1)
    | none => if allCaps pp.name then .cls else .type
  | some g =>
    let isUpperDummy := pp.name.front.isUpper
    let govIsClass ← match g with
      | [.upper n] =>
        -- X.683 8.3: a governor may be another dummy; it is a class if that dummy stands for one
        match others.find? (·.name == n) with
        | some other => pure (other.governor.isNone && allCaps other.name)
        | none => R.isClassName n
      | [.upper m, .sym ".", .upper n] => R.isClassRef (some m) n
      | .kw "CLASS" :: _ => pure true
      | [.kw "TYPE-IDENTIFIER"] | [.kw "ABSTRACT-SYNTAX"] => pure true
      | _ => pure false
    return match govIsClass, isUpperDummy with
      | true, true => .objSet
      | true, false => .obj
      | false, true => .valueSet
      | false, false => .value

/-- A class reference read in module `pm`, made usable from another module: a reference by name
becomes an external reference to `pm` (14.6), which `R.classDef` follows through `pm`'s imports. -/
def qualifyClass (pm : String) : ClassRef → ClassRef
  | .ref none n args => .ref (some pm) n args
  | c => c

/-- The class of a class field type, or of INSTANCE OF (X.682 A.2), through tags and constraints. -/
def tableClass : Ty → Option ClassRef
  | .classField c _ | .instanceOf c => some c
  | .tagged _ _ t | .constrained t _ => tableClass t
  | _ => none

mutual
  partial def rTy : Ty → R Ty
    | .sequence r e r2 => return .sequence (← r.mapM rComp) (← e.mapM (·.mapM rExtAdd)) (← r2.mapM rComp)
    | .set r e r2 => return .set (← r.mapM rComp) (← e.mapM (·.mapM rExtAdd)) (← r2.mapM rComp)
    | .sequenceOf t => return .sequenceOf (← rTy t)
    | .setOf t => return .setOf (← rTy t)
    | .choice r e => return .choice (← r.mapM rAlt) (← e.mapM (·.mapM rAltAdd))
    | .selection n t => return .selection n (← rTy t)
    | .tagged tg k t => return .tagged tg k (← rTy t)
    | .constrained t c => do
      let t' ← rTy t
      -- X.682 10.3: the objects of a table constraint's set are of the parent's class
      match c, tableClass t' with
      | .table os refs, some cls => return .constrained t' (.table (← rObjSetIn (some cls) os) refs)
      | _, _ => return .constrained t' (← rCons c)
    | .paramRef mn n args => return .paramRef mn n (← rArgs mn n args)
    | .classField (.ref mn n args) path => do
      -- X.681 14.1 or 15: a class, or an object set
      if ← R.isClassRef mn n then return .classField (.ref mn n (← rArgs mn n args)) path
      else return .fromObjects (.ref mn n (← rArgs mn n args)) path
    | .classField c path => return .classField (← rClass c) path
    | .fromObjects s path => return .fromObjects (← rObjSet s) path
    | .instanceOf c => return .instanceOf (← rClass c)
    | t => return t

  partial def rComp : Comp → R Comp
    | .mk n t p => return .mk n (← rTy t) p
    | .componentsOf t => return .componentsOf (← rTy t)

  partial def rExtAdd : ExtAdd → R ExtAdd
    | .one c => return .one (← rComp c)
    | .group v cs => return .group v (← cs.mapM rComp)

  partial def rAlt : Alt → R Alt
    | .mk n t => return .mk n (← rTy t)

  partial def rAltAdd : AltAdd → R AltAdd
    | .one a => return .one (← rAlt a)
    | .group v as => return .group v (← as.mapM rAlt)

  partial def rCons : Constraint → R Constraint
    | .mk r e a => return .mk (← rElemSet r) e (← a.mapM rElemSet)
    | .table os refs => return .table (← rObjSet os) refs
    | .contents t e => return .contents (← t.mapM rTy) e
    | .userDefined => return .userDefined

  partial def rElemSet : ElemSet → R ElemSet
    | .elem e => return .elem (← rElem e)
    | .union a b => return .union (← rElemSet a) (← rElemSet b)
    | .inter a b => return .inter (← rElemSet a) (← rElemSet b)
    | .except a b => return .except (← rElemSet a) (← rElemSet b)
    | .allExcept b => return .allExcept (← rElemSet b)

  partial def rElem : Elem → R Elem
    | .contained t inc => return .contained (← rTy t) inc
    | .size c => return .size (← rCons c)
    | .typeC t => return .typeC (← rTy t)
    | .from_ c => return .from_ (← rCons c)
    | .withComponent c => return .withComponent (← rCons c)
    | .withComponents p ncs => return .withComponents p (← ncs.mapM fun (n, c, pr) => do
        return (n, ← c.mapM rCons, pr))
    | e => return e

  partial def rClass : ClassRef → R ClassRef
    | .ref mn n args => return .ref mn n (← rArgs mn n args)
    | .defn fs syn => return .defn (← fs.mapM rField) syn
    | c => return c

  /-- X.681 9.11, 9.12: a field whose "type" is a class is an object or object set field. -/
  partial def rField : FieldSpec → R FieldSpec
    | .typeField n d => return .typeField n (← d.mapM (·.mapM rTy))
    | .fixedValue n t u d => do
      match t with
      -- 9.11: an "ObjectFieldSpec" has no UNIQUE (9.6: only a fixed-type value field is an identifier field)
      | .ref c => if ← R.isClassName c then do
                    if u then warn s!"UNIQUE on the object field {n} (X.681 9.6, 9.11)"
                    return .objectField n (.ref none c []) (d.map fun _ => none)
                  else return .fixedValue n (← rTy t) u d
      | .extRef m c => if ← R.isClassRef (some m) c then do
                         if u then warn s!"UNIQUE on the object field {n} (X.681 9.6, 9.11)"
                         return .objectField n (.ref (some m) c []) (d.map fun _ => none)
                       else return .fixedValue n t u d
      | _ => return .fixedValue n (← rTy t) u d
    | .fixedValueSet n t d => do
      match t with
      | .ref c => if ← R.isClassName c then return .objectSetField n (.ref none c []) (d.map fun _ => none)
                  else return .fixedValueSet n (← rTy t) (← d.mapM (·.mapM rCons))
      | .extRef m c => if ← R.isClassRef (some m) c then return .objectSetField n (.ref (some m) c []) (d.map fun _ => none)
                       else return .fixedValueSet n t (← d.mapM (·.mapM rCons))
      | _ => return .fixedValueSet n (← rTy t) (← d.mapM (·.mapM rCons))
    | f => return f

  partial def rObjSet : ObjSet → R ObjSet
    | .ref mn n args => return .ref mn n (← rArgs mn n args)
    | .spec r e a => return .spec (← r.mapM rOElems) e (← a.mapM rOElems)

  partial def rOElems : OElems → R OElems
    | .obj o => return .obj (← rObj none o)
    | .set s => return .set (← rObjSet s)
    | .fromObjects s p => return .fromObjects (← rObjSet s) p
    | .union a b => return .union (← rOElems a) (← rOElems b)
    | .inter a b => return .inter (← rOElems a) (← rOElems b)
    | .except a b => return .except (← rOElems a) (← rOElems b)

  /-- An object, read through its class `cls` if it is written in braces. -/
  partial def rObj (cls : Option ClassRef) : Obj → R Obj
    | .ref mn n args => return .ref mn n (← rArgs mn n args)
    | .fromObject o p => return .fromObject (← rObj none o) p
    | .raw ts => match cls with
      | some c => readObject c ts
      | none => return .raw ts
    | o => return o

  /-- X.683 9.5: the actual parameters of `mn.name`, read by what their dummies stand for. -/
  partial def rArgs (mn : Option String) (name : String) (args : List Arg) : R (List Arg) := do
    if args.isEmpty then return []
    match ← R.paramsOf mn name with
    | none => warn s!"no parameterized assignment {name}"; return args
    | some (pm, ps) =>
      if ps.length ≠ args.length then
        warn s!"{name} takes {ps.length} parameters, given {args.length}"
      (ps.zip args).mapM fun (pp, a) => do
        match a with
        | .raw ts => readArg pm pp ps ts
        | a => return a

  /-- An actual parameter for dummy `pp` of a parameterized assignment in module `pm`. What the
  dummy stands for is read where the assignment is (X.683 8.3); the actual parameter is read where it
  is written. -/
  partial def readArg (pm : String) (pp : PreParam) (ps : List PreParam) (ts : List Tok) : R Arg := do
    let kind ← withReader (fun c => { c with mod := pm, dummies := [] }) (R.paramKind pp ps)
    match kind with
    | .type =>
      match ← R.sub ty ts with
      | some t => return .type (← rTy t)
      | none => return .raw ts
    | .cls =>
      match ← R.sub classRef ts with
      | some c => return .cls (← rClass c)
      | none => return .raw ts
    | .value =>
      match ← R.sub value ts with
      | some v => return .value (.raw v)
      | none => return .raw ts
    | .valueSet =>
      match ts with
      | .sym "{" :: _ =>
        match ← R.sub (do sym "{"; let c ← elementSetSpecs; sym "}"; return c) ts with
        | some c => return .valueSet (← rCons c)
        | none => return .raw ts
      | _ =>
        -- a reference to a value set (a type, X.680 16.8): the set of its values (ledger X683-2)
        match ← R.sub ty ts with
        | some t => return .valueSet (.mk (.elem (.contained (← rTy t) false)) false none)
        | none => return .raw ts
    | .obj =>
      let gov ← match pp.governor with
        | some g => withReader (fun c => { c with mod := pm, dummies := [] }) (do
            match ← R.sub classRef g with
            | some c => pure (some (qualifyClass pm c))
            | none => pure none)
        | none => pure none
      match ts with
      | .sym "{" :: _ =>
        match ← R.sub (balanced "{" "}") ts with
        | some inner => return .obj (← rObj gov (.raw inner))
        | none => return .raw ts
      | _ =>
        -- a reference to an object, perhaps through object fields (X.681 15 "ObjectFromObject")
        let objP : P Obj := do
          let n ← lower
          if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .field _ => true | _ => false) then
            let _ ← next
            pure (.fromObject (.ref none n []) (← fieldPath))
          else pure (.ref none n [])
        match ← R.sub objP ts with
        | some o => return .obj o
        | none => return .raw ts
    | .objSet =>
      match ts with
      | .sym "{" :: _ =>
        match ← R.sub objSetBraces ts with
        | some s =>
          let gov ← match pp.governor with
            | some g => withReader (fun c => { c with mod := pm, dummies := [] }) (do
                match ← R.sub classRef g with
                | some c => pure (some (qualifyClass pm c))
                | none => pure none)
            | none => pure none
          return .objSet (← rObjSetIn gov s)
        | none => return .raw ts
      | _ =>
        -- a reference to an object set (ledger X683-2)
        let setRef : P (Option String × String × List Arg) := do
          let (mn, n) ← definedName
          if ← isSym "{" then
            let args ← actualParams
            pure (mn, n, args)
          else pure (mn, n, [])
        match ← R.sub setRef ts with
        | some (mn, n, args) => return .objSet (← rObjSet (.ref mn n args))
        | none => return .raw ts

  /-- An object set whose objects are of class `cls`. -/
  partial def rObjSetIn (cls : Option ClassRef) : ObjSet → R ObjSet
    | .spec r e a => return .spec (← r.mapM (rOElemsIn cls)) e (← a.mapM (rOElemsIn cls))
    | s => rObjSet s

  partial def rOElemsIn (cls : Option ClassRef) : OElems → R OElems
    | .obj o => return .obj (← rObj cls o)
    | .union a b => return .union (← rOElemsIn cls a) (← rOElemsIn cls b)
    | .inter a b => return .inter (← rOElemsIn cls a) (← rOElemsIn cls b)
    | .except a b => return .except (← rOElemsIn cls a) (← rOElemsIn cls b)
    | e => rOElems e

  /-- X.681 11.5 "DefaultSyntax" or 11.6 "DefinedSyntax", through the class `cls`. -/
  partial def readObject (cls : ClassRef) (ts : List Tok) : R Obj := do
    match ← R.classDef cls with
    | some (defMod, fs, syn) =>
      -- the fields' types and classes are written in the class's module
      let fs := fs.map fun f => match f with
        | .objectField n c d => .objectField n (qualifyClass defMod c) d
        | .objectSetField n c d => .objectSetField n (qualifyClass defMod c) d
        | f => f
      readObjectWith fs syn ts
    | none =>
      let nm := match cls with
        | .ref mn n _ => (mn.map (· ++ ".")).getD "" ++ n
        | _ => "?"
      warn s!"object of class {nm}, which is not defined"; return .raw ts

  /-- An object read through the fields `fs` and WITH SYNTAX `syn` of its class. -/
  partial def readObjectWith (fs : List FieldSpec) (syn : Option (List SynItem)) (ts : List Tok) : R Obj := do
      let byDefault := match ts with
        | .field _ :: _ => true
        | [] => true
        | _ => false
      if byDefault || syn.isNone then
        -- 11.5: `&f setting, …`
        let parts := splitTopCommas ts
        let settings ← parts.filterMapM fun part => do
          match part with
          | .field f :: rest =>
            let nm := "&" ++ f
            match fs.find? (·.name == nm) with
            | some fspec => match ← readSetting fspec rest with
              | some st => return some (nm, st)
              | none => return none
            | none => warn s!"no field {nm} in the class"; return none
          | _ => warn "a default syntax setting starts with a field name"; return none
        return .defn settings
      else
        match ← R.sub (definedSyntax fs (syn.getD [])) ts with
        | some settings =>
          let settings ← settings.mapM fun (nm, st) => do
            return (nm, ← rSettingFor (fs.find? (·.name == nm)) st)
          return .defn settings
        | none => return .raw ts

  /-- A setting for field `fspec`, from its lexical items (X.681 11.7). -/
  partial def readSetting (fspec : FieldSpec) (ts : List Tok) : R (Option Setting) := do
    match ← R.sub (settingP fspec) ts with
    | some st => return some (← rSettingFor (some fspec) st)
    | none => return none

  /-- A setting of field `fspec`: an object or object set setting is of the field's class (X.681
  11.11, 11.12). -/
  partial def rSettingFor (fspec : Option FieldSpec) (st : Setting) : R Setting := do
    match fspec, st with
    | some (.objectField _ cls _), .object o => return .object (← rObj (some cls) o)
    | some (.objectSetField _ cls _), .objectSet os => return .objectSet (← rObjSetIn (some cls) os)
    | _, st => rSetting st

  partial def rSetting : Setting → R Setting
    | .type t => return .type (← rTy t)
    | .valueSet c => return .valueSet (← rCons c)
    | .object o => return .object (← rObj none o)
    | .objectSet s => return .objectSet (← rObjSet s)
    | st => return st

  /-- X.681 11.7 "Setting" for a field of a given kind (11.8–11.12). -/
  partial def settingP (fspec : FieldSpec) : P Setting := do
    match fspec with
    | .typeField .. => return .type (← ty)
    | .fixedValue .. | .varValue .. => return .value (.raw (← value))
    | .fixedValueSet .. | .varValueSet .. =>
      sym "{"; let c ← elementSetSpecs; sym "}"; return .valueSet c
    | .objectField .. =>
      if ← isSym "{" then return .object (.raw (← balanced "{" "}"))
      else return .object (.ref none (← lower) [])
    | .objectSetField .. =>
      if ← isSym "{" then return .objectSet (← objSetBraces)
      else let (mn, n) ← definedName; return .objectSet (.ref mn n [])

  /-- X.681 10: read lexical items through a class's WITH SYNTAX. An optional group is taken when
  its first item, a literal (10.10), is next. -/
  partial def definedSyntax (fs : List FieldSpec) (items : List SynItem) : P (List (String × Setting)) := do
    let rec go (items : List SynItem) (acc : Array (String × Setting)) : P (Array (String × Setting)) := do
      match items with
      | [] => return acc
      | .literal w :: rest =>
        let t ← next
        let ok := match t with
          | .upper s | .kw s => s == w
          | .sym s => s == w
          | _ => false
        if ok then go rest acc else fail s!"expected {w} (WITH SYNTAX)"
      | .field f :: rest =>
        match fs.find? (·.name == f) with
        | some fspec => go rest (acc.push (f, ← settingP fspec))
        | none => fail s!"WITH SYNTAX names no field {f}"
      | .optional grp :: rest =>
        let starts : P Bool := match grp with
          | .literal w :: _ => do
            match ← peek with
            | some (.upper s) | some (.kw s) | some (.sym s) => return s == w
            | _ => return false
          | _ => return true
        if ← starts then
          let acc ← go grp acc
          go rest acc
        else go rest acc
    return (← go items #[]).toList
end

/-! ## Assembling the modules -/

/-- X.683 8.3: the parameters, with their governors read. -/
def rParams (ps : List PreParam) : R (List Param) :=
  ps.mapM fun pp => do
    match pp.governor with
    | none => return ⟨none, pp.name⟩
    | some g =>
      match g with
      | [.upper n] =>
        if ps.any (·.name == n) then return ⟨some (.dummy n), pp.name⟩
        else if ← R.isClassName n then return ⟨some (.cls (.ref none n [])), pp.name⟩
        else match ← R.sub ty g with
          | some t => return ⟨some (.type (← rTy t)), pp.name⟩
          | none => return ⟨none, pp.name⟩
      | .kw "CLASS" :: _ | [.kw "TYPE-IDENTIFIER"] | [.kw "ABSTRACT-SYNTAX"] =>
        match ← R.sub classRef g with
        | some c => return ⟨some (.cls (← rClass c)), pp.name⟩
        | none => return ⟨none, pp.name⟩
      | _ =>
        match ← R.sub ty g with
        | some t => return ⟨some (.type (← rTy t)), pp.name⟩
        | none => return ⟨none, pp.name⟩

/-- The dummies of a parameter list, with what they stand for. -/
def dummiesOf (ps : List PreParam) : R (List (String × DummyKind)) :=
  ps.mapM fun pp => do return (pp.name, ← R.paramKind pp ps)

/-- Run a resolver step inside a parameterized assignment's scope. -/
def withDummies {α : Type} (ps : List PreParam) (k : R α) : R α := do
  let ds ← dummiesOf ps
  withReader (fun c => { c with dummies := ds ++ c.dummies }) k

/-- The class of a type notation that names one. -/
def tyAsClass : Ty → Option ClassRef
  | .ref "TYPE-IDENTIFIER" => some .typeIdentifier
  | .ref "ABSTRACT-SYNTAX" => some .abstractSyntax
  | .ref n => some (.ref none n [])
  | .extRef m n => some (.ref (some m) n [])
  | .paramRef mn n args => some (.ref mn n args)
  | _ => none

/-- One module, resolved. -/
def resolveModule (pm : PreModule) : R Module := do
  let mut m : Module := { name := pm.name, header := pm.header, imports := pm.imports,
                          oid := pm.oid, importOids := pm.importOids, exports := pm.exports,
                          importMods := pm.importMods, exceptionRefs := pm.exceptionRefs,
                          unusedDummies := pm.unusedDummies }
  for a in pm.assigns do
    match a with
    | .cls n ps c =>
      let c ← withDummies ps (rClass c)
      if ps.isEmpty then m := { m with classes := m.classes ++ [(n, c)] }
      else m := { m with params := m.params ++ [.cls n (← rParams ps) c] }
    | .type n ps t =>
      let isCls := (← read).C.tyIsClass pm.name t
      if isCls then
        let c := (tyAsClass t).getD .typeIdentifier
        let c ← withDummies ps (rClass c)
        if ps.isEmpty then m := { m with classes := m.classes ++ [(n, c)] }
        else m := { m with params := m.params ++ [.cls n (← rParams ps) c] }
      else
        let t ← withDummies ps (rTy t)
        if ps.isEmpty then m := { m with types := m.types ++ [(n, t)] }
        else m := { m with params := m.params ++ [.type n (← rParams ps) t] }
    | .valueOrObject n ps gov rhs =>
      let gIsCls ← withDummies ps (match tyAsClass gov with
        | some (.ref mn c _) => R.isClassRef mn c
        | some .typeIdentifier | some .abstractSyntax => pure true
        | _ => pure false)
      if gIsCls then
        let cls := (tyAsClass gov).getD .typeIdentifier
        let o ← withDummies ps (do
          match rhs with
          | .sym "{" :: _ =>
            match ← R.sub (balanced "{" "}") rhs with
            | some inner => rObj (some cls) (.raw inner)
            | none => pure (.raw rhs)
          | _ =>
            -- X.681 11.3 "DefinedObject": `o`, `M.o` (14.6), or `o { … }`
            let objRef : P (Option String × String × List Arg) := do
              let mn ← match ← peek with
                | some (.upper m) => do let _ ← next; sym "."; pure (some m)
                | _ => pure none
              let n ← lower
              if ← isSym "{" then
                let args ← actualParams
                pure (mn, n, args)
              else pure (mn, n, [])
            match ← R.sub objRef rhs with
            | some (mn, n', args) => rObj none (.ref mn n' args)
            | none => pure (.raw rhs))
        if ps.isEmpty then m := { m with objects := m.objects ++ [(n, cls, o)] }
        else m := { m with params := m.params ++ [.obj n (← rParams ps) cls o] }
      else
        let v ← match ← R.sub value rhs with
          | some v => pure (Val.raw v)
          | none => pure (Val.raw (.braces []))
        let gov ← withDummies ps (rTy gov)
        if ps.isEmpty then m := { m with values := m.values ++ [(n, gov, v)] }
        else m := { m with params := m.params ++ [.value n (← rParams ps) gov v] }
    | .setOrObjectSet n ps gov rhs =>
      let gIsCls ← withDummies ps (match tyAsClass gov with
        | some (.ref mn c _) => R.isClassRef mn c
        | some .typeIdentifier | some .abstractSyntax => pure true
        | _ => pure false)
      if gIsCls then
        let cls := (tyAsClass gov).getD .typeIdentifier
        let s ← withDummies ps (do
          match rhs with
          | .sym "{" :: _ =>
            match ← R.sub objSetBraces rhs with
            | some s => rObjSetIn (some cls) s
            | none => pure (.spec none false none)
          | _ => match ← R.sub (do let (mn, n) ← definedName; pure (mn, n)) rhs with
            | some (mn, n') => rObjSet (.ref mn n' [])
            | none => pure (.spec none false none))
        if ps.isEmpty then m := { m with objectSets := m.objectSets ++ [(n, cls, s)] }
        else m := { m with params := m.params ++ [.objSet n (← rParams ps) cls s] }
      else
        let c ← withDummies ps (do
          match rhs with
          | .sym "{" :: _ =>
            match ← R.sub (do sym "{"; let c ← elementSetSpecs; sym "}"; pure c) rhs with
            | some c => rCons c
            | none => pure (.mk (.elem (.contained gov false)) false none)
          | _ => do
            -- 16.7 "ValueSet ::= "{" ElementSetSpecs "}"": braces are required
            warn s!"{n}: a value set is written in braces (X.680 16.7)"
            pure (.mk (.elem (.contained gov false)) false none))
        let gov ← withDummies ps (rTy gov)
        -- X.680 16.8: a value set assignment is a type assignment
        if ps.isEmpty then m := { m with types := m.types ++ [(n, .constrained gov c)] }
        else m := { m with params := m.params ++ [.valueSet n (← rParams ps) gov c] }
  return m

/-- The class definitions of every module, resolved (fields that are classes made object and object
set fields), so that objects can be read through them. -/
def classDefsOf (C : Classes) : List (String × String × List FieldSpec × Option (List SynItem)) :=
  let direct := C.mods.flatMap fun pm => pm.assigns.filterMap fun a =>
    match a with
    | .cls n _ (.defn fs syn) =>
      let ctx : RCtx := ⟨C, pm.name, [], []⟩
      let (fs', _) := ((fs.mapM rField).run ctx).run #[]
      some (pm.name, n, fs', syn)
    -- X.681 Annex A: TYPE-IDENTIFIER
    | .cls n _ .typeIdentifier =>
      some (pm.name, n, [.fixedValue "&id" .objectIdentifier true none, .typeField "&Type" none],
        some [.field "&Type", .literal "IDENTIFIED", .literal "BY", .field "&id"])
    | _ => none
  -- a class defined as another class (X.681 9.2 a)): the other's definition, to a fixed point
  let aliases := C.mods.flatMap fun pm => pm.assigns.filterMap fun a =>
    match a with
    | .type n _ (.ref o) | .cls n _ (.ref none o _) => some (pm.name, n, pm.name, o)
    | .type n _ (.extRef m o) | .cls n _ (.ref (some m) o _) => some (pm.name, n, C.target pm.name m, o)
    | _ => none
  let rec close (k : Nat) (defs : List (String × String × List FieldSpec × Option (List SynItem))) :=
    match k with
    | 0 => defs
    | k + 1 =>
      let more := aliases.filterMap fun (m, n, m', o) =>
        if defs.any (fun (dm, dn, _) => dm == m && dn == n) then none
        else
          -- the other class, assigned in `m'` or imported there
          let target := match (C.mod? m').bind (fun pm => pm.imports.find? (·.1 == o)) with
            | some (_, m'') => C.target m' m''
            | none => m'
          (defs.find? (fun (dm, dn, _) => (dm == m' || dm == target) && dn == o)).map
            fun (_, _, fs, syn) => (m, n, fs, syn)
      if more.isEmpty then defs else close k (defs ++ more)
  close 10 direct

/-- Every module, resolved, with the diagnostics. -/
def resolveAll (mods : List PreModule) : Env × Array String :=
  let C := classesOf mods
  let defs := classDefsOf C
  mods.foldl (fun (E, ws) pm =>
    let (m, ws') := ((resolveModule pm).run ⟨C, pm.name, [], defs⟩).run ws
    (E ++ [m], ws')) ([], #[])

end Asn1.Parse
