import Asn1.X680.Size

/-!
# The validity rules as programs

`Env.Valid` is a proposition. These are the rules it is made of that decide by computation, written
as functions to `Bool` so that they run on real specifications: distinct names (`NamesOk`,
`AssignedOnce`), distinct tags (`TagsOk`), IMPLICIT and the additions under automatic tagging
(`AutoAdditionsOk`), and references (`RefsOk`), over every type that occurs in an assignment
(`Occurs`). Each mirrors its rule clause by clause; proving each equal to its rule is to do.
-/

namespace Asn1.X680

/-- `Occurs t s`: every `s`, listed (the constructors of `Occurs`). -/
def occurrences (t : Ty) : List Ty :=
  t :: match t with
    | .sequence r e r2 | .set r e r2 =>
      (r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2).attach.flatMap fun ⟨c, h⟩ => match c, h with
        | .mk _ t _, h | .componentsOf t, h => occurrences t
    | .sequenceOf t | .setOf t | .selection _ t | .tagged _ _ t => occurrences t
    | .constrained t c => occurrences t ++ (consTypes c).attach.flatMap fun ⟨u, h⟩ => occurrences u
    | .choice r e => (choiceAlts r e).attach.flatMap fun ⟨a, h⟩ => match a, h with
      | .mk _ t, h => occurrences t
    -- X.683 9.2: a type written as an actual parameter is a type of the module like any other
    | .paramRef _ _ args => args.attach.flatMap fun ⟨a, h⟩ => match a, h with
      | .type t, h => occurrences t
      | _, _ => []
    | _ => []
decreasing_by all_goals decr_syntax

def namesOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .sequence r e r2 | .set r e r2 => decide ((entries E n sc r e r2).map (·.name)).Nodup
  | .choice r e => decide ((choiceAlts r e).map (·.name)).Nodup
  | .integer named => decide (named.map (·.1)).Nodup && decide (named.map (·.2)).Nodup
  | .bitString named => decide (named.map (·.1)).Nodup && decide (named.map (·.2)).Nodup
  | .enumerated r e =>
    let nums := enumNumbers r e
    decide (nums.map (·.1)).Nodup && decide (nums.map (·.2)).Nodup &&
      decide (((nums.drop r.length).map (·.2)).Pairwise (· < ·))
  | _ => true

/-- Every COMPONENTS OF in `cs` (and in the components it brings, `expand`) is of a SEQUENCE or SET
type that resolves: `expand` then lists all the components. It does not when one goes through a
dummy reference (X.683 8.3), which a parameterized body is checked with bound to nothing, or names
what does not exist (which `refsOkB` reports). -/
def expandKnown (E : Env) : Nat → Scope → List Comp → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | n + 1, sc, .mk .. :: rest => expandKnown E n sc rest
  | n + 1, sc, .componentsOf t :: rest =>
    (match builtin E n sc t with
     | some (sc', .sequence r _ r2) | some (sc', .set r _ r2) => expandKnown E n sc' (r ++ r2)
     | _ => false) && expandKnown E n sc rest

/-- `entries` lists all the components (`expandKnown`). The rules about all of them (distinct tags,
the names WITH COMPONENTS and an @ may use) are decided only then. -/
def entriesKnown (E : Env) (n : Nat) (sc : Scope) (root : List Comp) (ext : Option (List ExtAdd))
    (root2 : List Comp) : Bool :=
  expandKnown E n sc root && (ext.getD []).all (fun e => expandKnown E n sc e.comps) &&
    expandKnown E n sc root2

/-- `structComps` (and `compsOf`) list all the components of `t` (`entriesKnown`). -/
def structKnown (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Bool :=
  match builtin E n sc t with
  | some (sc', .sequence r e r2) | some (sc', .set r e r2) => entriesKnown E n sc' r e r2
  | _ => true

/-- `RunsDistinct`: for each `i`, each `j` after it reached through OPTIONAL or DEFAULT components
only, the tags of `i` and `j` do not clash. -/
def runsDistinctB (series : List (List CTag × Bool)) : Bool :=
  let arr := series.toArray
  (List.range arr.size).all fun i =>
    let rec go (j : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | k + 1 =>
        if j ≥ arr.size then true
        else
          (arr[i]!.1.all fun t => arr[j]!.1.all fun u => !t.clash u) &&
            (if arr[j]!.2 then go (j + 1) k else true)
    -- a run starts with an OPTIONAL or DEFAULT component (k = i)
    if arr[i]!.2 then go (i + 1) arr.size else true

def tagsDistinctB (ts : List CTag) : Bool :=
  let rec go : List CTag → Bool
    | [] => true
    | t :: rest => rest.all (fun u => !t.clash u) && go rest
  go ts

mutual
  /-- `tagsOf` where it is known: `none` when a reference on the way does not resolve (a dummy of a
  parameterized body, which the checker binds to nothing, or what the reference rules report), and
  then the type takes no part in the rules on tags. `some none` is an indeterminate tag. -/
  def tagsOfB (E : Env) : Nat → Scope → Ty → Option (Option (List Tag))
    | 0, _, _ => none
    | _ + 1, _, .tagged tg _ _ => some (some [tg])
    | n + 1, sc, .ref name => (resolveTy E n sc none name []).bind fun (sc', t) => tagsOfB E n sc' t
    | n + 1, sc, .extRef mn name => (resolveTy E n sc (some mn) name []).bind fun (sc', t) => tagsOfB E n sc' t
    | n + 1, sc, .paramRef mn name args => (resolveTy E n sc mn name args).bind fun (sc', t) => tagsOfB E n sc' t
    | n + 1, sc, .constrained t _ => tagsOfB E n sc t
    | n + 1, sc, .selection nm t => match builtin E n sc t with
      | some (sc', .choice root ext) => (findAlt (choiceAlts root ext) nm).bind fun a => tagsOfB E n sc' a.ty
      | _ => none
    | n + 1, sc, .choice root ext =>
      ((altTagsB E n sc root ext).map (·.2)).foldr
        (fun ts acc => match ts, acc with
          | some x, some y => some (match x, y with
            | some a, some b => some (a ++ b)
            | _, _ => none)
          | _, _ => none) (some (some []))
    | _ + 1, _, .openType => some none
    | n + 1, sc, .classField cls path =>
      match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => tagsOfB E n sc' t
      | some _ => some none
      | none => none
    | _ + 1, _, .instanceOf _ => some (some [⟨.universal, 8⟩])
    | n + 1, sc, .fromObjects src path => match objSetClass E n sc src with
      | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
        | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => tagsOfB E n sc' t
        | some _ => some none
        | none => none
      | none => none
    | _ + 1, _, t => some (some ((t.universalTag?.map fun k => [⟨.universal, k⟩]).getD []))

  /-- `altTags`, with `tagsOfB`. -/
  def altTagsB (E : Env) : Nat → Scope → List Alt → Option (List AltAdd) →
      List (Alt × Option (Option (List Tag)))
    | 0, _, root, ext => (choiceAlts root ext).map fun a => (a, none)
    | n + 1, sc, root, ext =>
      let alts := choiceAlts root ext
      if autoChoice sc.mod.header.tagDefault root ext then
        (alts.zip (autoNumber (root.map (fun _ => false) ++
            (alts.drop root.length).map (fun _ => true)))).map
          fun (a, k) => (a, some (some [⟨.context, k⟩]))
      else alts.map fun a => (a, tagsOfB E n sc a.ty)
end

/-- `entryTags`, with `tagsOfB`. -/
def entryTagsB (E : Env) (n : Nat) (sc : Scope) (root : List Comp) (ext : Option (List ExtAdd))
    (root2 : List Comp) : List (Entry × Option (Option (List Tag))) :=
  let es := entries E n sc root ext root2
  if autoSeq sc.mod.header.tagDefault root ext root2 then
    (es.zip (autoNumber (es.map (·.addition.isSome)))).map fun (e, k) => (e, some (some [⟨.context, k⟩]))
  else es.map fun e => (e, tagsOfB E n e.scope e.ty)

/-- `TagsOk`: the components or alternatives whose tags are known (`tagsOfB`), the others taking no
part. -/
def tagsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .sequence r e r2 =>
    let et := entryTagsB E n sc r e r2
    let auto := autoSeq sc.mod.header.tagDefault r e r2
    let ect (x : Entry × Option (Option (List Tag))) : List CTag := match x.2 with
      | some o => ctags o ++ if !auto && carriesConceptual E n x.1.scope x.1.ty then [.conceptual] else []
      | none => []
    let item (x : Entry × Option (Option (List Tag))) : List CTag × Bool := (ect x, !x.1.presence.isMandatory)
    let roots := et.filter (·.1.addition.isNone)
    let adds := et.filter (·.1.addition.isSome)
    let tail := et.drop (et.length - (entries E n sc [] none r2).length)
    let insert := (conceptual sc.mod e.isSome).map fun t => ([t], true)
    -- 25.7: the trailing root components up to and including the first mandatory one
    let firstRun := (tail.takeWhile (fun y => !y.1.presence.isMandatory)) ++
      ((tail.dropWhile (fun y => !y.1.presence.isMandatory)).take 1)
    !entriesKnown E n sc r e r2 ||
    runsDistinctB (roots.map item) &&
    runsDistinctB ((et.take (et.length - tail.length)).map item ++ insert ++ tail.map item) &&
    adds.all fun a => firstRun.all fun x => (ect a).all fun t => (ect x).all fun u => !t.clash u
  | .set r e r2 =>
    let et := entryTagsB E n sc r e r2
    let auto := autoSeq sc.mod.header.tagDefault r e r2
    let ect (x : Entry × Option (Option (List Tag))) : List CTag := match x.2 with
      | some o => ctags o ++ if !auto && carriesConceptual E n x.1.scope x.1.ty then [.conceptual] else []
      | none => []
    !entriesKnown E n sc r e r2 ||
    tagsDistinctB ((et.flatMap ect) ++ conceptual sc.mod e.isSome) &&
    decide (((et.filter (·.1.addition.isSome)).filterMap fun x => match x.2 with
      | some (some [t]) => some t
      | _ => none).Pairwise (fun a b => a.lt b))
  | .choice r e =>
    let at' := altTagsB E n sc r e
    let auto := autoChoice sc.mod.header.tagDefault r e
    let act (x : Alt × Option (Option (List Tag))) : List CTag := match x.2 with
      | some o => ctags o ++ if !auto && carriesConceptual E n sc x.1.ty then [.conceptual] else []
      | none => []
    tagsDistinctB ((at'.flatMap act) ++ conceptual sc.mod e.isSome) &&
    decide (((at'.drop r.length).filterMap fun x => match x.2 with
      | some (some [t]) => some t
      | _ => none).Pairwise (fun a b => a.lt b))
  | .tagged _ .implicit t => !untaggedChoiceOrOpen E n sc t
  | _ => true

def autoAdditionsOkB (sc : Scope) : Ty → Bool
  | .sequence r e r2 | .set r e r2 =>
    !(sc.mod.header.tagDefault == .automatic && !(r ++ r2).any Comp.textuallyTagged) ||
      !((e.getD []).flatMap ExtAdd.comps).any Comp.textuallyTagged
  | .choice r e =>
    !(sc.mod.header.tagDefault == .automatic && !r.any (fun a => a.ty.textuallyTagged)) ||
      !((choiceAlts r e).drop r.length).any (fun a => a.ty.textuallyTagged)
  | _ => true

def refsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  -- X.683 8.4: a dummy reference (inside a parameterized assignment) is a reference, and it is
  -- not parameterized itself
  | .ref name => (sc.bound name).isSome || (resolveTy E n sc none name []).isSome
  | .paramRef none name args => (sc.bound name).isNone && (resolveTy E n sc none name args).isSome
  | .extRef mn name => (resolveTy E n sc (some mn) name []).isSome
  | .paramRef mn name args => (resolveTy E n sc mn name args).isSome
  -- a selected type that does not resolve is for the rules on it to report (a dummy of a
  -- parameterized body is bound to nothing)
  | .selection nm t => match builtin E n sc t with
    | some (_, .choice r e) => (findAlt (choiceAlts r e) nm).isSome
    | some _ => false
    | none => true
  | _ => true

/-- X.680 13.16 a): each imported symbol is assigned in the module it is imported from, or present
once in that module's imports (and then not assigned there). -/
def importsOkB (E : Env) (m : Module) : List String :=
  m.imports.filterMap fun (sym, mn) =>
    match E.findFrom m mn with
    | none => some s!"{sym} (module {mn} not found)"
    | some m' =>
      if m'.assignedNames.contains sym then none
      else if (m'.imports.filter (·.1 == sym)).length == 1 then none
      else some s!"{sym} (not assigned in {mn})"

/-- The value references a value notation uses (X.680 14.1, 16.2), outside open types. -/
def valRefs : Val → List (Option String × String × List Arg)
  | .ref mn n args => [(mn, n, args)]
  | .seq cs => cs.attach.flatMap fun ⟨(f, v), h⟩ => valRefs v
  | .seqOf vs | .setOf vs => vs.attach.flatMap fun ⟨v, h⟩ => valRefs v
  | .choice _ v => valRefs v
  | _ => []
decreasing_by all_goals decr_syntax

def valRefsOkB (E : Env) (n : Nat) (sc : Scope) (v : Val) : Bool :=
  (valRefs v).all fun (mn, nm, args) =>
    (mn.isNone && args.isEmpty && (sc.bound nm).isSome) || (resolveVal E n sc mn nm args).isSome

mutual
  /-- The values a subtype constraint uses (X.680 51.2, 51.4, 51.5, 51.7). -/
  def consVals : Constraint → List Val
    | .mk r _ (some a) => esVals r ++ esVals a
    | .mk r _ none => esVals r
    | _ => []
  def esVals : ElemSet → List Val
    | .elem e => elVals e
    | .union a b | .inter a b | .except a b => esVals a ++ esVals b
    | .allExcept b => esVals b
  def elVals : Elem → List Val
    | .single v => [v]
    | .range lo _ hi _ => boundVals lo ++ boundVals hi
    | .size c | .from_ c => consVals c
    | _ => []
  def boundVals : Bound → List Val
    | .val v => [v]
    | _ => []
end

/-- X.680 14.1, 51: each value reference in a constraint names a value, where the constrained
type resolves. -/
def consRefsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained t c => (builtin E n sc t).isNone || (consVals c).all (valRefsOkB E n sc)
  | _ => true

/-- A name the module assigns or imports: it exists, whether or not what it names can be read
(its class may come from a module that is missing, which 13.16 a) reports). -/
def Scope.knows (sc : Scope) : Option String → String → Bool
  | none, nm => (sc.bound nm).isSome || sc.mod.assignedNames.contains nm || sc.mod.imports.any (·.1 == nm)
  | some _, _ => true

/-- A name that does not resolve to a thing of the kind sought but may still stand for one: a dummy
reference whose governor allows it (`gov`, X.683 8.3), or an imported symbol (its module may be
missing, which 13.16 a) reports). An external reference (`M.x`, 14.6) either resolves or names
nothing: its module is missing or does not have it. -/
def Scope.mayBe (sc : Scope) (gov : Option ParamGov → Bool) : Option String → String → Bool
  | none, nm => match sc.bound nm with
    | some (_, g, _) => gov g
    | none => sc.mod.imports.any (·.1 == nm)
  | some _, _ => false

/-- X.683 8.3: the governors of a dummy for a class (none), an object or object set (a class, or a
dummy governor), a value or value set (a type, or a dummy governor). -/
def govClass : Option ParamGov → Bool | none => true | _ => false
def govObjects : Option ParamGov → Bool | some (.cls _) | some (.dummy _) => true | _ => false

/-- `true` when a path of field names certainly names no field of the class (X.681 9.14): a name is
not a field of a class on the way, every class on the way resolving. -/
def fieldMissingB (E : Env) : Nat → Scope × List FieldSpec → List String → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | _ + 1, (_, fs), [f] => (fs.find? (·.name == f)).isNone
  | n + 1, (sc, fs), f :: rest => match fs.find? (·.name == f) with
    | some (.objectField _ c _) | some (.objectSetField _ c _) => match classFields E n sc c with
      | some cf => fieldMissingB E n cf rest
      | none => false
    | _ => true

/-- X.681 14.1, Annex C, X.680 14.1: the class `X.&f` and `INSTANCE OF X` name is assigned or imported. -/
def classRefsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .instanceOf (.ref mn name args) =>
    (resolveClass E n sc mn name args).isSome || sc.mayBe govClass mn name
  | .classField cls path =>
    (match cls with
      | .ref mn name args => (resolveClass E n sc mn name args).isSome || sc.mayBe govClass mn name
      | _ => true) &&
    (match classFields E n sc cls with
      -- X.681 9.14: the field names a field of the class (through object fields)
      | some r => !fieldMissingB E n r path
      | none => true)
  | _ => true

/-- X.681 9.4: what the fields of a class definition name exists: the class of an object or object set
field, and the type field a variable-type field names. -/
def classDefOkB (E : Env) (n : Nat) (sc : Scope) : ClassRef → Bool
  | .defn fs _ => fs.all fun f => match f with
    | .objectField _ (.ref mn name args) _ | .objectSetField _ (.ref mn name args) _ =>
      (resolveClass E n sc mn name args).isSome || sc.mayBe govClass mn name
    -- the types of the fields are among the module's types (`moduleTypes`), checked with them
    -- 9.8, 9.10: `&v &T` takes the type of the type field `&T` of this class
    | .varValue _ [p] _ | .varValueSet _ [p] _ =>
      fs.any fun g => match g with | .typeField q _ => q == p | _ => false
    | _ => true
  | _ => true

/-- X.683 8.3, X.680 14.1: the body of a parameterized type names types and classes that exist, or
that are dummy references of the type. -/
def paramBodyOkB (E : Env) (n : Nat) (sc : Scope) : ParamAssign → Bool
  | .type _ ps body =>
    let dum := ps.map (·.name)
    (occurrences body).all fun t => match t with
      | .ref nm => dum.contains nm || sc.knows none nm
      | .classField (.ref none c args) _ | .instanceOf (.ref none c args) =>
        dum.contains c || (resolveClass E n sc none c args).isSome || sc.knows none c
      | .fromObjects (.ref none c _) _ => dum.contains c || sc.knows none c
      | _ => true
  | _ => true

/-- X.681 12, 15; X.682 10: the objects and object sets an object set names exist. -/
def oelemsRefsOkB (E : Env) (n : Nat) (sc : Scope) : OElems → Bool
  | .obj (.ref mn nm args) => (resolveObj E n sc mn nm args).isSome || sc.mayBe govObjects mn nm
  | .set s | .fromObjects s _ => objSetRefsOkB E n sc s
  | .union a b | .inter a b | .except a b => oelemsRefsOkB E n sc a && oelemsRefsOkB E n sc b
  | _ => true
where
  objSetRefsOkB (E : Env) (n : Nat) (sc : Scope) : ObjSet → Bool
    | .ref mn nm args => (resolveObjSet E n sc mn nm args).isSome || sc.mayBe govObjects mn nm
    | .spec (some r) _ (some a) => oelemsRefsOkB E n sc r && oelemsRefsOkB E n sc a
    | .spec (some r) _ none => oelemsRefsOkB E n sc r
    | .spec none _ (some a) => oelemsRefsOkB E n sc a
    | .spec none _ none => true

/-- X.683 9.2: the value an actual parameter gives names a value, where the module's own parameterized
type says what governs it. An enumeration item or a named number is not a reference. -/
def argsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .paramRef mn name args =>
    -- X.681 11.3, 12.3: an object or object set given as an actual parameter names what exists
    (args.all fun a => match a with
      | .obj o => oelemsRefsOkB E n sc (.obj o)
      | .objSet os => oelemsRefsOkB.objSetRefsOkB E n sc os
      | _ => true) &&
    match mn with
    | some _ => true
    | none =>
    match sc.mod.params.find? fun pa => match pa with | .type nm .. => nm == name | _ => false with
    | some pa =>
      let ps := pa.paramList
      (args.zip ps).all fun (a, p) => match a, p.governor with
        | .value v, some (.type t) =>
          (match builtin E n sc t with
            | some (_, .enumerated ..) => true
            | some (_, .integer (_ :: _)) => true
            | some _ => valRefsOkB E n sc v
            -- a governor that does not resolve (a dummy): its identifiers are not decided
            | none => true)
        | _, _ => true
    | none => true
  | _ => true

/-- X.682 10.3: a table constraint's object set exists. -/
def tableRefsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained _ (.table os _) => oelemsRefsOkB.objSetRefsOkB E n sc os
  | _ => true

/-- X.681 15: the object set `S.&Type` or `{ o }.&Type` takes a column from exists (when `S` names no class). -/
def typeFromObjectsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .fromObjects os _ => oelemsRefsOkB.objSetRefsOkB E n sc os
  | _ => true

/-- X.681 15.4, 15.5 Table 1, for "InformationFromObjects" written as a type: from an object, a type
field ("TypeFromObject") or a fixed-type value set field; from an object set, a fixed-type value or
value set field ("ValueSetFromObjects"). Whether the first part (15.4) is an object or an object
set follows its form (`obj.&f`, `Set.&f`) and then each object set field on the path. Not decided
when the class or a field does not resolve. -/
def typeFromObjectsTableB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .fromObjects src path => match objSetClass E n sc src with
    | some (csc, cls) => match classFields E n csc cls with
      | some cf =>
        let viaSet := (List.range (path.length - 1)).any fun i =>
          match fieldAt E n cf (path.take (i + 1)) with
          | some (_, .objectSetField ..) => true
          | _ => false
        let isSet := (match src with | .ref .. => true | _ => false) || viaSet
        match fieldAt E n cf path with
        | some (_, .fixedValueSet ..) => true
        | some (_, .typeField ..) => !isSet
        | some (_, .fixedValue ..) => isSet
        | some _ => false
        | none => true
      | none => true
    | none => true
  | _ => true

/-- The type a table constraint is applied to is an "ObjectClassFieldType" or an "InstanceOfType"
(X.682 10.1), through references, tags and other constraints. Not decided when a reference does
not resolve. -/
def tableTargetB (E : Env) : Nat → Scope → Ty → Bool
  | 0, _, _ => true
  | _ + 1, _, .classField .. | _ + 1, _, .instanceOf _ => true
  | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
    | some (sc', t) => tableTargetB E n sc' t
    | none => true
  | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => tableTargetB E n sc' t
    | none => true
  | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
    | some (sc', t) => tableTargetB E n sc' t
    | none => true
  | n + 1, sc, .tagged _ _ t | n + 1, sc, .constrained t _ => tableTargetB E n sc t
  | _ + 1, _, _ => false

/-- X.682 10.4, 10.15: the object set of a table constraint is of the class of the
"ObjectClassFieldType" it constrains (decided where both classes resolve to named classes). -/
def tableClassB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained (.classField cls _) (.table os _) =>
    match objSetClass E n sc os.unwrap with
    | some (osc, c') => match classKey E n sc cls, classKey E n osc c' with
      | some a, some b => a == b
      | _, _ => true
    | none => true
  | _ => true

def tableOnFieldB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained t (.table ..) => tableTargetB E n sc t
  | _ => true

/-! ## INTEGER values against constraints, where that can be decided

`Semantics.Has` says when a value is a value of a type; it is not computable. These functions
decide the INTEGER part of it that a front end must check (25.12, 16.2, 50.10, 50.11): single
values, ranges and their set arithmetic, through value references, tags and type references.
`none` (and, for `intNotInTy`, `false`) means "not decided here": the rules below reject only
what they decide is outside. -/

/-- The integer a value denotes, through value references (at most `k` of them). -/
def intOfV (E : Env) (n : Nat) (sc : Scope) : Nat → Val → Option Int
  | _, .int i => some i
  | k + 1, .ref mn nm args => match resolveVal E n sc mn nm args with
    | some (sc', v) => intOfV E n sc' k v
    | none => none
  | _, _ => none

def orB : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

def andB : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- A decision on whether a value is in an element set, as `ESet` holds the set (50.5): in its
root, and in it with its additions. `none`: not decided. -/
abbrev Dec := Option Bool × Option Bool

/-- 50.2 b), 50.4 b), 50.5 (`ESet.union`) -/
def Dec.union (x y : Dec) : Dec := (orB x.1 y.1, orB (orB x.1 y.1) (orB x.2 y.2))
/-- 50.2 c) (`ESet.inter`) -/
def Dec.inter (x y : Dec) : Dec := (andB x.1 y.1, orB (andB x.1 y.1) (andB x.2 y.2))
/-- 50.2 d) (`ESet.except`) -/
def Dec.except (x y : Dec) : Dec :=
  (andB x.1 (y.1.map (!·)), orB (andB x.1 (y.1.map (!·))) (andB x.2 (y.2.map (!·))))
/-- 50.2 a) (`ESet.allExcept`), for a value of the governor -/
def Dec.allExcept (y : Dec) : Dec := (y.1.map (!·), y.1.map (!·))
/-- 49.6 (`VSet.ofSpecs`): the root, and the values with the additions. -/
def Dec.ofSpecs (r : Dec) (a : Option Dec) : Dec :=
  (r.1, match a with | some a => orB r.2 a.2 | none => r.2)

/-- An element set, decided element by element. -/
def decES (el : Elem → Dec) : ElemSet → Dec
  | .elem e => el e
  | .union a b => (decES el a).union (decES el b)
  | .inter a b => (decES el a).inter (decES el b)
  | .except a b => (decES el a).except (decES el b)
  | .allExcept b => (decES el b).allExcept

/-- A constraint, decided by its element sets: its root, and its values with its additions. -/
def decCons (es : ElemSet → Dec) : Constraint → Dec
  | .mk r _ a => Dec.ofSpecs (es r) (a.map es)
  | _ => (none, none)

/-- 51.2 SingleValue, 51.4 ValueRange: whether `i` is in an element, if decided. -/
def intInElem (E : Env) (n : Nat) (sc : Scope) (i : Int) : Elem → Option Bool
  | .single v => (intOfV E n sc 8 v).map (· == i)
  | .range lo loOpen hi hiOpen =>
    let a : Option Bool := match lo with
      | .min => some true
      | .max => none
      | .val v => (intOfV E n sc 8 v).map fun l => if loOpen then decide (l < i) else decide (l ≤ i)
    let b : Option Bool := match hi with
      | .max => some true
      | .min => none
      | .val v => (intOfV E n sc 8 v).map fun h => if hiOpen then decide (i < h) else decide (i ≤ h)
    andB a b
  | _ => none

/-- Whether `i` is in an element set (X.680 50), if decided. -/
def intInES (E : Env) (n : Nat) (sc : Scope) (i : Int) : ElemSet → Dec :=
  decES fun e => let d := intInElem E n sc i e; (d, d)

/-- Whether `i` satisfies a constraint: its root, and with `withAdds` its additions too. -/
def intInCons (E : Env) (n : Nat) (sc : Scope) (i : Int) (withAdds : Bool) (c : Constraint) :
    Option Bool :=
  let d := decCons (intInES E n sc i) c
  if withAdds then d.2 else d.1

def isIntTy (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Bool :=
  match builtin E n sc t with
  | some (_, .integer _) => true
  | _ => false

/-- `true` when a value is certainly not a value of `t`, as `dec sc w c` decides it against each
constraint `c` on the way: the outermost with its additions when `withAdds` (25.12), those under it
with their roots only, as serial application drops a parent's extensions (50.11); through tags and
type references. -/
def notInTy (E : Env) (n : Nat) (dec : Scope → Bool → Constraint → Option Bool) :
    Nat → Scope → Ty → Bool → Bool
  | 0, _, _, _ => false
  | k + 1, sc, .constrained t c, w => dec sc w c == some false || notInTy E n dec k sc t false
  | k + 1, sc, .tagged _ _ t, w => notInTy E n dec k sc t w
  | k + 1, sc, .ref nm, w => match resolveTy E n sc none nm [] with
    | some (sc', t) => notInTy E n dec k sc' t w
    | none => false
  | k + 1, sc, .extRef mn nm, w => match resolveTy E n sc (some mn) nm [] with
    | some (sc', t) => notInTy E n dec k sc' t w
    | none => false
  | _, _, _, _ => false

/-- `true` when `i` is certainly not a value of the INTEGER type `t`. -/
def intNotInTy (E : Env) (n : Nat) (k : Nat) (sc : Scope) (t : Ty) (i : Int) (w : Bool) : Bool :=
  notInTy E n (fun sc w c => intInCons E n sc i w c) k sc t w

/-- `v` is not certainly outside the INTEGER type `t` (other types: not decided here). -/
def intValOkB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  !(isIntTy E n sc t) ||
    match intOfV E n vsc 8 v with
    | some i => !(intNotInTy E n 16 sc t i true)
    | none => true

/-- Whether a length satisfies the SIZE elements of an element set (X.680 51.5), if decided: other
elements (a permitted alphabet, a pattern) are not decided here. The constraint inside SIZE counts
with its additions where the set does (`ESet.bySize`). -/
def sizeInES (E : Env) (n : Nat) (sc : Scope) (len : Nat) : ElemSet → Dec :=
  decES fun e => match e with
    | .size c => decCons (intInES E n sc len) c
    | _ => (none, none)

def sizeInCons (E : Env) (n : Nat) (sc : Scope) (len : Nat) (withAdds : Bool) (c : Constraint) :
    Option Bool :=
  let d := decCons (sizeInES E n sc len) c
  if withAdds then d.2 else d.1

/-- `true` when a value of length `len` is certainly not a value of `t`, by its SIZE constraints. -/
def sizeNotInTy (E : Env) (n : Nat) (k : Nat) (sc : Scope) (t : Ty) (len : Nat) (w : Bool) : Bool :=
  notInTy E n (fun sc w c => sizeInCons E n sc len w c) k sc t w

/-- `v` is not certainly outside `t` by its length. A BIT STRING with a NamedBitList may take
trailing 0 bits (X.680 22: encoding rules may add or drop them), so there a value shorter than the
SIZE allows is not rejected, only one no padding can bring into it. -/
def sizeValOkB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) : Bool :=
  match v.size?, builtin E n sc t with
  | some len, some (_, bt) =>
    let named := match bt with
      | .bitString nb => !nb.isEmpty
      | _ => false
    if named then (List.range 65).any fun d => !(sizeNotInTy E n 16 sc t (len + d) true)
    else !(sizeNotInTy E n 16 sc t len true)
  | _, _ => true

/-! ## Character string values against PATTERN, FROM and single values, where that can be decided -/

/-- `k` rounds of `step`, from `ps`. -/
def iterOpt (step : List Nat → Option (List Nat)) : Nat → List Nat → Option (List Nat)
  | 0, ps => some ps
  | k + 1, ps => step ps >>= iterOpt step k

/-- `acc`, and `k` more rounds of `step` from `f`, each added to `acc`. -/
def upToOpt (step : List Nat → Option (List Nat)) : Nat → List Nat → List Nat → Option (List Nat)
  | 0, _, acc => some acc
  | k + 1, f, acc => step f >>= fun f' => upToOpt step k f' (acc ++ f').eraseDups

/-- The least set holding `acc` closed under `step`, if `k` rounds reach it. -/
def closureOpt (step : List Nat → Option (List Nat)) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | k + 1, acc => step acc >>= fun s =>
    if s.all (acc.contains ·) then some acc else closureOpt step k (acc ++ s).eraseDups

/-- The positions at which a match of `re` that starts at `i` in `w` can end (`Matches re w i j`),
or `none` when a repetition count is too large to try (more than 1000). -/
def patEnds (w : List Nat) : Regex → Nat → Option (List Nat)
  | .cls neg rs, i => some (match w[i]? with
    | some c => if Regex.clsMem neg rs c then [i + 1] else []
    | none => [])
  | .boundary, i =>
    some (if decide ((i = 0 ∨ isWordAt w (i - 1) = false) ≠ (isWordAt w i = false)) then [i] else [])
  | .cat a b, i => patEnds w a i >>= fun ks => (ks.mapM (patEnds w b)).map (·.flatten.eraseDups)
  | .alt a b, i => patEnds w a i >>= fun xs => (patEnds w b i).map fun ys => (xs ++ ys).eraseDups
  | .rep a lo hi, i =>
    -- `Times a k`: the positions after exactly k matches of `a`
    let step (ps : List Nat) : Option (List Nat) := (ps.mapM (patEnds w a)).map (·.flatten.eraseDups)
    if lo > 1000 then none else
    iterOpt step lo [i] >>= fun f =>
    match hi with
    -- any number of further matches
    | none => closureOpt step (w.length + 2) f
    | some m => if m > 1000 then none else upToOpt step (m - lo) f (if lo ≤ m then f else [])

/-- X.680 51.9.2: whether the whole string matches, if decided. -/
def patAccepts (re : Regex) (w : List Nat) : Option Bool :=
  (patEnds w re 0).map (·.contains w.length)

/-- The characters a string value denotes, through value references (at most `k` of them). -/
def charsOfV (E : Env) (n : Nat) (sc : Scope) : Nat → Val → Option (List Nat)
  | _, .chars cs => some cs
  | k + 1, .ref mn nm args => match resolveVal E n sc mn nm args with
    | some (sc', v) => charsOfV E n sc' k v
    | none => none
  | _, _ => none

/-- An end of a range in a permitted alphabet: `some none` for MIN or MAX, `some (some x)` for the
one-character string of `x`, `none` when not known. -/
def charBound (E : Env) (n : Nat) (sc : Scope) : Bound → Option (Option Nat)
  | .min | .max => some none
  | .val v => match charsOfV E n sc 8 v with
    | some [x] => some (some x)
    | _ => none

/-- `true` when the character `c` is certainly in no string of the element set inside FROM (X.680
51.7): in no single value, outside every range of one-character values. -/
def alphaNo (E : Env) (n : Nat) (sc : Scope) (c : Nat) : ElemSet → Bool
  | .elem (.single v) => match charsOfV E n sc 8 v with
    | some cs => !cs.contains c
    | none => false
  | .elem (.range lo loOpen hi hiOpen) =>
    match charBound E n sc lo, charBound E n sc hi with
    | some l, some h =>
      !((l.all fun l => if loOpen then l < c else l ≤ c) && (h.all fun h => if hiOpen then c < h else c ≤ h))
    | _, _ => false
  | .elem _ => false
  | .union a b => alphaNo E n sc c a && alphaNo E n sc c b
  | .inter a b => alphaNo E n sc c a || alphaNo E n sc c b
  | .except a _ => alphaNo E n sc c a
  | .allExcept _ => false

/-- Whether the string `cs` is in an element set, by its PATTERN, FROM, SIZE and single value
elements, if decided. FROM decides only that a string is outside (`alphaNo`). -/
def charsInES (E : Env) (n : Nat) (sc : Scope) (cs : List Nat) : ElemSet → Dec :=
  decES fun e => match e with
    | .single v => let d := (charsOfV E n sc 8 v).map (· == cs); (d, d)
    | .pattern re => let d := patAccepts re cs; (d, d)
    | .size c => decCons (intInES E n sc cs.length) c
    | .from_ (.mk r _ a) =>
      (if cs.any (alphaNo E n sc · r) then some false else none,
       if cs.any (fun c => alphaNo E n sc c r && a.all (alphaNo E n sc c ·)) then some false else none)
    | _ => (none, none)

def charsInCons (E : Env) (n : Nat) (sc : Scope) (cs : List Nat) (withAdds : Bool) (c : Constraint) :
    Option Bool :=
  let d := decCons (charsInES E n sc cs) c
  if withAdds then d.2 else d.1

/-- `true` when the string `cs` is certainly not a value of `t`. -/
def charsNotInTy (E : Env) (n : Nat) (k : Nat) (sc : Scope) (t : Ty) (cs : List Nat) (w : Bool) : Bool :=
  notInTy E n (fun sc w c => charsInCons E n sc cs w c) k sc t w

/-- `v` is not certainly outside the restricted character string type `t` (16.2, 51.2, 51.7,
51.9); other types are not decided here. -/
def charsValOkB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  match builtin E n sc t with
  | some (_, .restricted _) => match charsOfV E n vsc 8 v with
    | some cs => !(charsNotInTy E n 16 sc t cs true)
    | none => true
  | _ => true

/-- `v`, written in scope `vsc`, is a value of a type with a value mapping to `t` (C.6.1), as far
as built-in types tell, if it is a value reference (`RefMaps`). -/
def refMapsB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  match v with
  | .ref mn nm args => match resolveValTy E n vsc mn nm args, (builtin E n sc t).bind (mapName ·.2) with
    | some (usc, u), some p => match (builtin E n usc u).bind (mapName ·.2) with
      | some q => p == q
      | none => true
    | _, _ => true
  | _ => true

/-- `refMapsB` for a value and the values of its components (`ValMaps`). -/
def valMapsB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  refMapsB E n sc t v vsc &&
  match v with
  | .seq cs => match builtin E n sc t with
    | some (sc', .sequence ro e r2) | some (sc', .set ro e r2) =>
      let es := entries E n sc' ro e r2
      !entriesKnown E n sc' ro e r2 || cs.attach.all fun ⟨(nm, w), h⟩ => match es.find? (·.name == nm) with
        | some en => valMapsB E n en.scope en.ty w vsc
        | none => true
    | _ => true
  | .seqOf vs | .setOf vs => match builtin E n sc t with
    | some (sc', .sequenceOf el) | some (sc', .setOf el) => vs.attach.all fun ⟨w, h⟩ => valMapsB E n sc' el w vsc
    | _ => true
  | .choice a w => match builtin E n sc t with
    | some (sc', .choice ro ext) => match findAlt (choiceAlts ro ext) a with
      | some alt => valMapsB E n sc' alt.ty w vsc
      | none => true
    | _ => true
  | _ => true
termination_by v
decreasing_by all_goals decr_syntax

/-- `builtin`, where the values of the type are those of the built-in type: not through a type from
objects, whose values are those of the objects' settings (X.681 15), nor to a type field, an open
type. -/
def builtinV (E : Env) : Nat → Scope → Ty → Option (Scope × Ty)
  | 0, _, _ => none
  | n + 1, sc, .ref name => (resolveTy E n sc none name []).bind fun (sc', t) => builtinV E n sc' t
  | n + 1, sc, .extRef mn name =>
    (resolveTy E n sc (some mn) name []).bind fun (sc', t) => builtinV E n sc' t
  | n + 1, sc, .paramRef mn name args =>
    (resolveTy E n sc mn name args).bind fun (sc', t) => builtinV E n sc' t
  | n + 1, sc, .tagged _ _ t => builtinV E n sc t
  | n + 1, sc, .constrained t _ => builtinV E n sc t
  | n + 1, sc, .selection nm t =>
    match builtin E n sc t with
    | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
      | some a => builtinV E n sc' a.ty
      | none => none
    | _ => none
  | n + 1, sc, .classField cls path =>
    match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
    | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => builtinV E n sc' t
    | _ => none
  | n + 1, sc, .instanceOf cls => builtinV E n sc (instanceOfTy cls)
  | _ + 1, _, .fromObjects .. => none
  | _ + 1, sc, t => some (sc, t)

/-- 46.3, 47.3: a GeneralizedTime or UTCTime value is a string of the format they give. -/
def timeFmtOkB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  match builtinV E n sc t with
  | some (_, .generalizedTime) => (charsOfV E n vsc 8 v).all fun cs => Notation.generalizedTimeOk (cs.map Char.ofNat)
  | some (_, .utcTime) => (charsOfV E n vsc 8 v).all fun cs => Notation.utcTimeOk (cs.map Char.ofNat)
  | _ => true

/-- `v`, written in scope `vsc`, is not certainly outside the type `t` read in `sc`: INTEGER
ranges, sizes, character string constraints and time formats, through the components of SEQUENCE,
SET, CHOICE, SEQUENCE OF and SET OF values. A component's value is held against each component of
its name (one, in a valid type), where the components are known. -/
def valSemB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  intValOkB E n sc t v vsc && sizeValOkB E n sc t v && charsValOkB E n sc t v vsc &&
  timeFmtOkB E n sc t v vsc &&
  match v with
  | .seq cs => match builtinV E n sc t with
    | some (sc', .sequence ro e r2) | some (sc', .set ro e r2) =>
      let es := entries E n sc' ro e r2
      !entriesKnown E n sc' ro e r2 ||
      cs.attach.all fun ⟨(nm, w), h⟩ =>
        !(es.any (·.name == nm)) || es.any fun en => en.name == nm && valSemB E n en.scope en.ty w vsc
    | _ => true
  | .seqOf vs | .setOf vs => match builtinV E n sc t with
    | some (sc', .sequenceOf el) | some (sc', .setOf el) => vs.attach.all fun ⟨w, h⟩ => valSemB E n sc' el w vsc
    | _ => true
  | .choice a w => match builtinV E n sc t with
    | some (sc', .choice ro ext) =>
      let alts := choiceAlts ro ext
      !(alts.any (·.name == a)) || alts.any fun alt => alt.name == a && valSemB E n sc' alt.ty w vsc
    | _ => true
  | _ => true
termination_by v
decreasing_by all_goals decr_syntax

/-- `v`, written in scope `vsc`, is not certainly outside the type `t` read in `sc` (`valSemB`),
and its value references map to the types of where they stand (`valMapsB`). -/
def valOkB (E : Env) (n : Nat) (sc : Scope) (t : Ty) (v : Val) (vsc : Scope := sc) : Bool :=
  valMapsB E n sc t v vsc && valSemB E n sc t v vsc

/-- X.680 25.12: a DEFAULT value is a value of the component's type. -/
def defaultsInTypeB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .sequence r e r2 | .set r e r2 =>
    (r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2).all fun c => match c with
      | .mk _ t (.default_ v) => valOkB E n sc t v
      | _ => true
  | _ => true

/-- X.681 11 (11.5, 11.6): an object gives every mandatory field of its class a setting. Decided
for objects already read into settings, of a class whose fields resolve. -/
def objFieldsOkB (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) : Obj → Bool
  | .defn settings => match classFields E n sc cls with
    | some (_, fs) => fs.all fun f => !f.mandatory || settings.any (·.1 == f.name)
    | none => true
  | _ => true

/-- The objects written out in an object set, each checked against the set's class. -/
def oelemsFieldsOkB (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) : OElems → Bool
  | .obj o => objFieldsOkB E n sc cls o
  | .set (.spec (some r) _ (some a)) => oelemsFieldsOkB E n sc cls r && oelemsFieldsOkB E n sc cls a
  | .set (.spec (some r) _ none) => oelemsFieldsOkB E n sc cls r
  | .set (.spec none _ (some a)) => oelemsFieldsOkB E n sc cls a
  | .union a b | .inter a b | .except a b => oelemsFieldsOkB E n sc cls a && oelemsFieldsOkB E n sc cls b
  | _ => true

/-- The component names each WITH COMPONENTS of an element set constrains (X.680 51.8). -/
def esWithComps : ElemSet → List (List String)
  | .elem (.withComponents _ cs) => [cs.map (·.1)]
  | .elem _ => []
  | .union a b | .inter a b | .except a b => esWithComps a ++ esWithComps b
  | .allExcept b => esWithComps b

/-- X.680 51.8.6: a NamedConstraint identifies a component of the parent type, and names it at
most once. -/
def innerNamesOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained t (.mk r _ a) =>
    let lists := esWithComps r ++ (a.map esWithComps).getD []
    if lists.isEmpty then true else
    let ok (names : List String) : Bool :=
      lists.all fun l => l.all (names.contains ·) && decide l.Nodup
    match builtin E n sc t with
    | some (sc', .sequence ro e r2) | some (sc', .set ro e r2) =>
      !entriesKnown E n sc' ro e r2 || ok ((entries E n sc' ro e r2).map (·.name))
    | some (_, .choice ro e) => ok ((choiceAlts ro e).map (·.name))
    | _ => true
  | _ => true

/-- Every element of an element set, through its set arithmetic. -/
def esElems : ElemSet → List Elem
  | .elem e => [e]
  | .union a b | .inter a b | .except a b => esElems a ++ esElems b
  | .allExcept b => esElems b

/-- The elements of a constraint's root and additions. -/
def consElems : Constraint → List Elem
  | .mk r _ a => esElems r ++ (a.map esElems).getD []
  | _ => []

/-- The integers an element names that are values it selects: a single value, and the closed ends
of a range that lie in the range. -/
def intPoints (E : Env) (n : Nat) (sc : Scope) : Elem → List Int
  | .single v => (intOfV E n sc 8 v).toList
  | .range lo loOpen hi hiOpen =>
    let l := match lo with | .val v => intOfV E n sc 8 v | _ => none
    let h := match hi with | .val v => intOfV E n sc 8 v | _ => none
    let inLo (i : Int) : Bool := match lo with
      | .min => true
      | .max => false
      | .val _ => l.any fun l => if loOpen then decide (l < i) else decide (l ≤ i)
    let inHi (i : Int) : Bool := match hi with
      | .max => true
      | .min => false
      | .val _ => h.any fun h => if hiOpen then decide (i < h) else decide (i ≤ h)
    (if loOpen then [] else (l.filter inHi).toList) ++ (if hiOpen then [] else (h.filter inLo).toList)
  | _ => []

/-- `true` unless a value of the constraint `c` on the INTEGER type `pt` is certainly outside the
root of `pt` (50.10, 50.11, 51.2.1, 51.4.2): its single values, and the ends of its ranges that are
in the range. -/
def intConsValsOkB (E : Env) (n : Nat) (sc : Scope) (pt : Ty) (c : Constraint) : Bool :=
  !(isIntTy E n sc pt) ||
    (consElems c).all fun el => (intPoints E n sc el).all fun i => !(intNotInTy E n 16 sc pt i false)

/-- X.680 50.10, 50.11: the values a constraint on a constrained parent uses are values of the
parent's extension root. -/
def serialValsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained t c => intConsValsOkB E n sc t c
  | _ => true

/-- `isIntTy`, where the values of the type are integers (`builtinV`). -/
def isIntTyV (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Bool :=
  match builtinV E n sc t with
  | some (_, .integer _) => true
  | _ => false

/-- X.680 49.7: an INTEGER element set (with its additions) has an element, if decided. It is a
finite union of intervals whose ends are the numbers it writes, so it is empty exactly when no number
next to one of them (or below or above them all) is in it. -/
def intNonEmptyB (E : Env) (n : Nat) (sc : Scope) (root : ElemSet) (adds : Option ElemSet) : Bool :=
  let ks := (esVals root ++ (adds.map esVals).getD []).filterMap (intOfV E n sc 8)
  let lo := ks.foldl min 0
  let hi := ks.foldl max 0
  let cands := [lo - 2, hi + 2] ++ ks.flatMap fun k => [k - 1, k, k + 1]
  let inSet (i : Int) : Option Bool :=
    (Dec.ofSpecs (intInES E n sc i root) (adds.map (intInES E n sc i))).2
  !(cands.all fun i => inSet i == some false)

/-- X.680 49.7 for a restricted character string type, where the element set is built from single
values by union, intersection and EXCEPT (no ALL EXCEPT): it is a subset of those values, so it is
empty exactly when none of them is in it. Decided where every single value is known. -/
def charsNonEmptyB (E : Env) (n : Nat) (sc : Scope) (root : ElemSet) (adds : Option ElemSet) : Bool :=
  let rec onlySingles : ElemSet → Bool
    | .elem (.single _) => true
    | .elem _ | .allExcept _ => false
    | .union a b | .inter a b | .except a b => onlySingles a && onlySingles b
  if !(onlySingles root && (adds.map onlySingles).getD true) then true else
  let vals := esVals root ++ (adds.map esVals).getD []
  let cands := vals.filterMap (charsOfV E n sc 8)
  if cands.length != vals.length then true else
  let inSet (cs : List Nat) : Option Bool :=
    (Dec.ofSpecs (charsInES E n sc cs root) (adds.map (charsInES E n sc cs))).2
  !(cands.all fun cs => inSet cs == some false)

/-- `true` when an element set certainly selects nothing, with its additions or without, by SIZE
elements whose constraint selects no length (`ESet.bySize`). -/
def sizeEmptyB (E : Env) (n : Nat) (sc : Scope) : ElemSet → Bool
  | .elem (.size (.mk r _ a)) => !intNonEmptyB E n sc r a
  | .elem _ => false
  | .union a b => sizeEmptyB E n sc a && sizeEmptyB E n sc b
  | .inter a b => sizeEmptyB E n sc a || sizeEmptyB E n sc b
  | .except a _ => sizeEmptyB E n sc a
  | .allExcept _ => false

mutual
  /-- `ConsOk` (Validity: X.680 51.1, Table 11, Table 12) as far as computation decides it: an
  element whose parent does not resolve to a built-in type is not decided. Also X.682 11.3: a
  contents constraint is on a BIT STRING or OCTET STRING type. -/
  def consOkB (E : Env) (n : Nat) (sc : Scope) (pt : Ty) (inPA : Bool) : Constraint → Bool
    | .mk root _ adds => esOkB E n sc pt inPA root &&
      (match adds with | some a => esOkB E n sc pt inPA a | none => true)
    | .contents .. => match builtin E n sc pt with
      | some (_, .bitString _) | some (_, .octetString) | none => true
      | some _ => false
    | _ => true

  termination_by c => sizeOf c
  decreasing_by all_goals decr_syntax

  def esOkB (E : Env) (n : Nat) (sc : Scope) (pt : Ty) (inPA : Bool) : ElemSet → Bool
    | .elem el => elemOkB E n sc pt inPA el
    | .union a b | .inter a b | .except a b => esOkB E n sc pt inPA a && esOkB E n sc pt inPA b
    | .allExcept b => esOkB E n sc pt inPA b

  termination_by s => sizeOf s
  decreasing_by all_goals decr_syntax

  def elemOkB (E : Env) (n : Nat) (sc : Scope) (pt : Ty) (inPA : Bool) (el : Elem) : Bool :=
    match builtin E n sc pt with
    | none => true
    | some (sc', bt) => match rowOf bt with
      | none => true
      | some r =>
        -- Table 11, Table 12, and note a)
        (r.allows el.kind || (match r with
          | .restricted k => k.knownOrder && inPA && el.kind == .range
          | _ => false)) &&
        -- 51.7.3: within a permitted alphabet, only these four
        (!inPA || el.kind ∈ [.single, .contained, .range, .size]) &&
        match el with
        -- 51.2.1: a value of the parent type (C.6.1)
        | .single v => refMapsB E n sc pt v
        -- 51.4.4 NOTE: in a permitted alphabet, each end is one character
        | .range lo _ hi _ =>
          let one (b : Bound) : Bool := match b with
            | .val v => (charsOfV E n sc 8 v).all (·.length == 1)
            | _ => true
          let maps (b : Bound) : Bool := match b with
            | .val v => refMapsB E n sc pt v
            | _ => true
          (!inPA || (one lo && one hi)) && maps lo && maps hi
        -- 51.3.2: derived from the same built-in type
        | .contained t _ => match (builtin E n sc t).bind (rowOf ·.2) with
          | some r' => r == r'
          | none => true
        -- 51.5.3: the size constraint is on INTEGER (0..MAX)
        | .size c => c.isSubtype && consOkB E n sc sizeParentTy false c && intConsValsOkB E n sc sizeParentTy c
        -- 51.7.2: the alphabet constraint is on the parent type; 51.7.3
        | .from_ c => c.isSubtype && consOkB E n sc pt true c
        | .withComponent c => match bt with
          | .sequenceOf et | .setOf et => consOkB E n sc' et false c
          | _ => false
        -- 51.8.6: each named constraint names a component of the type (or of its associated
        -- type), at most once; its constraint is one on (each) component of the name
        | .withComponents _ ncs =>
          let (isc, it) := innerTarget sc' bt
          let comps := structComps E n isc it
          decide (ncs.map (·.1)).Nodup && (comps.isEmpty || !structKnown E n isc it ||
            ncs.attach.all fun ⟨(nm, oc, p), h⟩ => comps.any (·.1 == nm) && match oc, h with
              | some c, h => comps.any fun x => x.1 == nm && consOkB E n x.2.1 x.2.2 false c
              | none, _ => true)
        -- 51.10.3, 51.10.4, 51.10.6
        | .settings ps => settingsOk ps
        | _ => true
  termination_by sizeOf el
  decreasing_by all_goals decr_syntax
end

/-- `ConsOk`, and X.680 49.7: the constraint selects some value, where decided. -/
def constraintKindsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained t c => consOkB E n sc t false c &&
    match c with
    | .mk root _ adds =>
      (!isIntTyV E n sc t || intNonEmptyB E n sc root adds) &&
      (match builtin E n sc t with
        | some (_, .restricted _) => charsNonEmptyB E n sc root adds
        | _ => true) &&
      !(sizeEmptyB E n sc root && adds.all (sizeEmptyB E n sc))
    | _ => true
  | _ => true

/-- X.680 25.5, 27.2: the type of COMPONENTS OF is a sequence type in a SEQUENCE and a set type in a
SET (where it resolves). -/
def componentsOfOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .sequence r e r2 => (r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2).all fun c => match c with
    | .componentsOf t => match builtin E n sc t with
      | some (_, .sequence ..) | none => true
      | some _ => false
    | _ => true
  | .set r e r2 => (r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2).all fun c => match c with
    | .componentsOf t => match builtin E n sc t with
      | some (_, .set ..) | none => true
      | some _ => false
    | _ => true
  | _ => true

/-- X.680 31.2.5: the class of a tag is not UNIVERSAL (except in the types the Recommendation
defines, which a module cannot be). -/
def universalTagOkB : Ty → Bool
  | .tagged ⟨.universal, _⟩ _ _ => false
  | _ => true

/-- The presence constraints each WITH COMPONENTS of an element set writes (X.680 51.8.10). -/
def esWithPres : ElemSet → List (List (String × PresenceC))
  | .elem (.withComponents _ cs) => [cs.map fun (nm, _, p) => (nm, p)]
  | .elem _ => []
  | .union a b | .inter a b | .except a b => esWithPres a ++ esWithPres b
  | .allExcept b => esWithPres b

/-- X.680 51.8.10.1: of the components of a SEQUENCE or SET, only one marked OPTIONAL (or DEFAULT)
is constrained to be PRESENT or ABSENT. -/
def presenceOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .constrained t (.mk r _ a) =>
    let lists := esWithPres r ++ (a.map esWithPres).getD []
    match builtin E n sc t with
    | some (sc', .sequence ro e r2) | some (sc', .set ro e r2) =>
      let es := entries E n sc' ro e r2
      !entriesKnown E n sc' ro e r2 || lists.all fun l => l.all fun (nm, p) =>
        (match p with | .present | .absent => false | _ => true) ||
        es.any (fun en => en.name == nm && !en.presence.isMandatory) ||
        -- a name the type does not have is for `innerNamesOkB` to report
        !es.any (·.name == nm)
    | _ => true
  | _ => true

/-- X.680 14.1, 16.2: each value reference in a DEFAULT names a value. -/
def defaultRefsOkB (E : Env) (n : Nat) (sc : Scope) : Ty → Bool
  | .sequence r e r2 | .set r e r2 =>
    (r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2).all fun c => match c with
      -- only where the governing type resolves: otherwise an identifier may be a named number
      -- or an enumeration item of a type we cannot see (a missing module)
      | .mk _ t (.default_ v) => (builtin E n sc t).isNone || valRefsOkB E n sc v
      | _ => true
  | _ => true

/-- X.681 11.7, X.680 14.1: the value, object and object set references an object's settings use
name what exists. Decided
where the object's class resolves (the settings were then read against the fields' types). -/
def objValRefsOkB (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) : Obj → Bool
  | .defn settings => (classFields E n sc cls).isNone ||
    settings.all fun (_, st) => match st with
      | .value v => valRefsOkB E n sc v
      | .object o => oelemsRefsOkB E n sc (.obj o)
      | .objectSet s => oelemsRefsOkB.objSetRefsOkB E n sc s
      | _ => true
  | _ => true

def oelemsValRefsOkB (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) : OElems → Bool
  | .obj o => objValRefsOkB E n sc cls o
  | .set (.spec (some r) _ (some a)) => oelemsValRefsOkB E n sc cls r && oelemsValRefsOkB E n sc cls a
  | .set (.spec (some r) _ none) => oelemsValRefsOkB E n sc cls r
  | .set (.spec none _ (some a)) => oelemsValRefsOkB E n sc cls a
  | .union a b | .inter a b | .except a b => oelemsValRefsOkB E n sc cls a && oelemsValRefsOkB E n sc cls b
  | _ => true

/-- X.683 8.3, X.680 14.1: the class that governs a parameter (`{ IE-CLASS : Set }`) is a class of the
module, an imported one, or an earlier parameter's dummy; and the type that governs one resolves. -/
def paramGovsOkB (E : Env) (n : Nat) (sc : Scope) (pa : ParamAssign) : Bool :=
  let ps := pa.paramList
  ps.all fun p => match p.governor with
    | some (.cls (.ref mn name args)) =>
      (resolveClass E n sc mn name args).isSome || sc.mayBe govClass mn name || ps.any (·.name == name)
    | some (.type t) => (occurrences t).all (refsOkB E n sc)
    | _ => true

/-- X.680 13.13 a): each exported symbol is assigned in the module, or appears exactly once in its
imports (and is then not assigned in it). -/
def exportsOkB (m : Module) : List String :=
  (m.exports.getD []).filter fun sym =>
    !(m.assignedNames.contains sym || (m.imports.filter (·.1 == sym)).length == 1)

/-- The scope of the body of a parameterized assignment: its dummy references bound, each to
nothing that resolves (X.683 8.4: a dummy hides any other meaning of its name). Rules that decide
only what resolves leave what depends on an actual parameter alone. -/
def Scope.withDummies (m : Module) (ps : List Param) : Scope :=
  .mk m (ps.map fun p => (p.name, .raw [], p.governor, Scope.ofModule m))

mutual
  /-- The type notations written in an object's settings (X.681 11.7), and in the objects inside it. -/
  def objTypes : Obj → List Ty
    | .defn ss => ss.attach.flatMap fun ⟨(f, st), h⟩ => match st, h with
      | .type t, _ => [t]
      | .object o, h => objTypes o
      | .objectSet os, h => objSetTypes os
      | _, _ => []
    | _ => []
  decreasing_by all_goals decr_syntax
  def objSetTypes : ObjSet → List Ty
    | .spec (some r) _ (some a) => oelemsTypes r ++ oelemsTypes a
    | .spec (some r) _ none => oelemsTypes r
    | .spec none _ (some a) => oelemsTypes a
    | _ => []
  def oelemsTypes : OElems → List Ty
    | .obj o => objTypes o
    | .set s => objSetTypes s
    | .union a b | .inter a b | .except a b => oelemsTypes a ++ oelemsTypes b
    | _ => []
end

/-- Every type notation of a module with the assignment it is in and the scope it is read in:
`Module.Site` (type and value assignments, class definitions, objects and object sets), and
`ParamAssign.Has`, the bodies of parameterized assignments, read with the dummies bound to nothing
(X.683 8.4), where `Module.ValidAt` reads them with actual parameters (8.5). -/
def moduleTypes (m : Module) : List (String × Scope × Ty) :=
  let sc := Scope.ofModule m
  m.types.map (fun (nm, t) => (nm, sc, t)) ++
  m.values.map (fun (nm, t, _) => (nm, sc, t)) ++
  m.classes.flatMap (fun (nm, c) => (classTypes c).map (nm, sc, ·)) ++
  m.objects.flatMap (fun (nm, _, o) => (objTypes o).map (nm, sc, ·)) ++
  m.objectSets.flatMap (fun (nm, _, os) => (objSetTypes os).map (nm, sc, ·)) ++
  m.params.flatMap fun pa =>
    let psc := Scope.withDummies m pa.paramList
    let ts : List Ty := match pa with
      | .type _ _ t | .value _ _ t _ => [t]
      | .valueSet _ _ t c => [.constrained t c]
      | .cls _ _ c => classTypes c
      | .obj _ _ _ o => objTypes o
      | .objSet _ _ _ os => objSetTypes os
    ts.map (pa.name, psc, ·)

/-! ## Component relation constraints (X.682 10.7–10.15) -/

/-- Two constraining object sets that are certainly different: references to different names. -/
def ObjSet.differs (a b : ObjSet) : Bool :=
  match a.unwrap, b.unwrap with
  | .ref m1 a _, .ref m2 b _ => m1 != m2 || a != b
  | _, _ => false

/-- X.682 10.8–10.10, 10.15: each "AtNotation" of a component relation constraint names a
component of the structure it points into, and the last one is an "ObjectClassFieldType"
constrained by the same object set. `anc`: the textually enclosing SET, SET OF, SEQUENCE, SEQUENCE OF
and CHOICE types, innermost first. -/
def atRefOkB (E : Env) (n : Nat) (sc : Scope) (anc : List Ty) (os : ObjSet) (a : AtRef) : Bool :=
  let isStruct (t : Ty) : Bool := match t with
    | .sequence .. | .set .. | .choice .. => true
    | _ => false
  let isSeqSet (t : Ty) : Bool := match t with
    | .sequence .. | .set .. => true
    | _ => false
  -- 10.10 a): the outermost enclosing set, sequence or choice; b): from the innermost set or
  -- sequence, up as many levels as the dots after the first
  let parent : Option Ty := match a.level with
    | none => (anc.filter isStruct).getLast?
    | some k => match anc.findIdx? isSeqSet with
      | some i => anc[i + k]?
      | none => none
  match parent with
  | none => false
  | some p =>
    let rec walk (sc : Scope) (t : Ty) : List String → Bool
      | [] => true
      | [id] => match compsOf E n sc t with
        | some cs => !structKnown E n sc t || match cs.find? (·.1 == id) with
          | some (_, csc, ct) => match tableOn E n n csc ct with
            | some (some os') => !os.differs os'
            | some none => false
            | none => true
          | none => false
        | none => true
      | id :: rest => match compsOf E n sc t with
        | some cs => !structKnown E n sc t || match cs.find? (·.1 == id) with
          | some (_, csc, ct) => walk csc ct rest
          | none => false
        | none => true
    walk sc p a.path

/-- Every component relation constraint written inside a type, with its enclosing structures. -/
def atPathsOkB (E : Env) (n : Nat) (sc : Scope) (anc : List Ty) (t : Ty) : Bool :=
  match t with
  | .sequence r e r2 | .set r e r2 =>
    (r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2).attach.all fun ⟨c, h⟩ => match c, h with
      | .mk _ ct _, h => atPathsOkB E n sc (t :: anc) ct
      | _, _ => true
  | .choice r e => (choiceAlts r e).attach.all fun ⟨a, h⟩ => match a, h with
    | .mk _ at', h => atPathsOkB E n sc (t :: anc) at'
  | .sequenceOf et | .setOf et => atPathsOkB E n sc (t :: anc) et
  | .tagged _ _ u => atPathsOkB E n sc anc u
  | .constrained u c =>
    (match c with
      | .table os refs => refs.all (atRefOkB E n sc anc os)
      | _ => true) && atPathsOkB E n sc anc u
  | _ => true
termination_by t
decreasing_by all_goals decr_syntax

/-- A value `valKey` computes: equal keys are equal values. -/
inductive VKey where
  | int (i : Int)
  | oid (a : List Nat)
  | bool (b : Bool)
  | enum (e : String)
  deriving DecidableEq

def VKey.toVal : VKey → Val
  | .int i => .int i
  | .oid a => .oid a
  | .bool b => .bool b
  | .enum e => .enum e

/-- A key that tells values apart, where one is computed: integers and object identifiers through
value references, booleans, enumeration items. -/
def valKey (E : Env) (n : Nat) (sc : Scope) : Nat → Val → Option VKey
  | _, .int i => some (.int i)
  | _, .oid a => some (.oid a)
  | _, .bool b => some (.bool b)
  | _, .enum e => some (.enum e)
  | k + 1, .ref mn nm args => match resolveVal E n sc mn nm args with
    | some (sc', v) => valKey E n sc' k v
    | none => none
  | _, _ => none

mutual
  /-- The objects of an object set as written (each with the scope its settings are read in), through
  object and object set references and unions; `none` when an intersection or EXCEPT is involved
  (what remains is not decided here). -/
  def setObjs (E : Env) (n : Nat) : Nat → Scope → OElems → Option (List (Scope × List (String × Setting)))
    | 0, _, _ => none
    | _ + 1, sc, .obj (.defn ss) => some [(sc, ss)]
    | _ + 1, sc, .obj (.ref mn nm args) => match resolveObj E n sc mn nm args with
      | some (sc', _, .defn ss) => some [(sc', ss)]
      | _ => some []
    | k + 1, sc, .set os => objSetObjs E n k sc os
    | k + 1, sc, .union a b => do return (← setObjs E n k sc a) ++ (← setObjs E n k sc b)
    | _ + 1, _, _ => none
  termination_by k _ _ => 2 * k

  def objSetObjs (E : Env) (n : Nat) : Nat → Scope → ObjSet → Option (List (Scope × List (String × Setting)))
    | k, sc, .spec r _ a => do
      let x ← match r with | some r => setObjs E n k sc r | none => some []
      let y ← match a with | some a => setObjs E n k sc a | none => some []
      return x ++ y
    | 0, _, .ref .. => none
    | k + 1, sc, .ref mn nm args => match resolveObjSet E n sc mn nm args with
      | some (sc', _, os) => objSetObjs E n k sc' os
      | none => some []
  termination_by k _ _ => 2 * k + 1
end

/-- X.681 9.7: the value of an identifier (UNIQUE) field is unambiguous within an object set: two
objects with the same identifier are the same object. Decided where both objects' settings are
known and some value setting certainly differs, or one sets a field the other does not. -/
def uniqueOkB (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) (os : ObjSet) : Bool :=
  match classFields E n sc cls, objSetObjs E n 8 sc os with
  | some (_, fs), some objs =>
    let ids := fs.filterMap fun f => match f with | .fixedValue nm _ true _ => some nm | _ => none
    let key (o : Scope × List (String × Setting)) (f : String) : Option VKey :=
      (o.2.find? (·.1 == f)).bind fun (_, st) => match st with
        | .value v => valKey E n o.1 8 v
        | _ => none
    let differ (a b : Scope × List (String × Setting)) : Bool :=
      (a.2.map (·.1)).any (fun f => !(b.2.any (·.1 == f))) ||
      (b.2.map (·.1)).any (fun f => !(a.2.any (·.1 == f))) ||
      (a.2.map (·.1)).any fun f => (match key a f, key b f with
        | some x, some y => x != y
        | _, _ => false) ||
        -- type settings of different built-in types
        (match (a.2.find? (·.1 == f)), (b.2.find? (·.1 == f)) with
          | some (_, .type t), some (_, .type u) =>
            match (builtin E n a.1 t).bind (builtinName ·.2), (builtin E n b.1 u).bind (builtinName ·.2) with
            | some x, some y => x != y
            | _, _ => false
          | _, _ => false)
    let rec pairsOk (f : String) : List (Scope × List (String × Setting)) → Bool
      | [] => true
      | a :: rest => rest.all (fun b => match key a f, key b f with
          | some x, some y => x != y || !differ a b
          | _, _ => true) && pairsOk f rest
    ids.all fun f => pairsOk f objs
  | _, _ => true

/-- X.680 16.1 (`RefChainEnds`): following references, and the tags and constraints around them,
from `t` reaches a type within `k` steps. A chain that comes back to itself (`T ::= T`,
`T ::= [0] T (1..5)`) never does. Unresolved references are other rules' business. -/
def tyChainB (E : Env) (n : Nat) : Nat → Scope → Ty → Bool
  | 0, _, _ => false
  | k + 1, sc, .ref name => match resolveTy E n sc none name [] with
    | some (sc', t) => (sc.bound name).isSome || tyChainB E n k sc' t
    | none => true
  | k + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => tyChainB E n k sc' t
    | none => true
  | k + 1, sc, .tagged _ _ t | k + 1, sc, .constrained t _ => tyChainB E n k sc t
  | _ + 1, _, _ => true

/-- X.680 16.2, 14.9: following value references from `v` reaches a value within `k` steps; one
defined through itself (`q INTEGER ::= q`) never does. -/
def valChainB (E : Env) (n : Nat) : Nat → Scope → Val → Bool
  | 0, _, _ => false
  | k + 1, sc, .ref mn name [] => match resolveVal E n sc mn name [] with
    | some (sc', v) => (mn.isNone && (sc.bound name).isSome) || valChainB E n k sc' v
    | none => true
  | _ + 1, _, _ => true

/-- A rule broken: the module, the assignment, the rule, and the dummy reference for X.683 8.6 and
8.10. -/
structure Violation where
  mod : String
  name : String
  rule : Rule
  detail : String
  deriving Repr

def Violation.text (v : Violation) : String := v.rule.text v.detail

/-- X.680 13.7, 13.10 (`ModuleNamesOk`) over the names and definitive identifiers of the modules of
one sphere of interest: the names that two modules share without distinct identifiers. -/
def moduleNamesTwice : List (String × Option (List Nat)) → List String
  | [] => []
  | (a, x) :: rest =>
    (rest.filterMap fun (b, y) => if a == b && !(x.isSome && y.isSome && x != y) then some a else none) ++
      moduleNamesTwice rest

/-- The rules on a module as a whole. -/
def moduleChecks (E : Env) (m : Module) : List Violation :=
  let sc := Scope.ofModule m
  (if decide (m.name :: m.importMods).Nodup then [] else
    [⟨m.name, "", .importTwice, ""⟩]) ++
  (m.unusedDummies.map fun (nm, d) => ⟨m.name, nm, .unusedDummy, d⟩) ++
  -- X.683 8.10: the right side of a parameterized type is not only a dummy reference
  (m.params.filterMap fun pa => match pa with
    | .type nm ps (.ref r) => if ps.any (·.name == r) then some ⟨m.name, nm, .bodyOnlyDummy, r⟩ else none
    | _ => none) ++
  -- X.681 7.1: an "objectclassreference" has no lower-case letter
  ((m.classes.map (·.1) ++ m.params.filterMap (fun pa => match pa with | .cls nm .. => some nm | _ => none)).filterMap
    fun nm => if nm.any Char.isLower then some ⟨m.name, nm, .classLowerCase, ""⟩ else none) ++
  -- 53.4, 14.1: the defined value of an exception spec exists (or is a dummy reference)
  (m.exceptionRefs.filterMap fun (mn, v) =>
    if sc.knows mn v || m.params.any (·.paramList.any (·.name == v)) then none
    else some ⟨m.name, v, .exceptionRef, ""⟩) ++
  (if decide m.assignedNames.Nodup then [] else [⟨m.name, "", .assignedTwice, ""⟩]) ++
  ((importsOkB E m).map fun s => ⟨m.name, s, .importMissing, ""⟩) ++
  ((exportsOkB m).map fun s => ⟨m.name, s, .exportMissing, ""⟩)

/-- The rules on one type `s` written in assignment `nm` of module `m`, read in scope `sc`. -/
def typeChecks (E : Env) (n : Nat) (m : Module) (nm : String) (sc : Scope) (s : Ty) : List Violation :=
  (if namesOkB E n sc s then [] else [⟨m.name, nm, .names, ""⟩]) ++
  (if tagsOkB E n sc s then [] else [⟨m.name, nm, .tags, ""⟩]) ++
  (if autoAdditionsOkB sc s then [] else [⟨m.name, nm, .autoAdditions, ""⟩]) ++
  (if refsOkB E n sc s then [] else [⟨m.name, nm, .refs, ""⟩]) ++
  (if typeFromObjectsOkB E n sc s then [] else [⟨m.name, nm, .typeFromObjects, ""⟩]) ++
  (if argsOkB E n sc s then [] else [⟨m.name, nm, .args, ""⟩]) ++
  (if classRefsOkB E n sc s then [] else [⟨m.name, nm, .classRefs, ""⟩]) ++
  (if defaultRefsOkB E n sc s then [] else [⟨m.name, nm, .defaultRefs, ""⟩]) ++
  (if consRefsOkB E n sc s then [] else [⟨m.name, nm, .consRefs, ""⟩]) ++
  (if typeFromObjectsTableB E n sc s then [] else [⟨m.name, nm, .typeFromObjectsTable, ""⟩]) ++
  (if tableRefsOkB E n sc s then [] else [⟨m.name, nm, .tableRefs, ""⟩]) ++
  (if tableClassB E n sc s then [] else [⟨m.name, nm, .tableClass, ""⟩]) ++
  (if tableOnFieldB E n sc s then [] else [⟨m.name, nm, .tableOnField, ""⟩]) ++
  (if defaultsInTypeB E n sc s then [] else [⟨m.name, nm, .defaultInType, ""⟩]) ++
  (if serialValsOkB E n sc s then [] else [⟨m.name, nm, .serialVals, ""⟩]) ++
  (if innerNamesOkB E n sc s then [] else [⟨m.name, nm, .innerNames, ""⟩]) ++
  (if constraintKindsOkB E n sc s then [] else [⟨m.name, nm, .constraintKind, ""⟩]) ++
  (if componentsOfOkB E n sc s then [] else [⟨m.name, nm, .componentsOf, ""⟩]) ++
  (if universalTagOkB s then [] else [⟨m.name, nm, .universalTag, ""⟩]) ++
  (if presenceOkB E n sc s then [] else [⟨m.name, nm, .presence, ""⟩])

/-- The rules on a type written in assignment `nm` (an entry of `moduleTypes`), and on the types
inside it. -/
def siteChecks (E : Env) (n : Nat) (m : Module) (nm : String) (sc : Scope) (t : Ty) : List Violation :=
  (if atPathsOkB E n sc [] t then [] else [⟨m.name, nm, .atPath, ""⟩]) ++
  (occurrences t).flatMap (typeChecks E n m nm sc)

/-- The rules on parameterized assignments. -/
def paramChecks (E : Env) (n : Nat) (m : Module) : List Violation :=
  let sc := Scope.ofModule m
  (m.params.flatMap fun pa =>
    if paramGovsOkB E n sc pa then [] else [⟨m.name, pa.name, .paramGov, ""⟩]) ++
  (m.params.flatMap fun pa =>
    if paramBodyOkB E n sc pa then [] else [⟨m.name, pa.name, .paramBody, ""⟩])

/-- The rules on class assignments. -/
def classChecks (E : Env) (n : Nat) (m : Module) : List Violation :=
  let sc := Scope.ofModule m
  -- X.681 9.6: a DEFAULT of a fixed-type value field is a value of its type
  (m.classes.flatMap fun (nm, c) => match c with
    | .defn fs _ => fs.filterMap fun f => match f with
      | .fixedValue _ t _ (some (some v)) =>
        if valOkB E n sc t v then none else some ⟨m.name, nm, .fieldDefault, ""⟩
      | _ => none
    | _ => []) ++
  (m.classes.flatMap fun (nm, c) =>
    if classDefOkB E n sc c then [] else [⟨m.name, nm, .classDef, ""⟩])

/-- The rules on an object set assignment. -/
def objSetChecks (E : Env) (n : Nat) (m : Module) (nm : String) (cls : ClassRef) (os : ObjSet) :
    List Violation :=
  let sc := Scope.ofModule m
  (match cls with
    | .ref mn cn args => if (resolveClass E n sc mn cn args).isSome || sc.mayBe govClass mn cn then [] else
        [⟨m.name, nm, .objSetClass, ""⟩]
    | _ => []) ++
  (if uniqueOkB E n sc cls os then [] else [⟨m.name, nm, .unique, ""⟩]) ++
  (if oelemsRefsOkB.objSetRefsOkB E n sc os then [] else [⟨m.name, nm, .objSetRefs, ""⟩]) ++
  (match os with
    | .spec r _ a =>
      if (r.map (oelemsFieldsOkB E n sc cls)).getD true && (a.map (oelemsFieldsOkB E n sc cls)).getD true
      then [] else [⟨m.name, nm, .mandatoryFields, ""⟩]
    | _ => []) ++
  (match os with
    | .spec r _ a =>
      if (r.map (oelemsValRefsOkB E n sc cls)).getD true && (a.map (oelemsValRefsOkB E n sc cls)).getD true
      then [] else [⟨m.name, nm, .settingValRefs, ""⟩]
    | _ => [])

/-- The rules on an object assignment. -/
def objChecks (E : Env) (n : Nat) (m : Module) (nm : String) (cls : ClassRef) (o : Obj) :
    List Violation :=
  let sc := Scope.ofModule m
  -- X.681 11.3, 14.1: an object defined as another names one that exists; its class exists
  (if oelemsRefsOkB E n sc (.obj o) then [] else [⟨m.name, nm, .objRef, ""⟩]) ++
  (match cls with
    | .ref mn cn args => if (resolveClass E n sc mn cn args).isSome || sc.mayBe govClass mn cn then [] else
        [⟨m.name, nm, .objClass, ""⟩]
    | _ => []) ++
  (if objFieldsOkB E n sc cls o then [] else [⟨m.name, nm, .mandatoryFields, ""⟩]) ++
  (if objValRefsOkB E n sc cls o then [] else [⟨m.name, nm, .settingValRefs, ""⟩])

/-- The rules on a type assignment. -/
def typeAssignChecks (E : Env) (n : Nat) (m : Module) (nm : String) (t : Ty) : List Violation :=
  if tyChainB E n n (.ofModule m) t then [] else [⟨m.name, nm, .typeCycle, ""⟩]

/-- The rules on a value assignment. -/
def valueChecks (E : Env) (n : Nat) (m : Module) (nm : String) (t : Ty) (v : Val) : List Violation :=
  let sc := Scope.ofModule m
  (if (builtin E n sc t).isNone || valRefsOkB E n sc v then [] else [⟨m.name, nm, .valueRefs, ""⟩]) ++
  (if valOkB E n sc t v then [] else [⟨m.name, nm, .valueInType, ""⟩]) ++
  (if valChainB E n n sc v then [] else [⟨m.name, nm, .valueCycle, ""⟩])

/-- The rules above, over every module, at fuel `n`. X.680 13.7 is checked by `asn1check` for each
file (`moduleNamesTwice`). -/
def checkEnv (E : Env) (n : Nat) : List Violation :=
  E.flatMap fun m =>
    moduleChecks E m ++
    -- the types written in value assignments obey the same rules as those of type assignments
    ((moduleTypes m).flatMap fun (nm, sc, t) => siteChecks E n m nm sc t) ++
    paramChecks E n m ++ classChecks E n m ++
    (m.objectSets.flatMap fun (nm, cls, os) => objSetChecks E n m nm cls os) ++
    (m.objects.flatMap fun (nm, cls, o) => objChecks E n m nm cls o) ++
    (m.types.flatMap fun (nm, t) => typeAssignChecks E n m nm t) ++
    m.values.flatMap fun (nm, t, v) => valueChecks E n m nm t v

/-- Where each rule `checkEnv` reports stands against `Env.Valid` (SPEC-GAP.md). `.valid` and
`.partly` name the rule's fields of the spec, which `Valid` states over the types `moduleTypes`
lists (`Module.Site`, `ParamAssign.Has`). -/
def Rule.status : Rule → Rule.Status
  | .moduleNameTwice => .valid [``Env.Valid.moduleNames]
  | .importTwice => .valid [``Module.ValidAt.importsOnce]
  | .importMissing => .valid [``Module.ValidAt.imports]
  | .exportMissing => .valid [``Module.ValidAt.exports]
  | .exceptionRef => .valid [``Module.ValidAt.exceptionRefs]
  | .assignedTwice => .valid [``Module.ValidAt.assignedOnce]
  -- X.683 8.6 is decided on the lexical items of the right side (`unusedDummies`); a dummy is used
  -- when its name is written there, which the parsed form keeps only spread over every kind of
  -- reference
  | .unusedDummy => .notation
  | .bodyOnlyDummy => .valid [``Module.ValidAt.paramBodies]
  | .classLowerCase => .notation
  | .atPath => .valid [``SiteOk.atPaths]
  | .names => .valid [``TypeOk.names]
  | .tags => .valid [``TypeOk.tags]
  | .autoAdditions => .valid [``TypeOk.autoAdditions]
  -- `refsOkB` also reads dummies (X.683 8.4), which only occur in parameterized bodies
  | .refs => .valid [``TypeOk.refs]
  | .typeFromObjects => .valid [``TypeOk.typeFromObjects]
  | .args => .valid [``TypeOk.args]
  | .classRefs => .valid [``TypeOk.classRefs]
  -- a DEFAULT and a constraint value evaluate only when their references resolve (`evalVal`)
  | .defaultRefs | .defaultInType | .componentsOf => .valid [``TypeOk.components]
  | .consRefs | .serialVals | .innerNames | .presence => .valid [``TypeOk.constraints]
  | .typeFromObjectsTable => .valid [``TypeOk.typeFromObjectsTable]
  | .tableRefs => .valid [``TypeOk.tableRefs]
  | .tableClass => .valid [``TypeOk.tableClass]
  | .tableOnField => .valid [``TypeOk.tableOnField]
  | .constraintKind => .valid [``TypeOk.constraints, ``TypeOk.nonEmpty]
  | .universalTag => .valid [``TypeOk.universalTag]
  | .paramGov => .valid [``Module.ValidAt.paramGovs]
  -- the body is read with actual parameters, where its references must resolve
  | .paramBody => .valid [``TypeOk.refs, ``TypeOk.classRefs, ``TypeOk.typeFromObjects]
  | .fieldDefault => .valid [``ClassOk.fieldDefaults]
  | .classDef => .valid [``ClassOk.fieldClasses]
  | .objSetClass => .valid [``ObjSetOk.clsResolves]
  | .unique => .valid [``ObjSetOk.unique]
  | .objSetRefs => .valid [``ObjSetOk.refs]
  | .mandatoryFields => .valid [``ObjOk.fields, ``ObjSetOk.fields]
  | .settingValRefs => .valid [``ObjOk.settingRefs, ``ObjSetOk.settingRefs]
  | .objRef => .valid [``ObjOk.ref]
  | .objClass => .valid [``ObjOk.clsResolves]
  | .typeCycle => .valid [``Module.ValidAt.typeChains]
  -- a value evaluates only when its references resolve (`evalVal`)
  | .valueRefs | .valueInType | .valueCycle => .valid [``Module.ValidAt.values]

end Asn1.X680
