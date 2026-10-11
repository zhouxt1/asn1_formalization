import Asn1.X680.Tags
import Asn1.X680.Enumerated

/-!
# A valid specification (X.680's "shall" rules)

The rules here are what the encoding rules' theorems rely on:
- identifiers are distinct;
- tags are distinct where the text requires it, including 52.7's conceptually-added element;
- extension additions are ordered;
- DEFAULT values are values of their types;
- references resolve.

- subtype notations are applied only where Table 11 and Table 12 allow them, and SETTINGS are well
  formed (51.10);
- information objects, object sets and classes are well formed as far as X.681–683 say what an
  ASN.1 tool must reject (references, mandatory fields, UNIQUE, table and component relation
  constraints, governors of parameters);
- module names, imports and exports (13.7, 13.13, 13.16).

These are the rules the checker (`checkEnv`, Checker.lean) reports, each a field of `TypeOk`,
`SiteOk`, `ClassOk`, `ClassSyntaxOk`, `ObjOk`, `ObjSetOk`, `Module.ValidAt` or `Env.Valid`
(`Rule.status`). Rules that only restrict the notation (12, lexical) are listed in COVERAGE.md
and not formalized.
-/

namespace Asn1.X680

/-! ## Where a type occurs inside another -/

mutual
  /-- The types a constraint mentions: a contained subtype (51.3), a type constraint (51.6), the
  type of a contents constraint (X.682 11), through SIZE, FROM and inner subtyping. -/
  def consTypes : Constraint → List Ty
    | .mk r _ (some a) => esTypes r ++ esTypes a
    | .mk r _ none => esTypes r
    | .contents (some t) _ => [t]
    | _ => []
  def esTypes : ElemSet → List Ty
    | .elem e => elTypes e
    | .union a b | .inter a b | .except a b => esTypes a ++ esTypes b
    | .allExcept b => esTypes b
  def elTypes : Elem → List Ty
    | .contained t _ | .typeC t => [t]
    | .size c | .from_ c | .withComponent c => consTypes c
    | .withComponents _ cs => ncTypes cs
    | _ => []
  def ncTypes : List (String × Option Constraint × PresenceC) → List Ty
    | [] => []
    | (_, some c, _) :: r => consTypes c ++ ncTypes r
    | (_, none, _) :: r => ncTypes r
end

/-- `Occurs t s`: the type notation `s` occurs inside `t` (or is `t`). The types of components,
alternatives and elements, the parent of a constraint, and the types a constraint mentions are all
inside it. -/
inductive Occurs : Ty → Ty → Prop where
  | self t : Occurs t t
  | seqComp {r e r2 nm t p s} : Comp.mk nm t p ∈ r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2 →
      Occurs t s → Occurs (.sequence r e r2) s
  | setComp {r e r2 nm t p s} : Comp.mk nm t p ∈ r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2 →
      Occurs t s → Occurs (.set r e r2) s
  | seqCompsOf {r e r2 t s} : Comp.componentsOf t ∈ r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2 →
      Occurs t s → Occurs (.sequence r e r2) s
  | setCompsOf {r e r2 t s} : Comp.componentsOf t ∈ r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2 →
      Occurs t s → Occurs (.set r e r2) s
  | seqOf {t s} : Occurs t s → Occurs (.sequenceOf t) s
  | setOf {t s} : Occurs t s → Occurs (.setOf t) s
  | choiceAlt {r e nm t s} : Alt.mk nm t ∈ choiceAlts r e → Occurs t s → Occurs (.choice r e) s
  | selection {nm t s} : Occurs t s → Occurs (.selection nm t) s
  | tagged {tg k t s} : Occurs t s → Occurs (.tagged tg k t) s
  | constrained {t c s} : Occurs t s → Occurs (.constrained t c) s
  | inConstraint {t c u s} : u ∈ consTypes c → Occurs u s → Occurs (.constrained t c) s
  /-- X.683 9.2: a type written as an actual parameter is a type of the module like any other -/
  | paramArg {mn nm args u s} : Arg.type u ∈ args → Occurs u s → Occurs (.paramRef mn nm args) s

/-! ## Where a module writes types -/

mutual
  /-- `ObjHas o t`: type notation `t` is written in the settings of object `o` (X.681 11.7), or of
  an object or object set inside them. -/
  inductive ObjHas : Obj → Ty → Prop
    | type {ss f t} : (f, Setting.type t) ∈ ss → ObjHas (.defn ss) t
    | object {ss f o t} : (f, Setting.object o) ∈ ss → ObjHas o t → ObjHas (.defn ss) t
    | objectSet {ss f os t} : (f, Setting.objectSet os) ∈ ss → ObjSetHas os t → ObjHas (.defn ss) t

  /-- `ObjSetHas os t`: `t` is written in an object of object set `os` (X.681 12.3). -/
  inductive ObjSetHas : ObjSet → Ty → Prop
    | root {r x a t} : OElemsHas r t → ObjSetHas (.spec (some r) x a) t
    | addition {r x a t} : OElemsHas a t → ObjSetHas (.spec r x (some a)) t

  inductive OElemsHas : OElems → Ty → Prop
    | obj {o t} : ObjHas o t → OElemsHas (.obj o) t
    | set {s t} : ObjSetHas s t → OElemsHas (.set s) t
    | unionL {a b t} : OElemsHas a t → OElemsHas (.union a b) t
    | unionR {a b t} : OElemsHas b t → OElemsHas (.union a b) t
    | interL {a b t} : OElemsHas a t → OElemsHas (.inter a b) t
    | interR {a b t} : OElemsHas b t → OElemsHas (.inter a b) t
    | exceptL {a b t} : OElemsHas a t → OElemsHas (.except a b) t
    | exceptR {a b t} : OElemsHas b t → OElemsHas (.except a b) t
end

/-- The types a class definition writes: of its fixed-type value and value set fields, and the
DEFAULT of a type field (X.681 9.5–9.10). -/
def classTypes : ClassRef → List Ty
  | .defn fs _ => fs.flatMap fun f => match f with
    | .fixedValue _ t _ _ | .fixedValueSet _ t _ => [t]
    | .typeField _ (some (some t)) => [t]
    | _ => []
  | _ => []

/-- `m.Site nm t`: module `m` writes type notation `t` in assignment `nm`, outside parameterized
assignments: a type or value set (X.680 16.1, 16.6), the governor of a value (16.2), a class
definition (X.681 9), the settings of an object or of the objects of an object set (X.681 11.7,
12). -/
inductive Module.Site (m : Module) : String → Ty → Prop
  | type {nm t} : (nm, t) ∈ m.types → m.Site nm t
  | valueGov {nm t v} : (nm, t, v) ∈ m.values → m.Site nm t
  | classDef {nm c t} : (nm, c) ∈ m.classes → t ∈ classTypes c → m.Site nm t
  | object {nm cls o t} : (nm, cls, o) ∈ m.objects → ObjHas o t → m.Site nm t
  | objectSet {nm cls os t} : (nm, cls, os) ∈ m.objectSets → ObjSetHas os t → m.Site nm t

/-- The parameters a parameterized assignment declares (X.683 8.1). -/
def ParamAssign.paramList : ParamAssign → List Param
  | .type _ ps _ | .value _ ps _ _ | .valueSet _ ps _ _ | .cls _ ps _ | .obj _ ps _ _ | .objSet _ ps _ _ => ps

/-- `pa.Has t`: the right side of parameterized assignment `pa` writes type notation `t`: the type,
the governor of the value, the value set (X.683 8.2), or as a class, object or object set does. -/
def ParamAssign.Has : ParamAssign → Ty → Prop
  | .type _ _ b, t | .value _ _ b _, t => t = b
  | .valueSet _ _ b c, t => t = .constrained b c
  | .cls _ _ c, t => t ∈ classTypes c
  | .obj _ _ _ o, t => ObjHas o t
  | .objSet _ _ _ os, t => ObjSetHas os t

/-! ## Helpers the rules below share -/

/-- The built-in type a type is derived from, for 51.3.2, as a name; `none` for an open type. The
useful types are the restricted character string types they are defined from (45.1, 46.1, 47.1). -/
def builtinName : Ty → Option String
  | .boolean => "BOOLEAN" | .integer _ => "INTEGER" | .enumerated .. => "ENUMERATED" | .real => "REAL"
  | .bitString _ => "BIT STRING" | .octetString => "OCTET STRING" | .null => "NULL"
  | .sequence .. => "SEQUENCE" | .sequenceOf _ => "SEQUENCE OF" | .set .. => "SET" | .setOf _ => "SET OF"
  | .choice .. => "CHOICE" | .objectIdentifier => "OBJECT IDENTIFIER" | .relativeOid => "RELATIVE-OID"
  | .oidIri => "OID-IRI" | .relativeOidIri => "RELATIVE-OID-IRI" | .embeddedPdv => "EMBEDDED PDV"
  | .external => "EXTERNAL" | .characterString => "CHARACTER STRING" | .restricted k => s!"{repr k}"
  | .generalizedTime | .utcTime => s!"{repr StrType.visible}"
  | .objectDescriptor => s!"{repr StrType.graphic}"
  | .time => "TIME" | .date => "DATE" | .timeOfDay => "TIME-OF-DAY" | .dateTime => "DATE-TIME"
  | .duration => "DURATION"
  | _ => none

/-- The type a value reference's assignment gives it (X.680 16.2; X.683 8.2 for a parameterized
value). A dummy is not decided. -/
def resolveValTy (E : Env) (n : Nat) (sc : Scope) (mn : Option String) (name : String)
    (args : List Arg) : Option (Scope × Ty) :=
  resolveIn E n sc mn name args (fun _ _ _ => none)
    (fun m => (m.values.find? (·.1 == name)).map (·.2.1))
    (fun | .value _ ps t _ => some (ps, t) | _ => none)

/-- What X.680 C.4 and C.5 let a value of one built-in type stand for a value of another: tagging
and subtyping keep the built-in type, the group A character string types map to one another
(C.5.1), and the useful types are their restricted character string types (C.4.2). -/
def mapName (t : Ty) : Option String :=
  match t with
  | .restricted k => if k ∈ [.utf8, .numeric, .printable, .ia5, .visible, .universal, .bmp] then some "A" else builtinName t
  | .generalizedTime | .utcTime => some "A"
  | _ => builtinName t


/-- X.681 9.5–9.12: a field neither OPTIONAL nor DEFAULT. -/
def FieldSpec.mandatory : FieldSpec → Bool
  | .typeField _ none | .fixedValue _ _ _ none | .varValue _ _ none | .fixedValueSet _ _ none
  | .varValueSet _ _ none | .objectField _ _ none | .objectSetField _ _ none => true
  | _ => false


/-- The components of a SEQUENCE, SET or CHOICE type, through references (`builtin`), with the scope
each is read in; `none` when the type is not one or does not resolve. -/
def compsOf (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Option (List (String × Scope × Ty)) :=
  match builtin E n sc t with
  | some (sc', .sequence r e r2) | some (sc', .set r e r2) =>
    some ((entries E n sc' r e r2).map fun en => (en.name, en.scope, en.ty))
  | some (sc', .choice r e) => some ((choiceAlts r e).map fun a => (a.name, sc', a.ty))
  | _ => none

/-- The object set and class of the table constraint on a component's type, through tags,
constraints and type references: `some none` when the type is an "ObjectClassFieldType" with no
table constraint, `none` when not decided. -/
def tableOn (E : Env) (n : Nat) : Nat → Scope → Ty → Option (Option ObjSet)
  | 0, _, _ => none
  | k + 1, sc, .tagged _ _ t => tableOn E n k sc t
  | k + 1, sc, .constrained t c => match c with
    | .table os _ => some (some os)
    | _ => tableOn E n k sc t
  | _ + 1, _, .classField .. => some none
  | k + 1, sc, .ref nm => match resolveTy E n sc none nm [] with
    | some (sc', t) => tableOn E n k sc' t
    | none => none
  | _ + 1, _, _ => none


/-- `{S}`, an object set spec of one element that is the set S, is S. -/
def ObjSet.unwrap : ObjSet → ObjSet
  | .spec (some (.set s)) false none => s
  | os => os

/-- The class a class reference finally names, through class assignments that are references
(`C2 ::= C`), as `module.name`; `none` for a parameterized class or one that does not resolve. -/
def classKey (E : Env) : Nat → Scope → ClassRef → Option String
  | 0, _, _ => none
  | _ + 1, _, .typeIdentifier => some "TYPE-IDENTIFIER"
  | _ + 1, _, .abstractSyntax => some "ABSTRACT-SYNTAX"
  | k + 1, sc, .ref mn nm [] => match resolveClass E k sc mn nm [] with
    | some (sc', .ref mn' nm' args) => classKey E k sc' (.ref mn' nm' args)
    | some (sc', .defn ..) =>
      -- the module the name is assigned in: follow imports
      let home := ((E.resolveWith (fun m => (m.classes.find? (·.1 == nm)).map (·.2)) nm k sc.mod).map (·.1.name))
      some s!"{(home.getD sc'.mod.name)}.{nm}"
    | some (_, c) => classKey E k sc c
    | none => none
  | _ + 1, _, _ => none


/-- A reference to an object or to an object set. -/
inductive ORef where
  | obj (mn : Option String) (name : String) (args : List Arg)
  | set (mn : Option String) (name : String) (args : List Arg)

mutual
  /-- `OElemsRef e r`: the elements `e` of an object set reference `r` (X.681 12.3, 12.10, 15), not
  looking into the settings of the objects written there. -/
  inductive OElemsRef : OElems → ORef → Prop
    | obj {mn nm args} : OElemsRef (.obj (.ref mn nm args)) (.obj mn nm args)
    | set {s r} : ObjSetRef s r → OElemsRef (.set s) r
    | fromObjects {s f r} : ObjSetRef s r → OElemsRef (.fromObjects s f) r
    | unionL {a b r} : OElemsRef a r → OElemsRef (.union a b) r
    | unionR {a b r} : OElemsRef b r → OElemsRef (.union a b) r
    | interL {a b r} : OElemsRef a r → OElemsRef (.inter a b) r
    | interR {a b r} : OElemsRef b r → OElemsRef (.inter a b) r
    | exceptL {a b r} : OElemsRef a r → OElemsRef (.except a b) r
    | exceptR {a b r} : OElemsRef b r → OElemsRef (.except a b) r

  inductive ObjSetRef : ObjSet → ORef → Prop
    | ref {mn nm args} : ObjSetRef (.ref mn nm args) (.set mn nm args)
    | root {r x a ref} : OElemsRef r ref → ObjSetRef (.spec (some r) x a) ref
    | addition {r x a ref} : OElemsRef a ref → ObjSetRef (.spec r x (some a)) ref
end

/-- X.681 11.3, 12.3, X.680 14.1: the reference names an object (object set) that exists. -/
def ORef.Resolves (E : Env) (n : Nat) (sc : Scope) : ORef → Prop
  | .obj mn nm args => (resolveObj E n sc mn nm args).isSome
  | .set mn nm args => (resolveObjSet E n sc mn nm args).isSome

/-- `ValRef v r`: value notation `v` references the value `r` (X.680 14.1), outside open types. -/
inductive ValRef : Val → Option String × String × List Arg → Prop
  | ref {mn nm args} : ValRef (.ref mn nm args) (mn, nm, args)
  | seq {cs f w r} : (f, w) ∈ cs → ValRef w r → ValRef (.seq cs) r
  | seqOf {vs w r} : w ∈ vs → ValRef w r → ValRef (.seqOf vs) r
  | setOf {vs w r} : w ∈ vs → ValRef w r → ValRef (.setOf vs) r
  | choice {a w r} : ValRef w r → ValRef (.choice a w) r

/-- X.680 14.1, 16.2: each value reference in `v` names a value, or is a dummy reference (X.683
8.4). -/
def ValRefsOk (E : Env) (n : Nat) (sc : Scope) (v : Val) : Prop :=
  ∀ mn nm args, ValRef v (mn, nm, args) →
    (mn = none ∧ args = [] ∧ (sc.bound nm).isSome) ∨ (resolveVal E n sc mn nm args).isSome

/-- X.680 C.6.1: a value reference used where type `t` (read in `sc`) governs names a value whose
type maps to `t` (C.4, C.5): one of the same built-in type, or both of the group A character string
types (C.5.1), as far as the built-in types tell. -/
def RefMaps (E : Env) (n : Nat) (sc : Scope) (t : Ty) (vsc : Scope) : Val → Prop
  | .ref mn nm args => ∀ usc u p q, resolveValTy E n vsc mn nm args = some (usc, u) →
      (builtin E n sc t).bind (mapName ·.2) = some p → (builtin E n usc u).bind (mapName ·.2) = some q →
      p = q
  | _ => True

/-- `RefMaps` for a value and the values of its components, at most `k` deep. -/
def ValMaps (E : Env) (n : Nat) : Nat → Scope → Ty → Scope → Val → Prop
  | 0, _, _, _, _ => True
  | k + 1, sc, t, vsc, v => RefMaps E n sc t vsc v ∧
    match v, builtin E n sc t with
    | .seq cs, some (sc', .sequence ro e r2) | .seq cs, some (sc', .set ro e r2) =>
      ∀ nm w, (nm, w) ∈ cs → ∀ en, (entries E n sc' ro e r2).find? (·.name == nm) = some en →
        ValMaps E n k en.scope en.ty vsc w
    | .seqOf vs, some (sc', .sequenceOf el) | .seqOf vs, some (sc', .setOf el)
    | .setOf vs, some (sc', .sequenceOf el) | .setOf vs, some (sc', .setOf el) =>
      ∀ w ∈ vs, ValMaps E n k sc' el vsc w
    | .choice a w, some (sc', .choice ro ext) =>
      ∀ alt, findAlt (choiceAlts ro ext) a = some alt → ValMaps E n k sc' alt.ty vsc w
    | _, _ => True

/-! ## The rules, for one occurrence of a type in module `m`, at fuel `n` -/

/-- X.680 25.14, 27.4 and 29.10: identifiers are distinct. X.680 20.2: so are the identifiers and
the numbers of an enumeration, and 20.4–20.5 order the additions' numbers. -/
def NamesOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : Ty → Prop
  | .sequence r e r2 | .set r e r2 => ((entries E n sc r e r2).map (·.name)).Nodup
  | .choice r e => ((choiceAlts r e).map (·.name)).Nodup
  -- 19.5, 19.6: the named numbers' identifiers and values are distinct
  | .integer named => (named.map (·.1)).Nodup ∧ (named.map (·.2)).Nodup
  -- 22.4, 22.5: so are the named bits' identifiers and numbers
  | .bitString named => (named.map (·.1)).Nodup ∧ (named.map (·.2)).Nodup
  | .enumerated r e =>
    let nums := enumNumbers r e
    (nums.map (·.1)).Nodup ∧ (nums.map (·.2)).Nodup ∧
      -- 20.4: each addition is greater than every addition before it
      ((nums.drop r.length).map (·.2)).Pairwise (· < ·)
  | _ => True

/-- Tags compared for distinctness: a tag, the indeterminate tag of an open type (X.681 14.2 b)),
or the tag of 52.7's conceptually-added element. -/
inductive CTag where
  | tag (t : Tag)
  | indeterminate
  | conceptual
  deriving DecidableEq

/-- Two tags that are not distinct.
- X.681 14.2 b): an open type "has an indeterminate tag and thus cannot be used where a tag
  distinct from that of some other type is required"; NOTE 2: that includes the conceptually-added
  element.
- X.680 52.7.3: the conceptually-added element's tag is distinct from the tags of all known types. -/
def CTag.clash : CTag → CTag → Bool
  | .tag a, .tag b => a == b
  | .indeterminate, _ | _, .indeterminate => true
  | .conceptual, .conceptual => true
  | _, _ => false

/-- Pairwise distinct tags. -/
def TagsDistinct (ts : List CTag) : Prop := ts.Pairwise fun a b => a.clash b = false

def ctags : Option (List Tag) → List CTag
  | some ts => ts.map .tag
  | none => [.indeterminate]

/-- X.680 52.7.1: whether a list of components or alternatives gets a conceptually-added element:
it has an ellipsis, or EXTENSIBILITY IMPLIED gives it one. -/
def conceptual (m : Module) (hasExt : Bool) : List CTag :=
  if hasExt || m.header.extImplied then [.conceptual] else []

/-- X.680 25.6.1: in a series of components, the tags of each run of OPTIONAL or DEFAULT
components, and of the component immediately after the run, are distinct. `series` gives each
component's tags and whether it is OPTIONAL or DEFAULT. -/
def RunsDistinct (series : List (List CTag × Bool)) : Prop :=
  ∀ (i j : Nat), i < j →
    (∀ (k : Nat), i ≤ k → k < j → ∃ x : List CTag × Bool, series[k]? = some x ∧ x.2 = true) →
    ∀ (x y : List CTag × Bool), series[i]? = some x → series[j]? = some y →
      ∀ t ∈ x.1, ∀ u ∈ y.1, t.clash u = false

/-- X.680 25.6–25.7, 27.3, 29.3, 29.7, 52.7: distinct tags. -/
def TagsOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : Ty → Prop
  | .sequence r e r2 =>
    let et := entryTags E n sc r e r2
    -- 52.7.3, 52.8: a component's tags, with a nested conceptually-added element
    let auto := autoSeq sc.mod.header.tagDefault r e r2
    let ect (x : Entry × Option (List Tag)) : List CTag :=
      ctags x.2 ++ if !auto && carriesConceptual E n x.1.scope x.1.ty then [.conceptual] else []
    let item (x : Entry × Option (List Tag)) : List CTag × Bool :=
      (ect x, !x.1.presence.isMandatory)
    let roots := et.filter (·.1.addition.isNone)
    let adds := et.filter (·.1.addition.isSome)
    let tail := et.drop (et.length - (entries E n sc [] none r2).length)
    let insert := (conceptual sc.mod e.isSome).map fun t => ([t], true)
    -- 25.6.2: the root series
    RunsDistinct (roots.map item) ∧
    -- 25.6.3, 52.7.1: the complete textual series, the conceptually-added element at the
    -- insertion point
    RunsDistinct ((et.take (et.length - tail.length)).map item ++ insert ++ tail.map item) ∧
    -- 25.7: each addition differs from the trailing root components up to and including the first
    -- mandatory one
    (∀ a ∈ adds, ∀ (k : Nat) (x : Entry × Option (List Tag)), tail[k]? = some x →
      (∀ (k' : Nat) (y : Entry × Option (List Tag)), k' < k → tail[k']? = some y →
        !y.1.presence.isMandatory) →
      ∀ t ∈ ect a, ∀ u ∈ ect x, t.clash u = false)
  | .set r e r2 =>
    let et := entryTags E n sc r e r2
    let auto := autoSeq sc.mod.header.tagDefault r e r2
    let ect (x : Entry × Option (List Tag)) : List CTag :=
      ctags x.2 ++ if !auto && carriesConceptual E n x.1.scope x.1.ty then [.conceptual] else []
    -- 27.3, 52.7, 52.8.3: all tags distinct, and the additions in increasing canonical order
    TagsDistinct ((et.flatMap ect) ++ conceptual sc.mod e.isSome) ∧
    ((et.filter (·.1.addition.isSome)).filterMap fun x => match x.2 with
      | some [t] => some t
      | _ => none).Pairwise (fun a b => a.lt b)
  | .choice r e =>
    let at' := altTags E n sc r e
    let auto := autoChoice sc.mod.header.tagDefault r e
    let act (x : Alt × Option (List Tag)) : List CTag :=
      ctags x.2 ++ if !auto && carriesConceptual E n sc x.1.ty then [.conceptual] else []
    -- 29.3, 52.7
    TagsDistinct ((at'.flatMap act) ++ conceptual sc.mod e.isSome) ∧
    -- 29.7: each addition canonically greater than the additions before it
    ((at'.drop r.length).filterMap fun x => match x.2 with
      | some [t] => some t
      | _ => none).Pairwise (fun a b => a.lt b)
  -- 31.2.9: IMPLICIT is not used on an untagged CHOICE or open type
  | .tagged _ .implicit t => untaggedChoiceOrOpen E n sc t = false
  | _ => True

/-- X.680 25.9 and 29.4: with automatic tagging and an untagged root, the additions are not
textually tagged. -/
def AutoAdditionsOk (sc : Scope) : Ty → Prop
  | .sequence r e r2 | .set r e r2 =>
    sc.mod.header.tagDefault = .automatic → !(r ++ r2).any Comp.textuallyTagged →
      !((e.getD []).flatMap ExtAdd.comps).any Comp.textuallyTagged
  | .choice r e =>
    sc.mod.header.tagDefault = .automatic → !r.any (fun a => a.ty.textuallyTagged) →
      !((choiceAlts r e).drop r.length).any (fun a => a.ty.textuallyTagged)
  | _ => True

/-- The components of a SEQUENCE or SET type that are COMPONENTS OF some type. -/
def componentsOfTypes (r : List Comp) (e : Option (List ExtAdd)) (r2 : List Comp) : List Ty :=
  (r ++ (e.getD []).flatMap ExtAdd.comps ++ r2).filterMap
    (fun c => match c with | .componentsOf t => some t | _ => none)

/-- X.680 25.12: a DEFAULT value is a value of the component's type. X.680 25.5: COMPONENTS OF in a
sequence type names a sequence type with at least one component; 27.2: in a set type, a set
type. -/
def ComponentsOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : Ty → Prop
  | .sequence r e r2 =>
    (∀ en ∈ entries E n sc r e r2, ∀ d, en.presence = .default_ d → ∃ d', evalVal E n en.scope d d' ∧ (sem E H n en.scope [] en.ty).all d') ∧
    -- C.6.1: the references in a DEFAULT value map to the component's type
    (∀ nm t d, Comp.mk nm t (.default_ d) ∈ r ++ (e.getD []).flatMap ExtAdd.comps ++ r2 → ValMaps E n n sc t sc d) ∧
    (∀ t ∈ componentsOfTypes r e r2, ∃ sc' r' e' r2', builtin E n sc t = some (sc', .sequence r' e' r2') ∧
        (entries E n sc' r' none r2') ≠ [])
  | .set r e r2 =>
    (∀ en ∈ entries E n sc r e r2, ∀ d, en.presence = .default_ d → ∃ d', evalVal E n en.scope d d' ∧ (sem E H n en.scope [] en.ty).all d') ∧
    (∀ nm t d, Comp.mk nm t (.default_ d) ∈ r ++ (e.getD []).flatMap ExtAdd.comps ++ r2 → ValMaps E n n sc t sc d) ∧
    (∀ t ∈ componentsOfTypes r e r2, ∃ sc' r' e' r2', builtin E n sc t = some (sc', .set r' e' r2') ∧
        (entries E n sc' r' none r2') ≠ [])
  | _ => True

/-- X.680 13.16, 14.1, 14.6: references resolve. X.680 30.1: a selection names an alternative of
a CHOICE. -/
def RefsOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : Ty → Prop
  | .ref name => (resolveTy E n sc none name []).isSome
  | .extRef mn name => (resolveTy E n sc (some mn) name []).isSome
  -- X.683 8.4: a dummy reference is not itself parameterized
  | .paramRef none name args => sc.bound name = none ∧ (resolveTy E n sc none name args).isSome
  | .paramRef mn name args => (resolveTy E n sc mn name args).isSome
  | .selection nm t => ∃ sc' r e, builtin E n sc t = some (sc', .choice r e) ∧
      (findAlt (choiceAlts r e) nm).isSome
  | _ => True

/-- X.680 49.7: a constraint selects at least one value. 3.8.61 NOTE: so does a recursive type. -/
def NonEmpty (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) (t : Ty) : Prop :=
  ∃ v, (sem E H n sc [] t).all v

/-! ## Which subtype notations apply to which types (51.1, Table 11, Table 12) -/

/-- The rows of Table 11 and Table 12: the built-in type a parent type is derived from. -/
inductive Row where
  | bitString | boolean | choice | embeddedPdv | enumerated | external | integer | null
  | objectDescriptor | oid | octetString | oidIri | openType | real | relOid | relOidIri
  | restricted (k : StrType) | sequence | sequenceOf | set | setOf | usefulTime | unrestricted
  /-- Table 12: TIME, and the useful time types, which are derived from it by tagging and
  subtyping (38.4) -/
  | time
  deriving DecidableEq

/-- The row of a built-in type (`builtin`'s result). INSTANCE OF is a sequence type (X.681 C.7),
and its row in Table 11 allows what Sequence's does.

OPEN (ledger X680-24): Table 11's row for an object class field type allows only single values and
contained subtypes, but X.681 14.5 makes a fixed-type field's type that type, which `builtin`
follows; we take the row of that type. -/
def rowOf : Ty → Option Row
  | .bitString _ => some .bitString
  | .boolean => some .boolean
  | .choice .. => some .choice
  | .embeddedPdv => some .embeddedPdv
  | .enumerated .. => some .enumerated
  | .external => some .external
  | .integer _ => some .integer
  | .null => some .null
  | .objectDescriptor => some .objectDescriptor
  | .objectIdentifier => some .oid
  | .octetString => some .octetString
  | .oidIri => some .oidIri
  | .openType => some .openType
  | .real => some .real
  | .relativeOid => some .relOid
  | .relativeOidIri => some .relOidIri
  | .restricted k => some (.restricted k)
  | .sequence .. => some .sequence
  | .sequenceOf _ => some .sequenceOf
  | .set .. => some .set
  | .setOf _ => some .setOf
  | .generalizedTime | .utcTime => some .usefulTime
  | .characterString => some .unrestricted
  | .time | .date | .timeOfDay | .dateTime | .duration => some .time
  | _ => none

/-- The columns of Table 11 and Table 12. Duration, time point and recurrence ranges are value
ranges (51.11.1, 51.12.1, 51.13.1). -/
inductive ElemKind where
  | single | contained | range | size | alphabet | typeC | inner | pattern | settings
  deriving DecidableEq

def Elem.kind : Elem → ElemKind
  | .single _ => .single
  | .contained _ _ => .contained
  | .range .. => .range
  | .size _ => .size
  | .typeC _ => .typeC
  | .from_ _ => .alphabet
  | .withComponent _ | .withComponents .. => .inner
  | .pattern _ => .pattern
  | .settings _ => .settings

/-- X.680 Table 11 and Table 12 ("Yes"). Value ranges on restricted character strings are only
allowed within a permitted alphabet (note a)), which `ElemOk` handles. -/
def Row.allows : Row → ElemKind → Bool
  | .bitString, k => k ∈ [.single, .contained, .size]
  | .boolean, k => k ∈ [.single, .contained]
  | .choice, k => k ∈ [.single, .contained, .inner]
  | .embeddedPdv, k => k ∈ [.single, .inner]
  | .enumerated, k => k ∈ [.single, .contained]
  | .external, k => k ∈ [.single, .inner]
  | .integer, k => k ∈ [.single, .contained, .range]
  | .null, k => k ∈ [.single, .contained]
  | .objectDescriptor, k => k ∈ [.single, .contained, .size, .alphabet]
  | .oid, k => k ∈ [.single, .contained]
  | .octetString, k => k ∈ [.single, .contained, .size]
  | .oidIri, k => k ∈ [.single, .contained]
  | .openType, k => k ∈ [.typeC]
  | .real, k => k ∈ [.single, .contained, .range, .inner]
  | .relOid, k => k ∈ [.single, .contained]
  | .relOidIri, k => k ∈ [.single, .contained]
  | .restricted _, k => k ∈ [.single, .contained, .size, .alphabet, .pattern]
  | .sequence, k => k ∈ [.single, .contained, .inner]
  | .sequenceOf, k => k ∈ [.single, .contained, .size, .inner]
  | .set, k => k ∈ [.single, .contained, .inner]
  | .setOf, k => k ∈ [.single, .contained, .size, .inner]
  | .usefulTime, k => k ∈ [.single, .contained]
  | .unrestricted, k => k ∈ [.single, .size, .inner]
  | .time, k => k ∈ [.single, .contained, .settings, .range, .inner]

/-- The type whose components an inner subtyping constraint names: the type itself, or the
associated type (21.5, 36.5, 37.5, 44.5) or equivalent sequence type (38.4.4.2). -/
def innerTarget (sc : Scope) : Ty → Scope × Ty
  | .real => (.ofModule assocModule, realAssoc)
  | .embeddedPdv => (.ofModule assocModule, embeddedPdvAssoc)
  | .external => (.ofModule assocModule, externalAssoc)
  | .characterString => (.ofModule assocModule, characterStringAssoc)
  | .time | .duration => (.ofModule assocModule, .sequence durationEquivComps none [])
  | t => (sc, t)

/-- X.680 51.5.3, 51.7.3: the "SubtypeConstraint" alternative of "ConstraintSpec". -/
def Constraint.isSubtype : Constraint → Bool
  | .mk .. => true
  | _ => false

/-- X.680 51.5.3: the parent type of the constraint inside SIZE, INTEGER (0..MAX). -/
def sizeParentTy : Ty := .constrained (.integer []) (.mk (.elem (.range (.val (.int 0)) false .max false)) false none)

/-- X.680 51.4.4 NOTE: an endpoint of a value range in a permitted alphabet is of size 1. -/
def SingleChar : Bound → Prop
  | .val (.chars [_]) => True
  | .val _ => False
  | _ => True

/-- The endpoints of a value range on TIME (51.11–51.13), evaluated.
- 51.11.2, 51.11.3: two durations, with the same least significant element to the same accuracy,
  and identical above it;
- 51.12.2–51.12.4: two time points with the same settings, Midnight aside, and the same time
  difference;
- 51.13.2: two integers (or MIN, MAX). -/
def timeRangeOk : Bound → Bound → Bool
  | .val (.time (.interval (.d a))), .val (.time (.interval (.d b))) =>
    a.Wf && b.Wf && a.last == b.last && a.frac.length == b.frac.length &&
      a.vec.take a.last == b.vec.take b.last
  | .val (.time (.point a)), .val (.time (.point b)) => a.Wf && b.Wf && a.sameShape b && a.zone == b.zone
  | .val (.int _), .val (.int _) | .min, .val (.int _) | .val (.int _), .max | .min, .max => true
  | _, _ => false

def PresenceC.isPresent : PresenceC → Bool | .present => true | _ => false
def PresenceC.isOptional : PresenceC → Bool | .optional => true | _ => false
def PresenceC.isEmpty : PresenceC → Bool | .unspecified => true | _ => false

/-- X.680 51.8.6, 51.8.10: the presence constraints of a "MultipleTypeConstraints" on type `t`.
- in a sequence type, the named constraints are in the components' order (51.8.6);
- in a sequence or set type, PRESENT, ABSENT and OPTIONAL constrain only components marked
  OPTIONAL (51.8.10.1);
- in a choice type, the presence constraints are PRESENT or ABSENT, at most one PRESENT
  (51.8.10.2). -/
def PresenceOk (E : Env) (n : Nat) (sc : Scope) (t : Ty)
    (ncs : List (String × Option Constraint × PresenceC)) : Prop :=
  let optionalOnly (es : List Entry) : Prop := ∀ x ∈ ncs, x.2.2.isEmpty = false →
    ∃ en ∈ es, en.name = x.1 ∧ en.presence = .optional
  match builtin E n sc t with
  | some (sc', .sequence r e r2) =>
    let es := entries E n sc' r e r2
    (ncs.map fun x => es.findIdx (·.name == x.1)).Pairwise (· < ·) ∧ optionalOnly es
  | some (sc', .set r e r2) => optionalOnly (entries E n sc' r e r2)
  | some (_, .choice _ _) =>
    (∀ x ∈ ncs, x.2.2.isOptional = false) ∧ (ncs.filter (·.2.2.isPresent)).length ≤ 1
  | _ => True

mutual
  /-- X.680 51.1: the subtype elements of constraint `c` on parent type `pt` are ones Table 11 or
  Table 12 allows for it, and so are those of the constraints inside them. `inPA`: within a
  "PermittedAlphabet" (Table 11 note a)). The constraints of X.682 have rules of their own. -/
  def ConsOk (E : Env) (H : ContentsHook) : Nat → Scope → Ty → Bool → Constraint → Prop
    | 0, _, _, _, _ => False
    | n + 1, sc, pt, inPA, .mk root _ adds =>
      ESetOk E H n sc pt inPA root ∧ ∀ a, adds = some a → ESetOk E H n sc pt inPA a
    -- X.682 11.3: a contents constraint is on a BIT STRING or OCTET STRING type
    | n + 1, sc, pt, _, .contents .. => match builtin E n sc pt with
      | some (_, .bitString _) | some (_, .octetString) => True
      | _ => False
    | _ + 1, _, _, _, _ => True

  def ESetOk (E : Env) (H : ContentsHook) : Nat → Scope → Ty → Bool → ElemSet → Prop
    | 0, _, _, _, _ => False
    | n + 1, sc, pt, inPA, .elem el => ElemOk E H n sc pt inPA el
    | n + 1, sc, pt, inPA, .union a b | n + 1, sc, pt, inPA, .inter a b
    | n + 1, sc, pt, inPA, .except a b =>
      ESetOk E H n sc pt inPA a ∧ ESetOk E H n sc pt inPA b
    | n + 1, sc, pt, inPA, .allExcept b => ESetOk E H n sc pt inPA b

  def ElemOk (E : Env) (H : ContentsHook) : Nat → Scope → Ty → Bool → Elem → Prop
    | 0, _, _, _, _ => False
    | n + 1, sc, pt, inPA, el =>
      ∃ sc' bt r, builtin E n sc pt = some (sc', bt) ∧ rowOf bt = some r ∧
        -- Table 11, Table 12, and note a)
        (r.allows el.kind ∨ (∃ k, r = .restricted k ∧ k.knownOrder ∧ inPA ∧ el.kind = .range)) ∧
        -- 51.7.3: within a permitted alphabet, only these four
        (inPA = true → el.kind ∈ [.single, .contained, .range, .size]) ∧
        match el with
        -- 51.2.1: the value is a value of the parent type, in its root (50.8, 50.10, 50.11)
        | .single v => (∃ w, evalVal E n sc v w ∧ (sem E H n sc [] pt).root w) ∧ RefMaps E n sc pt sc v
        -- 51.4.2: every value of the built-in type in the range is in the parent's root;
        -- 51.4.4 NOTE; 51.11–51.13
        | .range lo lo' hi hi' => ∃ l h, EvalBound E n sc lo l ∧ EvalBound E n sc hi h ∧
            (∀ w, (sem E H n sc' [] bt).all w → RangeHas l lo' h hi' w → (sem E H n sc [] pt).root w) ∧
            (inPA = true → SingleChar l ∧ SingleChar h) ∧
            (r = .time → timeRangeOk l h = true) ∧
            -- C.6.1: an end that is a value reference maps to the parent type
            (∀ v, lo = .val v → RefMaps E n sc pt sc v) ∧ (∀ v, hi = .val v → RefMaps E n sc pt sc v)
        -- 51.3.2: derived from the same built-in type
        | .contained t _ => ∃ sc'' bt', builtin E n sc t = some (sc'', bt') ∧ rowOf bt' = some r
        -- 51.5.3: the size constraint is on INTEGER (0..MAX)
        | .size c => c.isSubtype ∧ ConsOk E H n sc sizeParentTy false c
        -- 51.7.2: the alphabet constraint is on the parent type; 51.7.3
        | .from_ c => c.isSubtype ∧ ConsOk E H n sc pt true c
        | .withComponent c => match bt with
          | .sequenceOf et | .setOf et => ConsOk E H n sc' et false c
          | _ => False
        | .withComponents _ ncs =>
          -- Table 12 note: only on a duration subtype (38.4.4)
          (r = .time → ∀ v, (sem E H n sc [] pt).all v → ∃ t, v = .time t ∧ t.satisfies durationSettings) ∧
          let (isc, it) := innerTarget sc' bt
          -- 51.8.6: each named constraint names a component, at most once
          (ncs.map (·.1)).Nodup ∧
          (∀ nm oc p, (nm, oc, p) ∈ ncs → ∃ csc ct, (nm, csc, ct) ∈ structComps E n isc it ∧
            ∀ c, oc = some c → ConsOk E H n csc ct false c) ∧
          PresenceOk E n isc it ncs
        -- 51.10.3, 51.10.4, 51.10.6
        | .settings ps => settingsOk ps = true
        | _ => True
end

/-- X.680 51.1: the constraints in a constrained type. -/
def ConstraintsOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : Ty → Prop
  | .constrained t c => ConsOk E H n sc t false c
  | _ => True

/-! ## Information objects in types (X.681 14, 15; X.682 10) and the rest of the type rules -/

/-- X.681 14.1, Annex C, 9.14: the class of `C.&f` and of `INSTANCE OF C` exists, and the field
names a field of the class. -/
def ClassRefsOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .instanceOf (.ref mn name args) => (resolveClass E n sc mn name args).isSome
  | .classField cls path => ∃ cf, classFields E n sc cls = some cf ∧ (fieldAt E n cf path).isSome
  | _ => True

/-- X.681 15, X.680 14.1: the object set information is taken from exists. -/
def TypeFromObjectsOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .fromObjects os _ => ∀ r, ObjSetRef os r → r.Resolves E n sc
  | _ => True

/-- X.681 15.4, 15.5 Table 1, for "InformationFromObjects" written as a type: from an object, a
type field or a fixed-type value set field; from an object set, a fixed-type value or value set
field. The first part is an object set when written as a reference to one, or when the path goes
through an object set field. -/
def TypeFromObjectsTableOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .fromObjects src path => ∀ csc cls cf fsc f, objSetClass E n sc src = some (csc, cls) →
      classFields E n csc cls = some cf → fieldAt E n cf path = some (fsc, f) →
      let isSet := (∃ mn nm args, src = .ref mn nm args) ∨
        ∃ i, i + 1 < path.length ∧ ∃ x nm c o, fieldAt E n cf (path.take (i + 1)) = some (x, .objectSetField nm c o)
      match f with
      | .fixedValueSet .. => True
      | .typeField .. => ¬ isSet
      | .fixedValue .. => isSet
      | _ => False
  | _ => True

/-- X.683 9.2, X.681 11.3, 12.3: an object or object set given as an actual parameter names what
exists; a value given for a dummy whose governor is not an enumerated type or an INTEGER type with
named numbers (whose identifiers are not references) names values that exist. -/
def ArgsOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .paramRef mn name args =>
    (∀ o, Arg.obj o ∈ args → ∀ r, OElemsRef (.obj o) r → r.Resolves E n sc) ∧
    (∀ os, Arg.objSet os ∈ args → ∀ r, ObjSetRef os r → r.Resolves E n sc) ∧
    (mn = none → ∀ ps b, ParamAssign.type name ps b ∈ sc.mod.params →
      ∀ v p t, (Arg.value v, p) ∈ args.zip ps → p.governor = some (.type t) →
        match builtin E n sc t with
        | some (_, .enumerated ..) | some (_, .integer (_ :: _)) => True
        | _ => ValRefsOk E n sc v)
  | _ => True

/-- X.682 10.3: the object set of a table constraint exists. -/
def TableRefsOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .constrained _ (.table os _) => ∀ r, ObjSetRef os r → r.Resolves E n sc
  | _ => True

/-- X.682 10.4, 10.15: the object set of a table constraint is of the class of the
"ObjectClassFieldType" it constrains (both named classes). -/
def TableClassOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .constrained (.classField cls _) (.table os _) => ∀ osc c' a b,
      objSetClass E n sc os.unwrap = some (osc, c') → classKey E n sc cls = some a →
      classKey E n osc c' = some b → a = b
  | _ => True

/-- X.682 10.1: the type a table constraint is on is an "ObjectClassFieldType" or an
"InstanceOfType", through references, tags and other constraints. -/
def TableTarget (E : Env) : Nat → Scope → Ty → Prop
  | 0, _, _ => False
  | _ + 1, _, .classField .. | _ + 1, _, .instanceOf _ => True
  | n + 1, sc, .ref name => ∃ sc' t, resolveTy E n sc none name [] = some (sc', t) ∧ TableTarget E n sc' t
  | n + 1, sc, .extRef mn name => ∃ sc' t, resolveTy E n sc (some mn) name [] = some (sc', t) ∧ TableTarget E n sc' t
  | n + 1, sc, .paramRef mn name args => ∃ sc' t, resolveTy E n sc mn name args = some (sc', t) ∧ TableTarget E n sc' t
  | n + 1, sc, .tagged _ _ t | n + 1, sc, .constrained t _ => TableTarget E n sc t
  | _ + 1, _, _ => False

def TableOnFieldOk (E : Env) (n : Nat) (sc : Scope) : Ty → Prop
  | .constrained t (.table ..) => TableTarget E n sc t
  | _ => True

/-- X.680 31.2.5: a module does not write a tag of the UNIVERSAL class. -/
def UniversalTagOk : Ty → Prop
  | .tagged ⟨.universal, _⟩ _ _ => False
  | _ => True

/-- The rules for one type `s` occurring in an assignment, read in scope `sc`. Each field is a rule
the checker reports by name (`Rule.status`, Checker.lean). -/
structure TypeOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) (s : Ty) : Prop where
  names : NamesOk E H n sc s
  tags : TagsOk E H n sc s
  autoAdditions : AutoAdditionsOk sc s
  components : ComponentsOk E H n sc s
  refs : RefsOk E H n sc s
  nonEmpty : NonEmpty E H n sc s
  constraints : ConstraintsOk E H n sc s
  classRefs : ClassRefsOk E n sc s
  typeFromObjects : TypeFromObjectsOk E n sc s
  typeFromObjectsTable : TypeFromObjectsTableOk E n sc s
  args : ArgsOk E n sc s
  tableRefs : TableRefsOk E n sc s
  tableClass : TableClassOk E n sc s
  tableOnField : TableOnFieldOk E n sc s
  universalTag : UniversalTagOk s

/-! ## Component relation constraints (X.682 10.8–10.10, 10.15)

These need the types textually around a constraint, which `Occurs` does not keep. -/

/-- `Within anc t anc' s`: `s` is written inside `t`, and `anc'` are the SET, SEQUENCE, CHOICE, SET OF
and SEQUENCE OF types around it, innermost first (on top of `anc`, those around `t`). -/
inductive Within : List Ty → Ty → List Ty → Ty → Prop
  | here {anc t} : Within anc t anc t
  | seqComp {anc r e r2 nm ct p anc' s} :
      Comp.mk nm ct p ∈ r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2 →
      Within (.sequence r e r2 :: anc) ct anc' s → Within anc (.sequence r e r2) anc' s
  | setComp {anc r e r2 nm ct p anc' s} :
      Comp.mk nm ct p ∈ r ++ ((e.getD []).flatMap ExtAdd.comps) ++ r2 →
      Within (.set r e r2 :: anc) ct anc' s → Within anc (.set r e r2) anc' s
  | alt {anc r e a anc' s} : a ∈ choiceAlts r e → Within (.choice r e :: anc) a.ty anc' s →
      Within anc (.choice r e) anc' s
  | seqOf {anc et anc' s} : Within (.sequenceOf et :: anc) et anc' s → Within anc (.sequenceOf et) anc' s
  | setOf {anc et anc' s} : Within (.setOf et :: anc) et anc' s → Within anc (.setOf et) anc' s
  | tagged {anc tg k u anc' s} : Within anc u anc' s → Within anc (.tagged tg k u) anc' s
  | constrained {anc u c anc' s} : Within anc u anc' s → Within anc (.constrained u c) anc' s

/-- X.682 10.10: the structure an "AtNotation" starts from: a) the outermost enclosing SET,
SEQUENCE or CHOICE; b) from the innermost SET or SEQUENCE, up one level for each dot after the
first. -/
def atParent (anc : List Ty) (a : AtRef) : Option Ty :=
  let isStruct (t : Ty) : Bool := match t with
    | .sequence .. | .set .. | .choice .. => true
    | _ => false
  let isSeqSet (t : Ty) : Bool := match t with
    | .sequence .. | .set .. => true
    | _ => false
  match a.level with
  | none => (anc.filter isStruct).getLast?
  | some k => match anc.findIdx? isSeqSet with
    | some i => anc[i + k]?
    | none => none

/-- X.682 10.8, 10.9, 10.15: each name of the path is a component of the structure reached so far,
and the last is an "ObjectClassFieldType" constrained by the same object set `os`. -/
def AtWalk (E : Env) (n : Nat) (os : ObjSet) : Scope → Ty → List String → Prop
  | _, _, [] => True
  | sc, t, [id] => ∃ cs x csc ct os', compsOf E n sc t = some cs ∧ cs.find? (·.1 == id) = some (x, csc, ct) ∧
      tableOn E n n csc ct = some (some os') ∧ os'.unwrap = os.unwrap
  | sc, t, id :: rest => ∃ cs x csc ct, compsOf E n sc t = some cs ∧ cs.find? (·.1 == id) = some (x, csc, ct) ∧
      AtWalk E n os csc ct rest

/-- X.682 10.8–10.10, 10.15: every "AtNotation" of every component relation constraint written in
`t`. -/
def AtPathsOk (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Prop :=
  ∀ anc s, Within [] t anc s → ∀ u os refs, s = .constrained u (.table os refs) →
    ∀ a ∈ refs, ∃ p, atParent anc a = some p ∧ AtWalk E n os sc p a.path

/-- The rules for a type a module writes (a `Module.Site`, or a type in a parameterized body), read
in scope `sc`. -/
structure SiteOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) (t : Ty) : Prop where
  atPaths : AtPathsOk E n sc t
  types : ∀ s, Occurs t s → TypeOk E H n sc s

/-! ## Classes, objects and object sets (X.681 9–12) -/

/-- X.681 9.4, 14.1: the class of an object or object set field exists; 9.8, 9.10: the type field a
variable-type field names is a field of the class. -/
def FieldClassesOk (E : Env) (n : Nat) (sc : Scope) : ClassRef → Prop
  | .defn fs _ => ∀ f ∈ fs, match f with
    | .objectField _ (.ref mn name args) _ | .objectSetField _ (.ref mn name args) _ =>
      (resolveClass E n sc mn name args).isSome
    | .varValue _ [p] _ | .varValueSet _ [p] _ => ∃ o, FieldSpec.typeField p o ∈ fs
    | _ => True
  | _ => True

/-- X.681 9.6, X.680 16.2, C.6.1: the DEFAULT of a fixed-type value field is a value of its type. -/
def FieldDefaultsOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : ClassRef → Prop
  | .defn fs _ => ∀ nm t u v, FieldSpec.fixedValue nm t u (some (some v)) ∈ fs →
      (∃ w, evalVal E n sc v w ∧ (sem E H n sc [] t).all w) ∧ ValMaps E n n sc t sc v
  | _ => True

/-- The rules for a class assignment. -/
structure ClassOk (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) (c : ClassRef) : Prop where
  fieldClasses : FieldClassesOk E n sc c
  fieldDefaults : FieldDefaultsOk E H n sc c

/-- The field names a "SyntaxList" uses (X.681 10.7), in optional groups too. -/
def synFields : List SynItem → List String
  | [] => []
  | .field f :: r => f :: synFields r
  | .optional g :: r => synFields g ++ synFields r
  | .literal _ :: r => synFields r

/-- X.681 10.12 a): each optional group holds a field or a group. -/
def SynGroupsOk : List SynItem → Prop
  | [] => True
  | .optional g :: r => (∃ i ∈ g, ∀ w, i ≠ .literal w) ∧ SynGroupsOk g ∧ SynGroupsOk r
  | _ :: r => SynGroupsOk r

/-- The rules a class definition's own notation follows: X.681 9.6, UNIQUE is not with DEFAULT;
10.9, WITH SYNTAX names each field of the class exactly once, and no other; 10.12 a). The grammar
decides them (a module that breaks one does not read). -/
structure ClassSyntaxOk (c : ClassRef) : Prop where
  uniqueNoDefault : ∀ fs syn, c = .defn fs syn → ∀ nm t d, FieldSpec.fixedValue nm t true (some d) ∉ fs
  syntaxFields : ∀ fs items, c = .defn fs (some items) →
    (∀ f ∈ synFields items, f ∈ fs.map FieldSpec.name) ∧ ∀ f ∈ fs.map FieldSpec.name, (synFields items).count f = 1
  optionalGroups : ∀ fs items, c = .defn fs (some items) → SynGroupsOk items

/-- X.681 11.5, 11.6: an object has a setting for each mandatory field of its class. -/
def ObjV.FieldsSet (o : ObjV) : Prop := ∀ f ∈ o.fields, f.mandatory = true → ∃ st, (f.name, st) ∈ o.settings

/-- X.681 11.7, X.680 14.1: the references an object's settings use name what exists. -/
def ObjV.SettingRefsOk (E : Env) (n : Nat) (o : ObjV) : Prop :=
  ∀ f st, (f, st) ∈ o.settings → match st with
    | .value v => ValRefsOk E n o.sc v
    | .object ob => ∀ r, OElemsRef (.obj ob) r → r.Resolves E n o.sc
    | .objectSet s => ∀ r, ObjSetRef s r → r.Resolves E n o.sc
    | _ => True

/-- Two settings that are one: values that denote one value, types of one built-in type, other
settings written alike. -/
def SettingSame (E : Env) (n : Nat) (asc bsc : Scope) : Setting → Setting → Prop
  | .value v, .value w => ∃ x, evalVal E n asc v x ∧ evalVal E n bsc w x
  | .type t, .type u => (builtin E n asc t).bind (builtinName ·.2) = (builtin E n bsc u).bind (builtinName ·.2)
  | a, b => a = b

/-- Two objects that are one object (X.681 9.7): the same fields set, and alike. -/
def ObjV.Same (E : Env) (n : Nat) (a b : ObjV) : Prop :=
  (∀ f, f ∈ a.settings.map (·.1) ↔ f ∈ b.settings.map (·.1)) ∧
  ∀ f sa sb, (f, sa) ∈ a.settings → (f, sb) ∈ b.settings → SettingSame E n a.sc b.sc sa sb

/-- X.681 9.7: in an object set, two objects with one value of a UNIQUE field are one object. -/
def UniqueOk (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) (os : ObjSet) : Prop :=
  ∀ cf, classFields E n sc cls = some cf → ∀ f t, (f, t) ∈ uniqueFields cf.2 →
    ∀ a b, (evalObjSet E n sc (some cf) os).a a → (evalObjSet E n sc (some cf) os).a b →
      (∃ va vb x, (f, Setting.value va) ∈ a.settings ∧ (f, Setting.value vb) ∈ b.settings ∧
        evalVal E n a.sc va x ∧ evalVal E n b.sc vb x) →
      a.Same E n b

/-- X.681 11.1, 12.1, 14.1: the class an object or object set assignment names exists. -/
def ClassResolves (E : Env) (n : Nat) (sc : Scope) : ClassRef → Prop
  | .ref mn cn args => (resolveClass E n sc mn cn args).isSome
  | _ => True

/-- The rules for an object assignment `o` of class `cls`. -/
structure ObjOk (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) (o : Obj) : Prop where
  /-- X.681 11.3, 14.1 -/
  ref : ∀ r, OElemsRef (.obj o) r → r.Resolves E n sc
  clsResolves : ClassResolves E n sc cls
  fields : ∀ x, evalObj E n sc (classFields E n sc cls) o x → x.FieldsSet
  settingRefs : ∀ x, evalObj E n sc (classFields E n sc cls) o x → x.SettingRefsOk E n

/-- `OElemsWrites e o`: object `o` is written in the elements `e` of an object set, in an object set
written inside them too (X.681 12.3, 12.10), whether or not the set arithmetic keeps it: X.681 11
applies to every object definition. -/
inductive OElemsWrites : OElems → Obj → Prop
  | obj {o} : OElemsWrites (.obj o) o
  | root {r x a o} : OElemsWrites r o → OElemsWrites (.set (.spec (some r) x a)) o
  | addition {r x a o} : OElemsWrites a o → OElemsWrites (.set (.spec r x (some a))) o
  | unionL {a b o} : OElemsWrites a o → OElemsWrites (.union a b) o
  | unionR {a b o} : OElemsWrites b o → OElemsWrites (.union a b) o
  | interL {a b o} : OElemsWrites a o → OElemsWrites (.inter a b) o
  | interR {a b o} : OElemsWrites b o → OElemsWrites (.inter a b) o
  | exceptL {a b o} : OElemsWrites a o → OElemsWrites (.except a b) o
  | exceptR {a b o} : OElemsWrites b o → OElemsWrites (.except a b) o

/-- The objects written in an object set's root or additions. -/
def ObjSet.Writes (os : ObjSet) (o : Obj) : Prop :=
  ∃ r x a, os = .spec r x a ∧ ((∃ e, r = some e ∧ OElemsWrites e o) ∨ (∃ e, a = some e ∧ OElemsWrites e o))

/-- The rules for an object set assignment `os` of class `cls`. -/
structure ObjSetOk (E : Env) (n : Nat) (sc : Scope) (cls : ClassRef) (os : ObjSet) : Prop where
  clsResolves : ClassResolves E n sc cls
  /-- X.681 12 -/
  refs : ∀ r, ObjSetRef os r → r.Resolves E n sc
  unique : UniqueOk E n sc cls os
  fields : ∀ o, os.Writes o → ∀ x, evalObj E n sc (classFields E n sc cls) o x → x.FieldsSet
  settingRefs : ∀ o, os.Writes o → ∀ x, evalObj E n sc (classFields E n sc cls) o x → x.SettingRefsOk E n

/-! ## Rules on a module as a whole -/

/-- The reference names a module assigns: types and value sets (X.680 16.1, 16.6), values (16.2),
classes, objects and object sets (X.681 9.1, 11.1, 12.1), and parameterized assignments (X.683
8.1). -/
def Module.assignedNames (m : Module) : List String :=
  m.types.map (·.1) ++ m.values.map (·.1) ++ m.classes.map (·.1) ++ m.objects.map (·.1) ++
    m.objectSets.map (·.1) ++ m.params.map (·.name)

/-- X.680 3.8.88, 3.8.93: a reference name is "associated uniquely" with what it names, so a module
assigns each name once. -/
def AssignedOnce (m : Module) : Prop := m.assignedNames.Nodup

/-- X.680 16.2, 16.3: the value of a value assignment is a value of its type; C.6.1: the
references in it map to the types that govern them. -/
def ValuesOk (E : Env) (H : ContentsHook) (n : Nat) (m : Module) : Prop :=
  ∀ nm t v, (nm, t, v) ∈ m.values →
    (∃ w, evalVal E n (.ofModule m) v w ∧ (sem E H n (.ofModule m) [] t).all w) ∧
    ValMaps E n n (.ofModule m) t (.ofModule m) v

/-- X.680 16.1, 3.8.61: following the references from a type, through tags and constraints (which
construct nothing), ends in a type within `k` steps. A type defined through itself only (`T ::= T`,
`T ::= [0] T (1..5)`) is no type. A dummy reference, or a reference that does not resolve (which
`RefsOk` reports), ends the chain. -/
def RefChainEnds (E : Env) (n : Nat) : Nat → Scope → Ty → Prop
  | 0, _, _ => False
  | k + 1, sc, .ref name => (sc.bound name).isSome ∨
      ∀ sc' t, resolveTy E n sc none name [] = some (sc', t) → RefChainEnds E n k sc' t
  | k + 1, sc, .extRef mn name =>
      ∀ sc' t, resolveTy E n sc (some mn) name [] = some (sc', t) → RefChainEnds E n k sc' t
  | k + 1, sc, .tagged _ _ t | k + 1, sc, .constrained t _ => RefChainEnds E n k sc t
  | _ + 1, _, _ => True

/-- X.680 13.16 a): each imported symbol is assigned in the module it is imported from, or imported
by that module once. -/
def ImportsOk (E : Env) (m : Module) : Prop :=
  ∀ sym mn, (sym, mn) ∈ m.imports → ∃ m', E.findFrom m mn = some m' ∧
    (sym ∈ m'.assignedNames ∨ (m'.imports.filter (·.1 == sym)).length = 1)

/-- X.680 13.13 a): each exported symbol is assigned in the module, or imported by it once. -/
def ExportsOk (m : Module) : Prop :=
  ∀ sym ∈ m.exports.getD [], sym ∈ m.assignedNames ∨ (m.imports.filter (·.1 == sym)).length = 1

/-- X.680 53.4, 14.1: the defined value of an exception spec names a value, or is a dummy
reference. -/
def ExceptionRefsOk (E : Env) (n : Nat) (m : Module) : Prop :=
  ∀ mn v, (mn, v) ∈ m.exceptionRefs → (resolveVal E n (.ofModule m) mn v []).isSome ∨
    ∃ pa ∈ m.params, ∃ p ∈ pa.paramList, p.name = v

/-- X.683 8.3, X.680 14.1: a class that governs a parameter exists (or is an earlier dummy); the
references of a type that governs one resolve. -/
def ParamGovsOk (E : Env) (H : ContentsHook) (n : Nat) (m : Module) (pa : ParamAssign) : Prop :=
  ∀ p ∈ pa.paramList, match p.governor with
    | some (.cls (.ref mn name args)) =>
      (resolveClass E n (.ofModule m) mn name args).isSome ∨ ∃ q ∈ pa.paramList, q.name = name
    | some (.type t) => ∀ s, Occurs t s → RefsOk E H n (.ofModule m) s
    | _ => True

/-- X.683 8.10: the right side of a parameterized type assignment is not only a dummy reference. -/
def ParamAssign.NotOnlyDummy : ParamAssign → Prop
  | .type _ ps (.ref r) => r ∉ ps.map (·.name)
  | _ => True

/-- The class definitions a module writes: assigned, or the right side of a parameterized class
assignment. -/
def Module.ClassWritten (m : Module) (c : ClassRef) : Prop :=
  (∃ nm, (nm, c) ∈ m.classes) ∨ ∃ nm ps, ParamAssign.cls nm ps c ∈ m.params

/-- X.683 8.3, 8.5, 8.12: an actual parameter of the kind a dummy reference with governor `g`
stands for: a type or a class (no governor); a value of the governing type, or a value set (a type
governor); an object or object set (a class governor); any of these (a dummy governor, 8.9). -/
def ArgFits (E : Env) (H : ContentsHook) (n : Nat) (sc : Scope) : Option ParamGov → Arg → Prop
  | none, .type _ | none, .cls _ => True
  | some (.type g), .value v => ∃ w, evalVal E n sc v w ∧ (sem E H n sc [] g).all w
  | some (.type _), .valueSet _ => True
  | some (.cls _), .obj _ | some (.cls _), .objSet _ => True
  | some (.dummy _), .value _ | some (.dummy _), .valueSet _
  | some (.dummy _), .obj _ | some (.dummy _), .objSet _ => True
  | _, _ => False

/-- All the rules, for every type, class, object and object set module `m` writes, at fuel `n`.
The bodies of parameterized assignments are in `Env.Valid.params`. -/
structure Module.ValidAt (m : Module) (E : Env) (H : ContentsHook) (n : Nat) : Prop where
  assignedOnce : AssignedOnce m
  values : ValuesOk E H n m
  typeChains : ∀ nm t, (nm, t) ∈ m.types → RefChainEnds E n n (.ofModule m) t
  /-- X.680 13.16 e) i): a module is imported from once, and not from itself -/
  importsOnce : (m.name :: m.importMods).Nodup
  imports : ImportsOk E m
  exports : ExportsOk m
  exceptionRefs : ExceptionRefsOk E n m
  types : ∀ nm t, m.Site nm t → SiteOk E H n (.ofModule m) t
  paramGovs : ∀ pa ∈ m.params, ParamGovsOk E H n m pa
  paramBodies : ∀ pa ∈ m.params, pa.NotOnlyDummy
  classes : ∀ nm c, (nm, c) ∈ m.classes → ClassOk E H n (.ofModule m) c
  classSyntax : ∀ c, m.ClassWritten c → ClassSyntaxOk c
  objects : ∀ nm cls o, (nm, cls, o) ∈ m.objects → ObjOk E n (.ofModule m) cls o
  objectSets : ∀ nm cls os, (nm, cls, os) ∈ m.objectSets → ObjSetOk E n (.ofModule m) cls os

/-- X.680 13.7, 13.10: module names are used once in the sphere of interest, except by modules
with distinct definitive identifiers (13.10 imports them under other names). -/
def ModuleNamesOk (E : Env) : Prop :=
  E.Pairwise fun a b => a.name = b.name → ∃ x y, a.oid = some x ∧ b.oid = some y ∧ x ≠ y

/-- The body of parameterized assignment `pa` of module `m` read with actual parameters `args` its
governors allow (`bindParams`), at fuel `n`. -/
def ParamBodyOk (E : Env) (H : ContentsHook) (n : Nat) (m : Module) (pa : ParamAssign) (args : List Arg) :
    Prop :=
  List.Forall₂ (fun p a => ArgFits E H n (.ofModule m) p.governor a) pa.paramList args ∧
    ∀ t, pa.Has t → SiteOk E H n (bindParams m pa.paramList args (.ofModule m)) t

/-- A valid specification: module names (X.680 13.7), and every module valid, at every large enough
fuel.

A parameterized assignment is read with its dummy references standing for actual parameters
(`bindParams`). X.683 8.5: to check how the dummies are used, each "can be regarded to be defined"
as an unspecified thing of its kind and governor; 9.7: an instance is what its actual parameters
make it. So the body is valid when some actual parameters its governors allow make it so (at every
large enough fuel, as the other rules): a rule broken whatever the dummies stand for breaks it, and
a rule that depends on them is a rule on each instance. -/
structure Env.Valid (E : Env) (H : ContentsHook) : Prop where
  moduleNames : ModuleNamesOk E
  modules : Eventually fun n => ∀ m ∈ E, m.ValidAt E H n
  params : ∀ m ∈ E, ∀ pa ∈ m.params, ∃ args, Eventually fun n => ParamBodyOk E H n m pa args

end Asn1.X680
