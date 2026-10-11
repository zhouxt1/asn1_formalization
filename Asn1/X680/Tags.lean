import Asn1.X680.Semantics

/-!
# Tags (X.680 8, 25.2–25.10, 29.2–29.5, 31.2)

Tags do not change values, but encoding rules use them:
- X.691 orders CHOICE alternatives and SET components canonically by tag (10.2);
- BER, CER and DER put them on the wire.

This file gives:
- the universal tag of each built-in type;
- the tags of a type's values, which for an untagged CHOICE are those of all its alternatives;
- the automatic tagging transformation;
- implicit and explicit tagging;
- the canonical order.

Like the value sets, these take fuel, because a tag can be reached through references.
-/

namespace Asn1.X680

/-- X.680 8.4, Table 1, with the clause that gives each type its tag (18.2, 19.2, …). Types with no
tag of their own (CHOICE, a reference, a selection, an open type) have none here. -/
def Ty.universalTag? : Ty → Option Nat
  | .boolean => some 1
  | .integer _ => some 2
  | .bitString _ => some 3
  | .octetString => some 4
  | .null => some 5
  | .objectIdentifier => some 6
  | .objectDescriptor => some 7
  | .external => some 8
  | .real => some 9
  | .enumerated _ _ => some 10
  | .embeddedPdv => some 11
  | .restricted .utf8 => some 12
  | .relativeOid => some 13
  | .time => some 14
  | .sequence _ _ _ | .sequenceOf _ => some 16
  | .set _ _ _ | .setOf _ => some 17
  | .restricted .numeric => some 18
  | .restricted .printable => some 19
  | .restricted .teletex => some 20
  | .restricted .videotex => some 21
  | .restricted .ia5 => some 22
  | .utcTime => some 23
  | .generalizedTime => some 24
  | .restricted .graphic => some 25
  | .restricted .visible => some 26
  | .restricted .general => some 27
  | .restricted .universal => some 28
  | .characterString => some 29
  | .restricted .bmp => some 30
  | .date => some 31
  | .timeOfDay => some 32
  | .dateTime => some 33
  | .duration => some 34
  | .oidIri => some 35
  | .relativeOidIri => some 36
  | _ => none

/-! ## The canonical order (8.6) -/

/-- X.680 8.6 a): universal, application, context-specific, private. -/
def TagClass.rank : TagClass → Nat
  | .universal => 0
  | .application => 1
  | .context => 2
  | .private_ => 3

/-- X.680 8.6: `a` comes before `b` in the canonical order: by class (a), then by number (b). -/
def Tag.lt (a b : Tag) : Bool :=
  a.cls.rank < b.cls.rank || (a.cls.rank == b.cls.rank && a.num < b.num)

/-! ## Automatic tagging (25.2–25.4, 25.8–25.10, 29.2, 29.5) -/

/-- X.680 25.2: a textually tagged type. Encoding prefixes (31.3) are not represented, so only a
"TaggedType" is. -/
def Ty.textuallyTagged : Ty → Bool
  | .tagged _ _ _ => true
  | _ => false

def Comp.textuallyTagged : Comp → Bool
  | .mk _ t _ => t.textuallyTagged
  | .componentsOf _ => false

/-- X.680 25.3: automatic tagging is selected for a "ComponentTypeLists" when the module has
AUTOMATIC TAGS and none of its components (not counting COMPONENTS OF, the fourth alternative)
is textually tagged. 25.4: this is decided on the components as written, before COMPONENTS OF is
expanded. -/
def autoSeq (td : TagDefault) (root : List Comp) (ext : Option (List ExtAdd)) (root2 : List Comp) :
    Bool :=
  td == .automatic &&
    !(root ++ (ext.getD []).flatMap ExtAdd.comps ++ root2).any Comp.textuallyTagged

/-- X.680 29.2: the same for an "AlternativeTypeLists". -/
def autoChoice (td : TagDefault) (root : List Alt) (ext : Option (List AltAdd)) : Bool :=
  td == .automatic && !(choiceAlts root ext).any fun a => a.ty.textuallyTagged

/-- X.680 25.10 c), d), and 29.5 c), d): the tag numbers that automatic tagging gives a list of
`r` root items followed by its extension additions: `0 … r-1` for the root, and the additions from
`r` on, one greater than the largest root number (or from 0 when there is no root).

OPEN (ledger X680-10): 25.10 c) numbers "the RootComponentTypeList", and a SEQUENCE may have two.
Both root lists are numbered first, in textual order, then the additions. -/
def autoNumber (isAddition : List Bool) : List Nat :=
  let r := (isAddition.filter (! ·)).length
  (isAddition.foldl (fun (acc : List Nat × Nat × Nat) add =>
      let (out, nr, na) := acc
      if add then (out ++ [r + na], nr, na + 1) else (out ++ [nr], nr + 1, na))
    ([], 0, 0)).1

/-! ## The tags of a type -/

/-- Whether a type, followed through references and constraints, is a "TaggedType" (31.2): `builtin`
looks through tags, this does not. -/
def hasTag (E : Env) : Nat → Scope → Ty → Bool
  | 0, _, _ => false
  | _ + 1, _, .tagged .. => true
  | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
    | some (sc', t) => hasTag E n sc' t
    | none => false
  | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => hasTag E n sc' t
    | none => false
  | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
    | some (sc', t) => hasTag E n sc' t
    | none => false
  | n + 1, sc, .constrained t _ => hasTag E n sc t
  | n + 1, sc, .selection nm t => match builtin E n sc t with
    | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
      | some a => hasTag E n sc' a.ty
      | none => false
    | _ => false
  | _ + 1, _, _ => false

/-- X.680 52.7: an untagged CHOICE that is extensible gets a conceptually-added alternative, so its
tags (29.8, 29.9) include that element's tag (52.7.3), and so do those of an untagged CHOICE with
such an alternative, unless automatic tagging tags the alternatives (52.8.3). -/
def carriesConceptual (E : Env) : Nat → Scope → Ty → Bool
  | 0, _, _ => false
  | n + 1, sc, t => !hasTag E n sc t && match builtin E n sc t with
    | some (sc', .choice r e) => e.isSome || sc'.mod.header.extImplied ||
      (!autoChoice sc'.mod.header.tagDefault r e &&
        (choiceAlts r e).any fun a => carriesConceptual E n sc' a.ty)
    | _ => false

/-- X.680 31.2.7 c) and 31.2.9: whether a type is an untagged CHOICE, an untagged open type
(including a type field of a class, X.681 14.2) or an untagged "DummyReference" (X.683 8.3), the
cases where a tag must be explicit. -/
def untaggedChoiceOrOpen (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Bool :=
  let choiceOrOpen := !hasTag E n sc t && match builtin E n sc t with
    | some (_, .choice _ _) | some (_, .openType) => true
    | _ => false
  match t with
  -- an untagged "DummyReference" (X.683 8.3)
  | .ref name => (sc.bound name).isSome || choiceOrOpen
  | _ => choiceOrOpen

/-- X.680 31.2.7: whether a "TaggedType" written as `kind` around `inner`, in scope `sc`, is
explicit tagging (otherwise it is implicit). Automatic tagging writes its tags in the "Tag Type"
form (25.10 a), 29.5 a)), which is `kind = default_`. -/
def isExplicit (E : Env) (n : Nat) (sc : Scope) (kind : TagKind) (inner : Ty) : Bool :=
  match kind with
  | .explicit => true
  | .implicit => false
  | .default_ => sc.mod.header.tagDefault == .explicit || untaggedChoiceOrOpen E n sc inner

mutual
  /-- The possible tags of the values of a type read in scope `sc`. A tagged or built-in type has
  one. An untagged CHOICE has the tags of all its alternatives (29.8, 29.9). An open type's tag is
  indeterminate (X.681 14.2 NOTE 2): `none`. -/
  def tagsOf (E : Env) : Nat → Scope → Ty → Option (List Tag)
    | 0, _, _ => some []
    | _ + 1, _, .tagged tg _ _ => some [tg]
    | n + 1, sc, .ref name => match resolveTy E n sc none name [] with
      | some (sc', t) => tagsOf E n sc' t
      | none => some []
    | n + 1, sc, .extRef mn name => match resolveTy E n sc (some mn) name [] with
      | some (sc', t) => tagsOf E n sc' t
      | none => some []
    | n + 1, sc, .paramRef mn name args => match resolveTy E n sc mn name args with
      | some (sc', t) => tagsOf E n sc' t
      | none => some []
    | n + 1, sc, .constrained t _ => tagsOf E n sc t
    | n + 1, sc, .selection nm t => match builtin E n sc t with
      | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
        | some a => tagsOf E n sc' a.ty
        | none => some []
      | _ => some []
    | n + 1, sc, .choice root ext =>
      ((altTags E n sc root ext).map (·.2)).foldr
        (fun ts acc => match ts, acc with
          | some a, some b => some (a ++ b)
          | _, _ => none) (some [])
    | _ + 1, _, .openType => none
    -- X.681 14.2–14.4: a type field is an open type; a fixed-type field has its type's tags
    | n + 1, sc, .classField cls path =>
      match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => tagsOf E n sc' t
      | _ => none
    -- X.681 C.4, X.680 Table 1: UNIVERSAL 8, as EXTERNAL
    | _ + 1, _, .instanceOf _ => some [⟨.universal, 8⟩]
    -- X.681 15.7, 15.8: a value set from objects has the tags of the fixed-type field's type.
    -- OPEN (ledger X681-1): a type from objects (a type field) has the tag of the row's type, so
    -- none here.
    | n + 1, sc, .fromObjects src path => match objSetClass E n sc src with
      | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
        | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => tagsOf E n sc' t
        | _ => none
      | none => none
    | _ + 1, _, t => some ((t.universalTag?.map fun k => [⟨.universal, k⟩]).getD [])

  /-- Each alternative of a CHOICE read in scope `sc`, with its tags once automatic tagging is
  applied (29.2, 29.5). -/
  def altTags (E : Env) : Nat → Scope → List Alt → Option (List AltAdd) →
      List (Alt × Option (List Tag))
    | 0, _, _, _ => []
    | n + 1, sc, root, ext =>
      let alts := choiceAlts root ext
      if autoChoice sc.mod.header.tagDefault root ext then
        (alts.zip (autoNumber (root.map (fun _ => false) ++
            (alts.drop root.length).map (fun _ => true)))).map
          fun (a, k) => (a, some [⟨.context, k⟩])
      else alts.map fun a => (a, tagsOf E n sc a.ty)
end

/-- Each component of a SEQUENCE or SET read in scope `sc`, after COMPONENTS OF is expanded, with
its tags once automatic tagging is applied (25.3, 25.8–25.10). The decision is that of the module
the SEQUENCE is written in (25.3), and a component copied by COMPONENTS OF is tagged by it too
(25.10 NOTE 3). -/
def entryTags (E : Env) (n : Nat) (sc : Scope) (root : List Comp) (ext : Option (List ExtAdd))
    (root2 : List Comp) : List (Entry × Option (List Tag)) :=
  let es := entries E n sc root ext root2
  if autoSeq sc.mod.header.tagDefault root ext root2 then
    -- 25.10 numbers the root (both lists, OPEN X680-10) before the additions
    (es.zip (autoNumber (es.map (·.addition.isSome)))).map fun (e, k) => (e, some [⟨.context, k⟩])
  else es.map fun e => (e, tagsOf E n e.scope e.ty)

/-- The tags of the values of `t`, written in module `m`, in the limit of fuel. -/
def TagsOf (E : Env) (m : Module) (t : Ty) (ts : Option (List Tag)) : Prop :=
  Eventually fun n => tagsOf E n (.ofModule m) t = ts

end Asn1.X680
