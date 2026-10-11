import Asn1.X680.Syntax

/-!
# Extension-related types (X.680 3.8.31–3.8.41, 6, 7, 52)

A later version of a specification adds extension additions at the insertion points of extensible
types (3.8.35):
- components or groups at the end of a SEQUENCE's or SET's additions;
- alternatives at the end of a CHOICE's additions;
- enumerations at the end of an ENUMERATED type's additional enumeration;
- one subtype element at a time to an extensible constraint (3.8.31).

Two types are extension-related when one was created from the other this way (3.8.38). Clause 7
requires every encoding rule to let a decoder using one of them decode the other's values. 7.3
requires this "when a type with an extension marker is nested inside some other type", so the
additions may be made anywhere inside a type, not only at its outer level.

`implied` is the module's EXTENSIBILITY IMPLIED (13.4), which puts an extension marker in every
type that can have one, so additions may be made where nothing is written.
-/

namespace Asn1.X680

/-- Two lists related element by element. -/
def ListRel {α β : Type} (R : α → β → Prop) (l : List α) (l' : List β) : Prop :=
  l.length = l'.length ∧ ∀ (i : Nat) x y, l[i]? = some x → l'[i]? = some y → R x y

/-- 3.8.31, 50: an extensible constraint gains subtype elements in its additions. -/
inductive ExtendsCons : Constraint → Constraint → Prop where
  | refl c : ExtendsCons c c
  | add {root adds} (new : ElemSet) :
      ExtendsCons (.mk root true adds)
        (.mk root true (some (match adds with
          | some a => .union a new
          | none => new)))

mutual
  /-- `ExtendsT implied t t'`: `t'` is `t` with zero or more extension additions inserted at
  insertion points inside it. -/
  inductive ExtendsT (implied : Bool) : Ty → Ty → Prop where
    | refl t : ExtendsT implied t t
    /-- 25: the components' types may be extended, and additions appended at the insertion point
    (3.8.35), which is the end of the additions, before any trailing root components -/
    | sequence {r r' : List Comp} {e : Option (List ExtAdd)} {adds' new : List ExtAdd}
        {r2 r2' : List Comp} :
        (∀ (i : Nat) x y, r[i]? = some x → r'[i]? = some y → ExtendsC implied x y) → r.length = r'.length →
        (e.isSome || implied) = true →
        (∀ (i : Nat) x y, (e.getD [])[i]? = some x → adds'[i]? = some y → ExtendsA implied x y) →
        (e.getD []).length = adds'.length →
        (∀ (i : Nat) x y, r2[i]? = some x → r2'[i]? = some y → ExtendsC implied x y) →
        r2.length = r2'.length →
        ExtendsT implied (.sequence r e r2) (.sequence r' (some (adds' ++ new)) r2')
    /-- 27, as 25 -/
    | set {r r' : List Comp} {e : Option (List ExtAdd)} {adds' new : List ExtAdd}
        {r2 r2' : List Comp} :
        (∀ (i : Nat) x y, r[i]? = some x → r'[i]? = some y → ExtendsC implied x y) → r.length = r'.length →
        (e.isSome || implied) = true →
        (∀ (i : Nat) x y, (e.getD [])[i]? = some x → adds'[i]? = some y → ExtendsA implied x y) →
        (e.getD []).length = adds'.length →
        (∀ (i : Nat) x y, r2[i]? = some x → r2'[i]? = some y → ExtendsC implied x y) →
        r2.length = r2'.length →
        ExtendsT implied (.set r e r2) (.set r' (some (adds' ++ new)) r2')
    /-- A SEQUENCE or SET without an extension marker can still have extensible components. -/
    | sequenceRoot {r r' : List Comp} {r2 r2' : List Comp} :
        (∀ (i : Nat) x y, r[i]? = some x → r'[i]? = some y → ExtendsC implied x y) → r.length = r'.length →
        (∀ (i : Nat) x y, r2[i]? = some x → r2'[i]? = some y → ExtendsC implied x y) →
        r2.length = r2'.length →
        ExtendsT implied (.sequence r none r2) (.sequence r' none r2')
    | setRoot {r r' : List Comp} {r2 r2' : List Comp} :
        (∀ (i : Nat) x y, r[i]? = some x → r'[i]? = some y → ExtendsC implied x y) → r.length = r'.length →
        (∀ (i : Nat) x y, r2[i]? = some x → r2'[i]? = some y → ExtendsC implied x y) →
        r2.length = r2'.length →
        ExtendsT implied (.set r none r2) (.set r' none r2')
    /-- 29: the alternatives' types may be extended, and alternatives appended -/
    | choice {r r' : List Alt} {e : Option (List AltAdd)} {adds' new : List AltAdd} :
        (∀ (i : Nat) x y, r[i]? = some x → r'[i]? = some y → ExtendsAlt implied x y) → r.length = r'.length →
        (∀ (i : Nat) x y, (e.getD [])[i]? = some x → adds'[i]? = some y → ExtendsAA implied x y) →
        (e.getD []).length = adds'.length →
        (e.isSome || implied || new.isEmpty) = true →
        ExtendsT implied (.choice r e) (.choice r' (if e.isNone && new.isEmpty then none
          else some (adds' ++ new)))
    /-- 20: enumerations appended to the additional enumeration -/
    | enumerated {r : List (String × Option Int)} {e : Option (List (String × Option Int))}
        {new : List (String × Option Int)} :
        (e.isSome || implied) = true →
        ExtendsT implied (.enumerated r e) (.enumerated r (some (e.getD [] ++ new)))
    | sequenceOf {t t'} : ExtendsT implied t t' → ExtendsT implied (.sequenceOf t) (.sequenceOf t')
    | setOf {t t'} : ExtendsT implied t t' → ExtendsT implied (.setOf t) (.setOf t')
    | tagged {tg k t t'} : ExtendsT implied t t' → ExtendsT implied (.tagged tg k t) (.tagged tg k t')
    /-- 3.8.31: one or more subtype elements added to an extensible constraint's additions, and
    the parent type extended -/
    | constrained {t t' : Ty} {c c' : Constraint} :
        ExtendsT implied t t' → ExtendsCons c c' →
        ExtendsT implied (.constrained t c) (.constrained t' c')

  /-- A component, with its type extended. -/
  inductive ExtendsC (implied : Bool) : Comp → Comp → Prop where
    | mk {nm t t' p} : ExtendsT implied t t' → ExtendsC implied (.mk nm t p) (.mk nm t' p)
    | componentsOf {t} : ExtendsC implied (.componentsOf t) (.componentsOf t)

  /-- An extension addition, with its types extended. -/
  inductive ExtendsA (implied : Bool) : ExtAdd → ExtAdd → Prop where
    | one {c c'} : ExtendsC implied c c' → ExtendsA implied (.one c) (.one c')
    | group {v} {cs cs' : List Comp} :
        (∀ (i : Nat) x y, cs[i]? = some x → cs'[i]? = some y → ExtendsC implied x y) →
        cs.length = cs'.length → ExtendsA implied (.group v cs) (.group v cs')

  inductive ExtendsAlt (implied : Bool) : Alt → Alt → Prop where
    | mk {nm t t'} : ExtendsT implied t t' → ExtendsAlt implied (.mk nm t) (.mk nm t')

  inductive ExtendsAA (implied : Bool) : AltAdd → AltAdd → Prop where
    | one {a a'} : ExtendsAlt implied a a' → ExtendsAA implied (.one a) (.one a')
    | group {v} {as as' : List Alt} :
        (∀ (i : Nat) x y, as[i]? = some x → as'[i]? = some y → ExtendsAlt implied x y) →
        as.length = as'.length → ExtendsAA implied (.group v as) (.group v as')

end

/-- X.680 3.8.38: two types are extension-related when one was created from the other by adding
extension additions. -/
def ExtRelated (implied : Bool) (t t' : Ty) : Prop := ExtendsT implied t t' ∨ ExtendsT implied t' t

/-- A later version of a module: every type assignment kept, each one extended, and possibly new
assignments. -/
def Module.Extends (m m' : Module) : Prop :=
  m'.name = m.name ∧ m'.header = m.header ∧ m'.imports = m.imports ∧
  ∀ nm t, m.lookup nm = some t → ∃ t', m'.lookup nm = some t' ∧ ExtendsT m.header.extImplied t t'

/-- A later version of a specification, module by module. -/
def Env.Extends (E E' : Env) : Prop :=
  ∀ m ∈ E, ∃ m' ∈ E', Module.Extends m m'

end Asn1.X680
