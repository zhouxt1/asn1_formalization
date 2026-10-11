import Asn1.X680.Semantics

/-!
# The format model shared by every encoding rule

An encoding rule is a *relation* between abstract values and bit strings. Where the text leaves the
encoder a choice (X.690 8.1.3 length forms, X.691 19.5 DEFAULT components, …), the relation allows
every choice. A canonical rule (CER, DER, CANONICAL-PER) is the same relation with the choices
fixed.

The properties below are stated once, for any rule; each encoding rule proves them (or is shown not
to have them) for every schema. Values are compared by `Equiv`, the equality of abstract values
(X.680 25.12, 28, 22.7, 38.2.3), not by their notation.
-/

namespace Asn1

open Asn1.X680

/-- An encoding rule. -/
structure EncodingRule where
  /-- What the rule says a contents constraint means (X.682 11.4): its own encodings, which depend
  on the specification the contained type is resolved in. -/
  hook : Env → ContentsHook
  /-- `Encodes E m t v bs`: `bs` is a complete encoding of the value `v` of type `t`, `t` written in
  module `m` of the specification `E`. -/
  Encodes : Env → Module → Ty → Val → Bits → Prop

namespace EncodingRule

variable (R : EncodingRule) (E : Env) (m : Module) (t : Ty)

/-- Only values of the type have encodings. -/
def EncodesValues : Prop := ∀ v bs, R.Encodes E m t v bs → Has E (R.hook E) m t v

/-- **Completeness**: every value of the type has an encoding. -/
def Complete : Prop := ∀ v, Has E (R.hook E) m t v → ∃ bs, R.Encodes E m t v bs

/-- **Unambiguity**: a bit string encodes at most one abstract value. -/
def Unambiguous : Prop := ∀ v w bs, R.Encodes E m t v bs → R.Encodes E m t w bs → Equiv E m t v w

/-- **Self-delimitation**: no encoding is a proper prefix of another (X.690 12.1, "self-delimiting";
X.691's complete encodings are self-delimiting only in octets, after 11.1's padding). -/
def PrefixFree : Prop :=
  ∀ v w bs rest, R.Encodes E m t v bs → R.Encodes E m t w (bs ++ rest) → rest = []

/-- **Canonicity**: one abstract value has one encoding. -/
def Canonical : Prop :=
  ∀ v w bs bs', R.Encodes E m t v bs → R.Encodes E m t w bs' → Equiv E m t v w → bs = bs'

/-- Every encoding under `R` is one under `R'`: a canonical rule refines its basic rule (X.690 9
and 10: "the basic encoding … together with the following restrictions"; X.691 7.5). -/
def Refines (R R' : EncodingRule) : Prop :=
  ∀ E m t v bs, R.Encodes E m t v bs → R'.Encodes E m t v bs

/-- **Extensibility** (X.680 7.1–7.3): two versions of a specification, `E` and its later version
`E'` (`Env.Extends`): what is encoded under the later version is decoded under the earlier one,
and what is encoded under the earlier one is decoded under the later one, to the same value.
Stated here only for values that both versions have. -/
def ExtensionCompatible (E E' : Env) (m m' : Module) (t t' : Ty) : Prop :=
  ∀ v bs, Has E (R.hook E) m t v → Has E' (R.hook E') m' t' v →
    (R.Encodes E m t v bs ↔ R.Encodes E' m' t' v bs)

end EncodingRule

end Asn1
