import Asn1.Format
import Asn1.X680.Tags
import Asn1.X680.Enumerated
import Asn1.X690.Contents

/-!
# BER, CER and DER (X.690 8–11)

An encoding (8.1.1) is identifier octets, length octets, contents octets and, for the indefinite
length form, end-of-contents octets. `Node` is that structure: a primitive encoding with its
contents octets, or a constructed one with the encodings it contains. `Node.octets` lays it out
(8.1.1–8.1.5); nothing else is needed to turn a node into octets, so a node *is* an encoding.

`ber E p n sc t v nd` says `nd` is an encoding of the value `v` of type `t` (written in scope `sc`)
under profile `p`. It allows every choice clause 8 leaves to the sender; CER and DER fix them, by
the restrictions of clauses 9, 10 and 11, each placed where the choice is made. Length forms are
checked separately, on every node (`Node.LenOk`), because 8.1.3, 9.1 and 10.1 apply to every
encoding alike.

8.1.1.4: constraints and extension markers do not affect these encodings. Extension additions are
encoded as if they were in the root.
-/

namespace Asn1.X690

open Asn1.X680

/-! ## Encodings (8.1.1) -/

/-- X.690 8.1.1: an encoding. A primitive one carries its contents octets; a constructed one, the
encodings its contents octets are made of. The length form is the sender's choice, checked by
`Node.LenOk`. -/
inductive Node where
  | prim (tag : Tag) (len : LenForm) (contents : Octets)
  | cons (tag : Tag) (len : LenForm) (children : List Node)
  deriving Repr

instance : Inhabited Node := ⟨.prim ⟨.universal, 0⟩ .short []⟩

def Node.tag : Node → Tag
  | .prim tg _ _ | .cons tg _ _ => tg

def Node.isConstructed : Node → Bool
  | .prim .. => false
  | .cons .. => true

def Node.len : Node → LenForm
  | .prim _ f _ | .cons _ f _ => f

mutual
  /-- X.690 8.1.1.1, 8.1.2–8.1.5: the octets of an encoding. -/
  def Node.octets : Node → Octets
    | .prim tg f cs => identOctets tg false ++ lengthOctets f cs.length ++ cs
    | .cons tg f ch =>
      let cs := Node.octetsList ch
      identOctets tg true ++ lengthOctets f cs.length ++ cs ++ (if f = .indefinite then eoc else [])

  /-- The contents octets of a constructed encoding: its encodings, in order. -/
  def Node.octetsList : List Node → Octets
    | [] => []
    | nd :: rest => nd.octets ++ Node.octetsList rest
end

/-- The number of contents octets. -/
def Node.contentsLength : Node → Nat
  | .prim _ _ cs => cs.length
  | .cons _ _ ch => (Node.octetsList ch).length

mutual
  /-- X.690 8.1.3.2, 9.1, 10.1: every encoding in `nd` (itself and those it contains) uses a length
  form the profile allows for it (`LenForm.Allowed`). -/
  def Node.LenOk (p : Profile) : Node → Prop
    | .prim _ f cs => f.Allowed p false cs.length
    | .cons _ f ch => f.Allowed p true (Node.octetsList ch).length ∧ Node.LenOkList p ch

  def Node.LenOkList (p : Profile) : List Node → Prop
    | [] => True
    | nd :: rest => nd.LenOk p ∧ Node.LenOkList p rest
end

/-- X.690 8.14.4: the encoding with implicit tagging: the base encoding's form (a), length and
contents octets (b), with the new tag. -/
def Node.retag (tg : Tag) : Node → Node
  | .prim _ f cs => .prim tg f cs
  | .cons _ f ch => .cons tg f ch

/-- A universal tag. -/
def univ (k : Nat) : Tag := ⟨.universal, k⟩

/-- A primitive encoding with tag `tg` whose contents octets satisfy `P`. -/
def Prim (tg : Tag) (P : Octets → Prop) (nd : Node) : Prop := ∃ f cs, nd = .prim tg f cs ∧ P cs

/-! ## Strings: primitive or segmented (8.6, 8.7, 8.23.3, 9.2, 10.2) -/

/-- X.690 9.2: the CER fragments of a constructed string encoding: primitive, each with 1000
contents octets except the last, which has 1 to 1000. -/
def CerFragments (ch : List Node) : Prop :=
  (∀ nd ∈ ch, nd.isConstructed = false) ∧
  (∀ (i : Nat) nd, ch[i]? = some nd → i + 1 < ch.length → nd.contentsLength = 1000) ∧
  (∃ nd, ch.getLast? = some nd ∧ 1 ≤ nd.contentsLength ∧ nd.contentsLength ≤ 1000)

/-- X.690 8.7: an encoding with tag `tg` of the octet string `os`.
- 8.7.1, 8.7.2: primitive, the octets as the contents;
- 8.7.3: constructed, the contents being encodings of consecutive segments of the octets, each an
  octet string encoded the same way, with the universal tag of OCTET STRING (8.7.3.2 NOTE 2), and
  any segment possibly empty (8.7.3.1 NOTE).
- 9.2 (CER): primitive up to 1000 octets, otherwise constructed from `CerFragments`;
- 10.2 (DER): primitive.

8.23.3 encodes a restricted character string as `[UNIVERSAL x] IMPLICIT OCTET STRING`, so it uses
this too, with `tg` its universal tag. -/
def octetsEnc (p : Profile) : Nat → Tag → Octets → Node → Prop
  | 0, _, _, _ => False
  | n + 1, tg, os, nd =>
    (∃ f, nd = .prim tg f os ∧ (p = .cer → os.length ≤ 1000)) ∨
    (∃ f ch, ∃ segs : List Octets, nd = .cons tg f ch ∧ p ≠ .der ∧ os = segs.flatten ∧
      List.Forall₂ (fun s c => octetsEnc p n (univ 4) s c) segs ch ∧
      (p = .cer → 1000 < os.length ∧ CerFragments ch))

/-- X.690 8.6: an encoding with tag `tg` of the bits `bs`.
- 8.6.1, 8.6.2: primitive (`BitsPrim`);
- 8.6.3, 8.6.4: constructed from segments, each a whole number of octets of bits except possibly the
  last, each encoded the same way with the universal tag of BIT STRING (8.6.4.1 NOTE 2);
- 9.2, 10.2 as for octet strings. A bit string's contents octets include the initial octet, so a
  CER fragment of 1000 contents octets holds 7992 bits.

OPEN (ledger X690-10): 8.6.4 says "with the possible exception of the last" segment is a multiple
of eight bits; a segment encoded constructed is again segmented, so its own last segment may be
short only if it is the last segment of the whole value. We require exactly that: every segment
but the last of the whole value is a whole number of octets. -/
def bitsEnc (p : Profile) : Nat → Bool → Tag → Bits → Node → Prop
  | 0, _, _, _, _ => False
  | n + 1, isLast, tg, bs, nd =>
    (∃ f cs, nd = .prim tg f cs ∧ BitsPrim p bs cs ∧ (isLast = false → bs.length % 8 = 0) ∧
      (p = .cer → cs.length ≤ 1000)) ∨
    (∃ f ch, ∃ segs : List Bits, nd = .cons tg f ch ∧ p ≠ .der ∧ bs = segs.flatten ∧
      List.Forall₂ (fun (si : Bits × Nat) c =>
        bitsEnc p n (isLast && si.2 + 1 == segs.length) (univ 3) si.1 c) segs.zipIdx ch ∧
      (p = .cer → 1000 < (bs.length + 7) / 8 + 1 ∧ CerFragments ch))

/-! ## SEQUENCE, SET and CHOICE components -/

/-- X.680 25.10 a), 31.2.7 c): the replacement "TaggedType" automatic tagging gives a component or
alternative of type `t` (read in `sc`): context-specific `k`, implicit unless `t` is an untagged
CHOICE, open type or dummy reference. The environment is that of the module the SEQUENCE, SET or
CHOICE is written in, which has AUTOMATIC TAGS, so a component brought in by COMPONENTS OF from a
module with another default is tagged the same way (25.10 NOTE 3). -/
def autoTagged (E : Env) (n : Nat) (sc : Scope) (k : Nat) (t : Ty) : Ty :=
  .tagged ⟨.context, k⟩ (if untaggedChoiceOrOpen E n sc t then .explicit else .implicit) t

/-- The components of a SEQUENCE or SET in textual order, each with its scope and the type that is
encoded: under automatic tagging (X.680 25.3) the type with its replacement tag (`entryTags`). -/
def compTys (E : Env) (n : Nat) (sc : Scope) (r : List Comp) (e : Option (List ExtAdd))
    (r2 : List Comp) : List (Entry × Ty) :=
  (entryTags E n sc r e r2).map fun (en, ts) =>
    if autoSeq sc.mod.header.tagDefault r e r2 then
      match ts with
      | some [tg] => (en, autoTagged E n en.scope tg.num en.ty)
      | _ => (en, en.ty)
    else (en, en.ty)

/-- The alternatives of a CHOICE, with the type that is encoded (X.680 29.2, 29.5). -/
def altTys (E : Env) (n : Nat) (sc : Scope) (r : List Alt) (e : Option (List AltAdd)) :
    List (Alt × Ty) :=
  (altTags E n sc r e).map fun (a, ts) =>
    if autoChoice sc.mod.header.tagDefault r e then
      match ts with
      | some [tg] => (a, autoTagged E n sc tg.num a.ty)
      | _ => (a, a.ty)
    else (a, a.ty)

/-- X.680 25.12: `x` is the default value of component `en`. -/
def IsDefault (E : Env) (n : Nat) (en : Entry) (x : Val) : Prop :=
  match en.presence with
  | .default_ d => ∃ d', evalVal E n en.scope d d' ∧ eqv E n en.scope en.ty x d'
  | _ => False

/-- X.690 8.9.2, 8.9.3, 8.11.2, 8.11.3, 11.5: what is encoded for component `en` of the value with
components `cs`: `some x` for an encoding of `x`, `none` for none.
- A component the value has is encoded, except that one equal to its default value may be left
  out (8.9.3), and under CER and DER is left out (11.5).
- A DEFAULT component the value omits has its default value (X.680 25.12): BER may encode that
  value (8.9.3); CER and DER do not (11.5).
- An OPTIONAL component the value omits is not encoded. -/
def CompChoice (E : Env) (p : Profile) (n : Nat) (en : Entry) (cs : List (String × Val)) :
    Option Val → Prop
  | some x =>
    match cs.lookup en.name with
    | some y => x = y ∧ (p.restricted = true → ¬ IsDefault E n en x)
    | none => p.restricted = false ∧ IsDefault E n en x
  | none =>
    match cs.lookup en.name with
    | some y => IsDefault E n en y
    | none => True

/-- X.690 8.9, 8.11: the encodings of the components, in the order of the type, each with its
component, given `enc`, the encoding of a value of a component's type. -/
def CompEncs (E : Env) (p : Profile) (n : Nat) (comps : List (Entry × Ty)) (cs : List (String × Val))
    (enc : Scope → Ty → Val → Node → Prop) (out : List ((Entry × Ty) × Node)) : Prop :=
  -- every component of the value is one of the type's (X.680 25.11, 27.3)
  (∀ q ∈ cs, q.1 ∈ comps.map (·.1.name)) ∧
  ∃ sel : List (Option Val), List.Forall₂ (fun c o => CompChoice E p n c.1 cs o) comps sel ∧
    List.Forall₂ (fun (q : (Entry × Ty) × Val) (r : (Entry × Ty) × Node) =>
        r.1 = q.1 ∧ enc q.1.1.scope q.1.2 q.2 r.2)
      ((comps.zip sel).filterMap fun (c, o) => o.map (c, ·)) out

/-- X.690 11.6: the order of SET OF encodings: compared as octet strings, the shorter padded with
zero octets at its end. -/
def octLe : Octets → Octets → Prop
  | [], _ => True
  | a :: as, [] => a = 0 ∧ octLe as []
  | a :: as, b :: bs => a < b ∨ (a = b ∧ octLe as bs)

/-- X.690 9.3: the tag a SET component is ordered by under CER: its tag, or, for an untagged
CHOICE, the smallest tag of the choice and of the untagged choices nested in it (which `tagsOf`
collects, X.680 29.8).

OPEN (ledger X690-11): 9.3 does not say where an untagged open type goes, whose tag is
indeterminate (X.681 14.2 NOTE 2; `tagsOf` gives `none`). We order it by the tag of its encoding,
as 10.3 does for DER. -/
def cerKey (E : Env) (n : Nat) (sc : Scope) (t : Ty) : Option Tag :=
  (tagsOf E n sc t).bind fun ts => ts.foldl (fun acc tg => match acc with
    | some a => if Tag.lt tg a then some tg else some a
    | none => some tg) none

/-! ## EXTERNAL (8.18) -/

/-- X.690 8.18.1: EXTERNAL is encoded as this type, in an environment of EXPLICIT TAGS, under
`[UNIVERSAL 8] IMPLICIT`. Its `encoding` component is built separately (`ExternalEncoding`),
since the type of `single-ASN1-type` is the open type ABSTRACT-SYNTAX.&Type. -/
def externalModule : Module := { name := "", header := ⟨.explicit, false⟩ }

/-- X.690 8.18.4, Table 2: the `direct-reference` and `indirect-reference` for an "identification"
alternative (the others "CANNOT OCCUR": X.680 37.5 excludes them). -/
def externalRefs : Val → Option (Option (List Nat) × Option Int)
  | .choice "syntax" (.oid o) => some (some o, none)
  | .choice "presentation-context-id" (.int i) => some (none, some i)
  | .choice "context-negotiation" (.seq cs) =>
    match cs.lookup "presentation-context-id", cs.lookup "transfer-syntax" with
    | some (.int i), some (.oid o) => some (some o, some i)
    | _, _ => none
  | _ => none

/-- X.690 8.18.5–8.18.11: the `encoding` CHOICE for data value octets `dv`, as the sender chooses:
- `single-ASN1-type` `[0]` (explicit) around the data value encoded as the single ASN.1 type it is a
  value of (8.18.6, 8.18.9);
- `octet-aligned` `[1] IMPLICIT OCTET STRING` (8.18.7, 8.18.10);
- `arbitrary` `[2] IMPLICIT BIT STRING` (8.18.7, 8.18.11).

OPEN (ledger X690-8): the abstract value (X.680 37.5) keeps the data value only as octets, the
encoding under the identified transfer syntax. `single-ASN1-type` is possible when those octets are
themselves one encoding under this profile (8.18.6: "a single ASN.1 data type", "encoding rules …
specified in this Recommendation"); the encoding is then those octets. -/
def ExternalEncoding (p : Profile) (n : Nat) (dv : Octets) (nd : Node) : Prop :=
  (∃ f inner, nd = .cons ⟨.context, 0⟩ f [inner] ∧ inner.octets = dv ∧ inner.LenOk p) ∨
  (∃ base, octetsEnc p n (univ 4) dv base ∧ nd = base.retag ⟨.context, 1⟩) ∨
  (∃ base, bitsEnc p n true (univ 3) (bitsOf dv) base ∧ nd = base.retag ⟨.context, 2⟩)

/-! ## The encoding relation -/

/-- X.690 8.26: the time type a built-in time type is. -/
def timeKind? : Ty → Option TimeKind
  | .time => some .time
  | .date => some .date
  | .timeOfDay => some .timeOfDay
  | .dateTime => some .dateTime
  | .duration => some .duration
  | _ => none

/-- `ber E p n sc t v nd`: `nd` is an encoding under profile `p` of the value `v` of type `t`,
written in scope `sc`. -/
def ber (E : Env) (p : Profile) : Nat → Scope → Ty → Val → Node → Prop
  | 0, _, _, _, _ => False
  -- 8.2, 11.1
  | _ + 1, _, .boolean, .bool b, nd => Prim (univ 1) (BoolContents p b) nd
  -- 8.3
  | _ + 1, _, .integer _, .int i, nd => Prim (univ 2) (IntContents i) nd
  -- 8.4: the integer associated with the identifier (X.680 20.3–20.6)
  | _ + 1, _, .enumerated r e, .enum id, nd =>
    ∃ k, (enumNumbers r e).lookup id = some k ∧ Prim (univ 10) (IntContents k) nd
  -- 8.5, 11.3
  | _ + 1, _, .real, .real r, nd => Prim (univ 9) (RealContents p r) nd
  -- 8.6, 11.2. 8.6.2.4: where X.680 22.7 applies (named bits), trailing 0 bits may be added or
  -- removed; 11.2.2: under CER and DER all are removed.
  | n + 1, _, .bitString named, .bits bs, nd =>
    ∃ bs', (if named = [] then bs' = bs
            else if p.restricted then bs' = stripTrailingZeros bs
            else stripTrailingZeros bs' = stripTrailingZeros bs) ∧
      bitsEnc p n true (univ 3) bs' nd
  -- 8.7
  | n + 1, _, .octetString, .octets os, nd => octetsEnc p n (univ 4) os nd
  -- 8.8
  | _ + 1, _, .null, .null, nd => Prim (univ 5) (· = []) nd
  -- 8.9: constructed, the components in the order of the type
  | n + 1, sc, .sequence r e r2, .seq cs, nd =>
    ∃ f, ∃ out : List ((Entry × Ty) × Node), nd = .cons (univ 16) f (out.map (·.2)) ∧
      CompEncs E p n (compTys E n sc r e r2) cs (ber E p n) out
  -- 8.10
  | n + 1, sc, .sequenceOf el, .seqOf vs, nd =>
    ∃ f ch, nd = .cons (univ 16) f ch ∧ List.Forall₂ (fun x c => ber E p n sc el x c) vs ch
  -- 8.11: constructed, the components in an order the sender chooses (8.11.2); 9.3 (CER) by the
  -- tags of the components' types, an untagged CHOICE by its smallest tag; 10.3 (DER) by the tags
  -- of the encodings (X.680 8.6)
  | n + 1, sc, .set r e r2, .seq cs, nd =>
    ∃ f, ∃ out out' : List ((Entry × Ty) × Node), nd = .cons (univ 17) f (out.map (·.2)) ∧
      CompEncs E p n (compTys E n sc r e r2) cs (ber E p n) out' ∧ out.Perm out' ∧
      (p = .der → out.Pairwise fun a b => Tag.lt a.2.tag b.2.tag = true) ∧
      (p = .cer → out.Pairwise fun a b =>
        Tag.lt ((cerKey E n a.1.1.scope a.1.2).getD a.2.tag)
          ((cerKey E n b.1.1.scope b.1.2).getD b.2.tag) = true)
  -- 8.12: constructed, the elements' encodings in any order (8.12.3); 11.6 (CER, DER) ascending
  | n + 1, sc, .setOf el, .setOf vs, nd =>
    ∃ f ch ch', nd = .cons (univ 17) f ch ∧ List.Forall₂ (fun x c => ber E p n sc el x c) vs ch' ∧
      ch.Perm ch' ∧ (p.restricted = true → ch.Pairwise fun a b => octLe a.octets b.octets)
  -- 8.13: the encoding of the chosen alternative's value
  | n + 1, sc, .choice r e, .choice a x, nd =>
    ∃ alt ∈ altTys E n sc r e, alt.1.name = a ∧ ber E p n sc alt.2 x nd
  -- X.691 10.6.2 and X.680 30: a selection type is the selected alternative's type
  | n + 1, sc, .selection nm t, v, nd =>
    match builtin E n sc t with
    | some (sc', .choice root ext) => match findAlt (choiceAlts root ext) nm with
      | some alt => ber E p n sc' alt.ty v nd
      | none => False
    | _ => False
  -- 8.19, 8.20
  | _ + 1, _, .objectIdentifier, .oid arcs, nd => Prim (univ 6) (· = oidContents arcs) nd
  | _ + 1, _, .relativeOid, .oid arcs, nd => Prim (univ 13) (· = relOidContents arcs) nd
  -- 8.21, 8.22
  | _ + 1, _, .oidIri, .iri ls, nd => Prim (univ 35) (· = iriContents ls) nd
  | _ + 1, _, .relativeOidIri, .iri ls, nd => Prim (univ 36) (· = relIriContents ls) nd
  -- 8.17.1: the encoding of the associated type of X.680 36.5, with EMBEDDED PDV's own tag.
  -- OPEN (ledger X690-12): 8.17.1 says "the BER encoding of the type as defined in 36.5", a
  -- SEQUENCE; the tag of EMBEDDED PDV is UNIVERSAL 11 (X.680 8.4, Table 1), which we keep.
  | n + 1, _, .embeddedPdv, v, nd =>
    ber E p n (.ofModule assocModule) (.tagged (univ 11) .implicit embeddedPdvAssoc) v nd
  -- 8.24.1: likewise with X.680 44.5
  | n + 1, _, .characterString, v, nd =>
    ber E p n (.ofModule assocModule) (.tagged (univ 29) .implicit characterStringAssoc) v nd
  -- 8.18
  | n + 1, _, .external, .seq cs, nd =>
    ∃ f id dvd dv refs, cs.lookup "identification" = some id ∧ cs.lookup "data-value" = some (.octets dv) ∧
      cs.lookup "data-value-descriptor" = dvd ∧ externalRefs id = some refs ∧
      ∃ dr ir dd enc, nd = .cons (univ 8) f (dr ++ ir ++ dd ++ [enc]) ∧
        -- 8.18.4: direct-reference and indirect-reference as Table 2 says
        (match refs.1 with
         | some o => ∃ x, dr = [x] ∧ Prim (univ 6) (· = oidContents o) x
         | none => dr = []) ∧
        (match refs.2 with
         | some i => ∃ x, ir = [x] ∧ Prim (univ 2) (IntContents i) x
         | none => ir = []) ∧
        -- 8.18.3: data-value-descriptor exactly when the abstract value has one
        (match dvd with
         | some d => ∃ x, dd = [x] ∧ ber E p n (.ofModule externalModule) .objectDescriptor d x
         | none => dd = []) ∧
        ExternalEncoding p n dv enc
  -- 8.23
  | n + 1, _, .restricted k, v, nd =>
    ∃ os, StringOctets p k v os ∧ ∃ tg, (Ty.restricted k).universalTag? = some tg ∧
      octetsEnc p n (univ tg) os nd
  -- 8.25: GeneralizedTime is [UNIVERSAL 24] IMPLICIT VisibleString (X.680 46.3), with 11.7
  | n + 1, _, .generalizedTime, .chars cs, nd =>
    (p.restricted = true → GenTimeCanon (cs.map Char.ofNat)) ∧
    ∃ os, StringOctets p .visible (.chars cs) os ∧ octetsEnc p n (univ 24) os nd
  -- 8.25: UTCTime is [UNIVERSAL 23] IMPLICIT VisibleString (X.680 47.3), with 11.8
  | n + 1, _, .utcTime, .chars cs, nd =>
    (p.restricted = true → UtcTimeCanon (cs.map Char.ofNat)) ∧
    ∃ os, StringOctets p .visible (.chars cs) os ∧ octetsEnc p n (univ 23) os nd
  -- 8.25: ObjectDescriptor is [UNIVERSAL 7] IMPLICIT GraphicString (X.680 48.3)
  | n + 1, _, .objectDescriptor, v, nd =>
    ∃ os, StringOctets p .graphic v os ∧ octetsEnc p n (univ 7) os nd
  -- X.680 13.19, 14.1, 14.6; X.683 9
  | n + 1, sc, .ref name, v, nd => match resolveTy E n sc none name [] with
    | some (sc', t) => ber E p n sc' t v nd
    | none => False
  | n + 1, sc, .extRef mn name, v, nd => match resolveTy E n sc (some mn) name [] with
    | some (sc', t) => ber E p n sc' t v nd
    | none => False
  | n + 1, sc, .paramRef mn name args, v, nd => match resolveTy E n sc mn name args with
    | some (sc', t) => ber E p n sc' t v nd
    | none => False
  -- 8.14.3: explicit tagging: constructed, the contents the complete base encoding;
  -- 8.14.4: implicit tagging: the base encoding with the tag replaced
  | n + 1, sc, .tagged tg kind t, v, nd =>
    ∃ base, ber E p n sc t v base ∧
      if isExplicit E n sc kind t then ∃ f, nd = .cons tg f [base] else nd = base.retag tg
  -- 8.1.1.4: constraints do not affect the encoding
  | n + 1, sc, .constrained t _, v, nd => ber E p n sc t v nd
  -- 8.15: the encoding of the value as a value of the type it is of
  | n + 1, _, .openType, .open_ t w, nd => ∃ sc', ber E p n sc' t w nd
  -- X.681 14.2–14.5: a fixed-type field is its type; a type field is an open type
  | n + 1, sc, .classField cls path, v, nd =>
    match (classFields E n sc cls).bind (fun cf => fieldAt E n cf path) with
    | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => ber E p n sc' t v nd
    | some (_, .typeField _ _) | some (_, .varValue _ _ _) | some (_, .varValueSet _ _ _) =>
      ber E p n sc .openType v nd
    | _ => False
  -- X.681 15: a column of a table, a fixed-type field's type or an open type
  | n + 1, sc, .fromObjects src path, v, nd => match objSetClass E n sc src with
    | some (csc, cls) => match (classFields E n csc cls).bind (fun cf => fieldAt E n cf path) with
      | some (sc', .fixedValue _ t _ _) | some (sc', .fixedValueSet _ t _) => ber E p n sc' t v nd
      | some (_, _) => ber E p n sc .openType v nd
      | none => False
    | none => False
  -- 8.16: [UNIVERSAL 8] IMPLICIT SEQUENCE { type-id …, value [0] EXPLICIT … } (X.681 C.7)
  | n + 1, sc, .instanceOf cls, v, nd =>
    ber E p n sc (.tagged (univ 8) .implicit (instanceOfTy cls)) v nd
  -- 8.26, 11.9
  | _ + 1, _, t, .time tv, nd => match timeKind? t, t.universalTag? with
    | some k, some tg => Prim (univ tg) (TimeContents p k tv) nd
    | _, _ => False
  | _ + 1, _, _, _, _ => False

/-! ## The encoding rules -/

/-- X.690 8.1, 9, 10: `bs` is an encoding of `v` (of type `t`, in scope `sc`) for every large enough
fuel: an encoding whose every length form the profile allows, laid out as octets. -/
def BerEncodes (E : Env) (p : Profile) (sc : Scope) (t : Ty) (v : Val) (os : Octets) : Prop :=
  Eventually fun n => ∃ nd, ber E p n sc t v nd ∧ nd.LenOk p ∧ os = nd.octets

/-- X.690 12.2–12.4: the object identifiers of BER, CER and DER, which ENCODED BY can name. -/
def Profile.oid : Profile → List Nat
  | .ber => [2, 1, 1]
  | .cer => [2, 1, 2, 0]
  | .der => [2, 1, 2, 1]

/-- X.682 11.4, 11.6 under X.690: the values of `OCTET STRING (CONTAINING T)` are the encodings of
`T`'s values under the rules applied to the octet string, or those ENCODED BY names; for a BIT
STRING, their bits.

OPEN (ledger X690-9): ENCODED BY an object identifier that is not BER's, CER's or DER's names rules
this specification does not have; its values are then any octet or bit string. -/
def hook (p : Profile) (E : Env) : ContentsHook := fun sc t enc tvals x =>
  let rules : Option Profile := match enc with
    | none => some p
    | some (.oid o) => [Profile.ber, .cer, .der].find? (·.oid = o)
    | some _ => none
  match rules, t with
  | some q, some t => ∃ y os, tvals y ∧ BerEncodes E q sc t y os ∧ (x = .octets os ∨ x = .bits (bitsOf os))
  | some _, none => ∃ os, x = .octets os ∨ x = .bits (bitsOf os)
  | none, _ => (∃ os, x = .octets os) ∨ (∃ bs, x = .bits bs)

/-- BER (`.ber`), CER (`.cer`) and DER (`.der`) as encoding rules: the encodings of the values of a
type written in module `m`. -/
def rule (p : Profile) : EncodingRule where
  hook := hook p
  Encodes E m t v bs :=
    Has E (hook p E) m t v ∧ ∃ os, BerEncodes E p (.ofModule m) t v os ∧ bs = bitsOf os

end Asn1.X690
