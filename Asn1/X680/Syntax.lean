import Mathlib.Data.Rat.Defs
import Asn1.X680.Pattern
import Asn1.X680.Time
import Asn1.X680.Lexical
import Asn1.X680.Rule

/-!
# ASN.1 types and abstract values (X.680)

`Ty` is the type notation (X.680 17) after parsing: what a type assignment's right-hand side says,
with references still references, including references to information objects (X.681) and
parameterized assignments (X.683). `Val` is an abstract value. It is not value notation: two notations for one value
(`{ a 1 }` and `{ a 1, b 0 }` when `b` is `DEFAULT 0`, or `1E1` and `10` for REAL) give one `Val`.

The value set of a type, `Has` (in `Semantics.lean`), connects the two.
-/

namespace Asn1.X680

/-- X.680 8.1: the four tag classes, in the canonical order of 8.6. -/
inductive TagClass where
  | universal | application | context | private_
  deriving DecidableEq, Repr, Ord

/-- X.680 8: a tag is a class and a number. -/
structure Tag where
  cls : TagClass
  num : Nat
  deriving DecidableEq, Repr

/-- X.680 31.2: how a "TaggedType" was written. `default_` takes the module's "TagDefault" (31.2.7). -/
inductive TagKind where
  | explicit | implicit | default_
  deriving DecidableEq, Repr

/-- X.680 13.1 "TagDefault": EXPLICIT when nothing is written (13.2). -/
inductive TagDefault where
  | explicit | implicit | automatic
  deriving DecidableEq, Repr

/-- X.680 21.3: the base of a numeric REAL value. Values with base 2 and with base 10 are distinct
abstract values, even when they are equal as numbers. -/
inductive RealBase where
  | two | ten
  deriving DecidableEq, Repr

/-- X.680 21.3: the abstract values of REAL. A numeric value is the number `M × B^E`, kept as a
rational, so that every `M × B^E` with the same numerical value is the same abstract value
(`RealVal.Wf` says which rationals are reachable). -/
inductive RealVal where
  | plusInfinity | minusInfinity | notANumber
  | plusZero | minusZero
  | num (base : RealBase) (q : ℚ)
  deriving DecidableEq, Repr

/-- The abstract value `M × B^E`, `M ≠ 0` (X.680 21.3). -/
def RealVal.Wf : RealVal → Prop
  | .num .two q => q ≠ 0 ∧ ∃ m e : Int, q = m * (2 : ℚ) ^ e
  | .num .ten q => q ≠ 0 ∧ ∃ m e : Int, q = m * (10 : ℚ) ^ e
  | _ => True

/-- X.682 10.7 "AtNotation": `@a.b` (`level = none`), or `@.a.b` with `level = some k` for `k`
additional dots after "@.". -/
structure AtRef where
  level : Option Nat
  path : List String
  deriving DecidableEq, Repr

/-- X.680 17.7 "Value" as written, before it is read against its governing type (X.680 14.8, Annex
C.6): what `{ a, b }` or `"…"` is depends on the type. The front end reads it into a `Val`. -/
inductive RawVal where
  /-- 12.8, 19.9 "SignedNumber" -/
  | num (i : Int)
  /-- 12.9 "realnumber", with a sign -/
  | real (neg : Bool) (int : Nat) (frac : String) (exp : Int)
  /-- 12.10 -/
  | bstring (bs : List Bool)
  /-- 12.12 -/
  | hstring (hs : List Nat)
  /-- 12.14, 12.17: the characters -/
  | cstring (cs : List Nat)
  /-- TRUE, FALSE, NULL, PLUS-INFINITY, MINUS-INFINITY, NOT-A-NUMBER -/
  | kw (s : String)
  /-- an identifier, or a valuereference (12.4: told apart by context) -/
  | ident (s : String)
  /-- 14.6 "ExternalValueReference" -/
  | ext (moduleName name : String)
  /-- 29.11 "ChoiceValue" -/
  | choice (alt : String) (v : RawVal)
  /-- `{ … }`: its comma-separated items, each the run of values written in it -/
  | braces (items : List (List RawVal))
  /-- 32.3 "NameAndNumberForm", 19.6 "NamedNumber": `id(n)` -/
  | nameNum (id : String) (n : RawVal)
  /-- 22.9, 23.3: CONTAINING Value -/
  | containing (v : RawVal)
  /-- X.681 15 "ValueFromObject" with an object reference: `obj.&f…` -/
  | fromObject (obj : String) (field : List String)
  /-- X.681 14.6: an open type's value, `Type : Value`, the type as lexical items -/
  | typed (ty : List Tok) (v : RawVal)
  deriving Repr, Inhabited

/-- X.681 10.5 "TokenOrGroupSpec": an item of a class's WITH SYNTAX. -/
inductive SynItem where
  /-- 10.6 "Literal": a word or a comma -/
  | literal (w : String)
  /-- 10.7 "PrimitiveFieldName" -/
  | field (name : String)
  /-- 10.8 "OptionalGroup" -/
  | optional (items : List SynItem)
  deriving Repr, Inhabited

mutual
  /-- X.680 17.1 "Type". -/
  inductive Ty where
    /-- X.680 18 -/
    | boolean
    /-- X.680 19: with its "NamedNumberList". Named numbers do not change the value set (19.3). -/
    | integer (named : List (String × Int))
    /-- X.680 20: the "RootEnumeration", then, if there is an ellipsis, the "AdditionalEnumeration".
    Numbers are as written; `Ty.enumNumbers` assigns the rest (20.3). -/
    | enumerated (root : List (String × Option Int)) (ext : Option (List (String × Option Int)))
    /-- X.680 21 -/
    | real
    /-- X.680 22: with its "NamedBitList" -/
    | bitString (named : List (String × Nat))
    /-- X.680 23 -/
    | octetString
    /-- X.680 24 -/
    | null
    /-- X.680 25.1 "ComponentTypeLists": the root components, then, if there is an ellipsis, the
    extension additions, and the root components after a second ellipsis (the third and fourth
    alternatives). Those trailing root components are root components (X.691 19.9 NOTE 2), but they
    stay apart here because automatic tagging (25.10) and the distinct-tag rule of 25.7 depend on
    where they were written. -/
    | sequence (root : List Comp) (ext : Option (List ExtAdd)) (root2 : List Comp)
    /-- X.680 26. `SEQUENCE OF NamedType` names the component, which changes nothing here. -/
    | sequenceOf (elem : Ty)
    /-- X.680 27, as `sequence` -/
    | set (root : List Comp) (ext : Option (List ExtAdd)) (root2 : List Comp)
    /-- X.680 28 -/
    | setOf (elem : Ty)
    /-- X.680 29: the root alternatives, then the extension additions. -/
    | choice (root : List Alt) (ext : Option (List AltAdd))
    /-- X.680 30: `name < T`, the type of alternative `name` of the CHOICE type `T`. -/
    | selection (name : String) (t : Ty)
    /-- X.680 32 -/
    | objectIdentifier
    /-- X.680 33 -/
    | relativeOid
    /-- X.680 34 -/
    | oidIri
    /-- X.680 35 -/
    | relativeOidIri
    /-- X.680 36, defined by its associated type (36.5) -/
    | embeddedPdv
    /-- X.680 37, defined by its associated type (37.5) -/
    | external
    /-- X.680 40.1, 41 -/
    | restricted (k : StrType)
    /-- X.680 44: CHARACTER STRING, defined by its associated type (44.5) -/
    | characterString
    /-- X.680 38: TIME -/
    | time
    /-- X.680 38.4.1–38.4.4: DATE, TIME-OF-DAY, DATE-TIME and DURATION, each a TIME with property
    settings and a tag of its own (Table 1) -/
    | date | timeOfDay | dateTime | duration
    /-- X.680 46: GeneralizedTime, a VisibleString in a stated format -/
    | generalizedTime
    /-- X.680 47: UTCTime, likewise -/
    | utcTime
    /-- X.680 48: ObjectDescriptor, a GraphicString -/
    | objectDescriptor
    /-- X.680 14.1: a "typereference", resolved in the module it is written in (13.16, 13.19) -/
    | ref (name : String)
    /-- X.680 14.6: an "ExternalTypeReference", `modulereference.typereference` -/
    | extRef (moduleName name : String)
    /-- X.680 31.2: a "TaggedType" -/
    | tagged (tag : Tag) (kind : TagKind) (t : Ty)
    /-- X.680 49.1: a "ConstrainedType", with its constraint -/
    | constrained (t : Ty) (c : Constraint)
    /-- X.681 14.2: an open type, any type, carried with its value: what a type field of a class
    denotes before a table constraint restricts it -/
    | openType
    /-- X.681 14.1 "ObjectClassFieldType": `C.&f1.&f2…`, a field of a class, reached through object
    fields (9.14) -/
    | classField (cls : ClassRef) (field : List String)
    /-- X.681 15 "TypeFromObject", and "ValueSetFromObjects" used as a type (X.680 16.8): a column
    of the associated table of an object or object set (an object is the set of just itself,
    13.3) -/
    | fromObjects (src : ObjSet) (field : List String)
    /-- X.683 9.2 "ParameterizedType" and "ParameterizedValueSetType", with the module name when it
    is an external reference -/
    | paramRef (moduleName : Option String) (name : String) (args : List Arg)
    /-- X.681 Annex C: INSTANCE OF -/
    | instanceOf (cls : ClassRef)

  /-- X.680 25.1 "ComponentType" -/
  inductive Comp where
    | mk (name : String) (t : Ty) (presence : Presence)
    /-- `COMPONENTS OF t`, which 25.5 and 27.2 replace by the root components of `t` -/
    | componentsOf (t : Ty)

  /-- X.680 25.1: how a component may be omitted -/
  inductive Presence where
    | mandatory
    | optional
    /-- 25.12: omitting it is "exactly equivalent" to inserting this value -/
    | default_ (v : Val)

  /-- X.680 25.1 "ExtensionAddition": one component, or a "[[ ... ]]" group with its version
  number, if written. -/
  inductive ExtAdd where
    | one (c : Comp)
    | group (version : Option Nat) (cs : List Comp)

  /-- X.680 29.1 "NamedType" as a choice alternative -/
  inductive Alt where
    | mk (name : String) (t : Ty)

  /-- X.680 29.1 "ExtensionAdditionAlternative" -/
  inductive AltAdd where
    | one (a : Alt)
    | group (version : Option Nat) (alts : List Alt)

  /-- X.680 49.6 "ElementSetSpecs", with 52's extensibility: the root, whether there is an
  ellipsis, and the additional elements. The exception specification (53) does not change the
  value set, so it is not kept. -/
  inductive Constraint where
    | mk (root : ElemSet) (extensible : Bool) (additions : Option ElemSet)
    /-- X.682 10.3 "TableConstraint": a simple table constraint (`refs = []`, 10.3) or a component
    relation constraint (10.7), `refs` its "AtNotation"s -/
    | table (os : ObjSet) (refs : List AtRef)
    /-- X.682 11.1 "ContentsConstraint": CONTAINING a type, ENCODED BY an object identifier, or
    both -/
    | contents (t : Option Ty) (encodedBy : Option Val)
    /-- X.682 9 "UserDefinedConstraint", CONSTRAINED BY {…} -/
    | userDefined

  /-- X.680 50.1 "ElementSetSpec" -/
  inductive ElemSet where
    | elem (e : Elem)
    | union (a b : ElemSet)
    | inter (a b : ElemSet)
    /-- `a EXCEPT b` -/
    | except (a b : ElemSet)
    /-- `ALL EXCEPT b` -/
    | allExcept (b : ElemSet)

  /-- X.680 51.1 "SubtypeElements" -/
  inductive Elem where
    /-- 51.2 -/
    | single (v : Val)
    /-- 51.3: the values of `t`; whether INCLUDES was written (51.3.1), which 51.6 needs on an open
    type -/
    | contained (t : Ty) (includes : Bool)
    /-- 51.4: each end, and whether it is open (`<`) -/
    | range (lo : Bound) (loOpen : Bool) (hi : Bound) (hiOpen : Bool)
    /-- 51.5 -/
    | size (c : Constraint)
    /-- 51.6: a type constraint, on an open type -/
    | typeC (t : Ty)
    /-- 51.7 -/
    | from_ (c : Constraint)
    /-- 51.8 WITH COMPONENT, on a SEQUENCE OF or SET OF -/
    | withComponent (c : Constraint)
    /-- 51.8 WITH COMPONENTS: whether it is partial, and for each named component its value
    constraint and presence constraint -/
    | withComponents (isPartial : Bool) (cs : List (String × Option Constraint × PresenceC))
    /-- 51.9 PATTERN, with its Annex A regular expression parsed -/
    | pattern (re : Regex)
    /-- 51.10 SETTINGS: the "PropertyAndSettingPair"s of the "simplestring", as written. The
    duration, time point and recurrence ranges of 51.11–51.13 are "ValueRange"s, so `range`. -/
    | settings (ps : List (String × String))

  /-- X.680 51.4 "LowerEndValue" and "UpperEndValue" -/
  inductive Bound where
    | min | max
    | val (v : Val)

  /-- X.680 51.8.5 "PresenceConstraint" -/
  inductive PresenceC where
    | present | absent | optional | unspecified

  /-- An abstract value. -/
  inductive Val where
    | bool (b : Bool)
    | int (i : Int)
    /-- X.680 20: the value is the identifier. Its number is a property of the type. -/
    | enum (id : String)
    | real (r : RealVal)
    | bits (bs : Bits)
    /-- X.680 23: a sequence of octets, each as 8 bits, leading bit first -/
    | octets (os : List (Fin 256))
    | null
    /-- X.680 25, 27: the components present, as (identifier, value), in the order of the type.
    A component with a DEFAULT is always present (25.12). A SET value is unordered, but its
    components have distinct identifiers, so the type's order identifies it. -/
    | seq (cs : List (String × Val))
    /-- X.680 26 -/
    | seqOf (vs : List Val)
    /-- X.680 28: a SET OF value is unordered. Two lists that are permutations of each other are
    the same abstract value: see `Val.Equiv`. -/
    | setOf (vs : List Val)
    /-- X.680 29: the alternative chosen, and its value -/
    | choice (alt : String) (v : Val)
    /-- X.680 32, 33: the arcs -/
    | oid (arcs : List Nat)
    /-- X.680 34, 35: the arcs, as their Unicode labels -/
    | iri (arcs : List String)
    /-- X.680 39–41: the characters, as ISO/IEC 10646 code points -/
    | chars (cs : List Nat)
    /-- X.680 41, Table 8: the characters of TeletexString, VideotexString, GraphicString and
    GeneralString, which are cells of sets in the ISO International Register (`RegChar`) -/
    | regChars (cs : List RegChar)
    /-- X.680 38: a time abstract value (`Time.lean`) -/
    | time (t : TimeV)
    /-- X.681 14.6: an open type's value is a value of some type: that type, and the value -/
    | open_ (t : Ty) (v : Val)
    /-- Value notation that names a value (X.680 14.1 "valuereference", 14.6, X.683 9.2
    "ParameterizedValue"). It is never part of an abstract value: `evalVal` replaces it. -/
    | ref (moduleName : Option String) (name : String) (args : List Arg)
    /-- X.681 15 "ValueFromObject": likewise notation only -/
    | fromObject (src : ObjSet) (field : List String)
    /-- Value notation the front end has not read yet; it is not a value of any type -/
    | raw (r : RawVal)

  /-- X.681 9.2 "ObjectClass" -/
  inductive ClassRef where
    /-- 9.2 a) "DefinedObjectClass", X.683 "ParameterizedObjectClass" -/
    | ref (moduleName : Option String) (name : String) (args : List Arg)
    /-- 9.3 "ObjectClassDefn", with its WITH SYNTAX spec (10), which says how objects of the class
    are written -/
    | defn (fields : List FieldSpec) (withSyntax : Option (List SynItem) := none)
    /-- X.681 Annex A, TYPE-IDENTIFIER, and Annex B, ABSTRACT-SYNTAX -/
    | typeIdentifier
    | abstractSyntax

  /-- X.681 9.4 "FieldSpec". An optionality is `none` when the field is required, `some none` for
  OPTIONAL, and `some (some d)` for DEFAULT `d`. -/
  inductive FieldSpec where
    /-- 9.5 -/
    | typeField (name : String) (opt : Option (Option Ty))
    /-- 9.6, with UNIQUE -/
    | fixedValue (name : String) (t : Ty) (unique : Bool) (opt : Option (Option Val))
    /-- 9.8: the type is that of the type field named by `typeField` -/
    | varValue (name : String) (typeField : List String) (opt : Option (Option Val))
    /-- 9.9 -/
    | fixedValueSet (name : String) (t : Ty) (opt : Option (Option Constraint))
    /-- 9.10 -/
    | varValueSet (name : String) (typeField : List String) (opt : Option (Option Constraint))
    /-- 9.11 -/
    | objectField (name : String) (cls : ClassRef) (opt : Option (Option Obj))
    /-- 9.12 -/
    | objectSetField (name : String) (cls : ClassRef) (opt : Option (Option ObjSet))

  /-- X.681 11.3 "Object" -/
  inductive Obj where
    /-- "DefinedObject", "ParameterizedObject" -/
    | ref (moduleName : Option String) (name : String) (args : List Arg)
    /-- 11.5 "DefaultSyntax": the settings by field name. "DefinedSyntax" (11.6) is another
    notation for the same settings. -/
    | defn (settings : List (String × Setting))
    /-- 15 "ObjectFromObject" -/
    | fromObject (src : Obj) (field : List String)
    /-- An object written in "DefinedSyntax" (11.6), as lexical items, before the front end reads
    it through its class's syntax; it is not an object -/
    | raw (toks : List Tok)

  /-- X.681 11.7 "Setting" -/
  inductive Setting where
    | type (t : Ty)
    | value (v : Val)
    /-- X.680 16.7 "ValueSet", an "ElementSetSpecs" -/
    | valueSet (c : Constraint)
    | object (o : Obj)
    | objectSet (s : ObjSet)

  /-- X.681 12.3 "ObjectSet" -/
  inductive ObjSet where
    /-- "DefinedObjectSet", "ParameterizedObjectSet" -/
    | ref (moduleName : Option String) (name : String) (args : List Arg)
    /-- 12.3 "ObjectSetSpec": an optional root (it may be just "..."), whether it is extensible,
    and the additional elements -/
    | spec (root : Option OElems) (extensible : Bool) (additions : Option OElems)

  /-- X.680 50 set arithmetic over objects (X.681 12.10 "ObjectSetElements"). ALL EXCEPT is not
  allowed over objects (X.680 50.3). -/
  inductive OElems where
    | obj (o : Obj)
    | set (s : ObjSet)
    /-- X.681 15 "ObjectSetFromObjects" -/
    | fromObjects (src : ObjSet) (field : List String)
    | union (a b : OElems)
    | inter (a b : OElems)
    | except (a b : OElems)

  /-- X.683 9.5 "ActualParameter" -/
  inductive Arg where
    | type (t : Ty)
    | value (v : Val)
    | valueSet (c : Constraint)
    | cls (c : ClassRef)
    | obj (o : Obj)
    | objSet (s : ObjSet)
    /-- An actual parameter as lexical items, before the front end knows what its dummy stands
    for (9.5) -/
    | raw (toks : List Tok)
end

/-- X.683 8.3 "ParamGovernor" -/
inductive ParamGov where
  | type (t : Ty)
  | cls (c : ClassRef)
  | dummy (name : String)

/-- X.683 8.3 "Parameter": a dummy reference, and its governor if it stands for a value, value set,
object or object set -/
structure Param where
  governor : Option ParamGov
  name : String

/-- X.683 8.1–8.2: the parameterized assignments -/
inductive ParamAssign where
  | type (name : String) (params : List Param) (body : Ty)
  | value (name : String) (params : List Param) (t : Ty) (v : Val)
  | valueSet (name : String) (params : List Param) (t : Ty) (c : Constraint)
  | cls (name : String) (params : List Param) (c : ClassRef)
  | obj (name : String) (params : List Param) (cls : ClassRef) (o : Obj)
  | objSet (name : String) (params : List Param) (cls : ClassRef) (s : ObjSet)

def ParamAssign.name : ParamAssign → String
  | .type n .. | .value n .. | .valueSet n .. | .cls n .. | .obj n .. | .objSet n .. => n

/-- X.680 13: what the module header says about the types defined in it. -/
structure ModuleHeader where
  tagDefault : TagDefault
  /-- 13.4 EXTENSIBILITY IMPLIED -/
  extImplied : Bool

/-- X.680 13.1: a module: its name (13.6), its header, the symbols it imports and the module each
comes from (13.16), and its assignments (13.21). A value set assignment (16.6) is a type
assignment (16.8). -/
structure Module where
  name : String
  header : ModuleHeader
  imports : List (String × String) := []
  /-- X.680 13.8 "DefinitiveIdentification": the module's object identifier, if it has one -/
  oid : Option (List Nat) := none
  /-- X.680 13.9–13.11: for each module this one imports from, the object identifier its
  "AssignedIdentifier" gives, which identifies that module definitively (13.11) -/
  importOids : List (String × List Nat) := []
  /-- X.680 13.13: the symbols EXPORTS lists; none for EXPORTS ALL or no EXPORTS (13.14) -/
  exports : Option (List String) := none
  /-- X.680 13.16 e): the module reference of each "SymbolsFromModule", in order -/
  importMods : List String := []
  /-- X.680 53.4: the defined values that exception specs name (an exception spec does not change
  the values, 53.3, so this is all that is kept of it) -/
  exceptionRefs : List (Option String × String) := []
  /-- X.683 8.6, a rule about the notation, found broken when the module was read: the assignment,
  and its dummy reference that is not used -/
  unusedDummies : List (String × String) := []
  /-- X.680 16.1 -/
  types : List (String × Ty) := []
  /-- X.680 16.2: the value's governing type, and the value -/
  values : List (String × Ty × Val) := []
  /-- X.681 9.1 -/
  classes : List (String × ClassRef) := []
  /-- X.681 11.1 -/
  objects : List (String × ClassRef × Obj) := []
  /-- X.681 12.1 -/
  objectSets : List (String × ClassRef × ObjSet) := []
  /-- X.683 8.1 -/
  params : List ParamAssign := []

def Module.lookup (m : Module) (n : String) : Option Ty := (m.types.find? (·.1 == n)).map (·.2)

/-- The modules of a specification: "the sphere of interest" of X.680 13.7. -/
abbrev Env := List Module

def Env.find (E : Env) (name : String) : Option Module := E.find? (·.name == name)

/-- X.680 13.10, 13.11: the module that module `m` means by `mn`: the one with the object identifier
`m`'s import gives for `mn`, if one has it (that identifier is definitive, and the name may then
differ), otherwise the one named `mn`. -/
def Env.findFrom (E : Env) (m : Module) (mn : String) : Option Module :=
  match (m.importOids.find? (·.1 == mn)).bind (fun (_, o) => E.find? (·.oid == some o)) with
  | some m' => some m'
  | none => E.find mn

/-- X.680 13.16, 13.19: a reference in module `m` means what is assigned to it in `m` (found by
`get`), or, if `m` imports it, what it means in the module it is imported from. An import can name
a symbol that module itself imports (13.16 a)), so this follows a chain, with fuel.

X.680 13.20: a symbol that is imported from more than one module, or both imported and assigned,
can only be used in an external reference, so a reference to it here resolves to nothing. A symbol
listed twice in one "SymbolsFromModule" is not in another (13.16 e) forbids naming a module twice),
so it is imported once. -/
def Env.resolveWith {α : Type} (E : Env) (get : Module → Option α) (name : String) :
    Nat → Module → Option (Module × α)
  | 0, _ => none
  | n + 1, m =>
    match get m, ((m.imports.filter (·.1 == name)).map (·.2)).eraseDups with
    | some a, [] => some (m, a)
    | none, [mn] => match E.findFrom m mn with
      | some m' => Env.resolveWith E get name n m'
      | none => none
    | _, _ => none

/-- A typereference (13.16, 13.19, 14.1). -/
def Env.resolve (E : Env) (n : Nat) (m : Module) (name : String) : Option (Module × Ty) :=
  E.resolveWith (·.lookup name) name n m

/-- X.680 14.5, 14.6: an external reference `mn.name`, written in module `m`, names what module `mn`
(as `m` means it, 13.10) assigns to `name` (14.5 a)), or, if `mn` imports `name` and only once,
what that import means (14.5 b)). -/
def Env.resolveExtWith {α : Type} (E : Env) (get : Module → Option α) (name : String) (n : Nat)
    (m : Module) (mn : String) : Option (Module × α) :=
  match E.findFrom m mn with
  | some m' => match get m', m'.imports.filter (·.1 == name) with
    | some a, _ => some (m', a)
    | none, [(_, mn')] => (E.findFrom m' mn').bind fun m'' => E.resolveWith get name n m''
    | none, _ => none
  | none => none

def Env.resolveExt (E : Env) (n : Nat) (m : Module) (mn name : String) : Option (Module × Ty) :=
  E.resolveExtWith (·.lookup name) name n m mn

end Asn1.X680
