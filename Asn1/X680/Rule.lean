/-!
# The rules the front end checks

One constructor for each rule `checkEnv` (Checker.lean) reports broken, with the message it prints,
and for X.680 13.7, which `asn1check` checks for each file (`moduleNamesTwice`).
`Rule.status` (Checker.lean) says for each where it stands against `Env.Valid`: a field of the
spec, part of one, not yet in the spec (the gap, SPEC-GAP.md), or a rule about notation that stays
out of the spec on purpose. A new check needs a new constructor, so it cannot be added without
that decision.
-/

namespace Asn1.X680

inductive Rule where
  -- the specification as a whole
  /-- X.680 13.7, 13.10: a module name is used once, except by modules with distinct definitive
  identifiers -/
  | moduleNameTwice
  -- the module as a whole
  /-- X.680 13.16 e) i): a module imported from twice, or from itself -/
  | importTwice
  /-- X.683 8.6: a dummy reference is used -/
  | unusedDummy
  /-- X.683 8.10: the right side is not only a dummy reference -/
  | bodyOnlyDummy
  /-- X.681 7.1: an objectclassreference has no lower-case letter -/
  | classLowerCase
  /-- X.680 53.4, 14.1: the defined value of an exception spec exists -/
  | exceptionRef
  /-- X.680 3.8.88: a module assigns each name once -/
  | assignedTwice
  /-- X.680 13.16 a): an imported symbol is in its module -/
  | importMissing
  /-- X.680 13.13 a): an exported symbol is assigned or imported -/
  | exportMissing
  -- each type written in the module, and each type inside it
  /-- X.682 10.8–10.10, 10.15: the @ of a component relation constraint -/
  | atPath
  /-- X.680 25.14, 29.10, 20.2, 19.5, 22.4: distinct names -/
  | names
  /-- X.680 25.6, 25.7, 27.3, 29.3, 52.7, 31.2.9: distinct tags -/
  | tags
  /-- X.680 25.9, 29.4: additions under automatic tagging -/
  | autoAdditions
  /-- X.680 13.16, 14, 30.1: type references resolve -/
  | refs
  /-- X.681 14.1, 15: the object set or class of information from objects resolves -/
  | typeFromObjects
  /-- X.683 9.2, 14.1: an actual parameter names a value, object or object set that exists -/
  | args
  /-- X.681 14.1, Annex C: class references resolve -/
  | classRefs
  /-- X.680 14.1, 16.2, 25.12: a DEFAULT's value references resolve -/
  | defaultRefs
  /-- X.680 14.1, 51: a constraint's value references resolve -/
  | consRefs
  /-- X.681 15.5 Table 1: information from objects used as a type is a type -/
  | typeFromObjectsTable
  /-- X.682 10.3: a table constraint names an object set -/
  | tableRefs
  /-- X.682 10.4, 10.15: a table constraint's object set is of the field's class -/
  | tableClass
  /-- X.682 10.1: a table constraint is on a class field type or INSTANCE OF -/
  | tableOnField
  /-- X.680 25.12: a DEFAULT value is in its type -/
  | defaultInType
  /-- X.680 50.10, 50.11: a constraint's values are in the parent type -/
  | serialVals
  /-- X.680 51.8.6: WITH COMPONENTS names components of the type, each once -/
  | innerNames
  /-- X.680 49.7, 51.1 Table 11, Table 12, 51.3.2, 51.4.4, 51.5.3, 51.7.3, 51.8.6; X.682 11.3 -/
  | constraintKind
  /-- X.680 25.5, 27.2: COMPONENTS OF a sequence (set) type -/
  | componentsOf
  /-- X.680 31.2.5: no tag of the UNIVERSAL class -/
  | universalTag
  /-- X.680 51.8.10.1: PRESENT and ABSENT only on OPTIONAL components -/
  | presence
  -- parameterized assignments
  /-- X.683 8.3, 14.1: a parameter's governor resolves -/
  | paramGov
  /-- X.683 8.3, 14.1: the body of a parameterized assignment names what exists -/
  | paramBody
  -- classes
  /-- X.681 9.6, 16.2: a field's DEFAULT is in its type -/
  | fieldDefault
  /-- X.681 9.4, 14.1: a field names a class or type that exists -/
  | classDef
  -- object sets and objects
  /-- X.681 12.1, 14.1: the class of an object set resolves -/
  | objSetClass
  /-- X.681 9.7: no two objects with one value of a UNIQUE field -/
  | unique
  /-- X.681 12: an object set names objects and object sets that exist -/
  | objSetRefs
  /-- X.681 11 (11.5, 11.6): an object sets each mandatory field -/
  | mandatoryFields
  /-- X.681 11.7, 14.1: an object's settings name values that exist -/
  | settingValRefs
  /-- X.681 11.3, 14.1: an object defined as another names one that exists -/
  | objRef
  /-- X.681 11.1, 14.1: the class of an object resolves -/
  | objClass
  -- type and value assignments
  /-- X.680 16.1, 3.8.61: a type is not defined through itself only -/
  | typeCycle
  /-- X.680 14.1, 16.2: a value's references resolve -/
  | valueRefs
  /-- X.680 16.2, C.6.1: a value is in its type -/
  | valueInType
  /-- X.680 16.2, 14.9: a value is not defined through itself -/
  | valueCycle
  deriving DecidableEq, Repr, Inhabited

/-- Every rule. -/
def Rule.all : List Rule :=
  [.moduleNameTwice, .importTwice, .unusedDummy, .bodyOnlyDummy, .classLowerCase, .exceptionRef, .assignedTwice,
   .importMissing, .exportMissing, .atPath, .names, .tags, .autoAdditions, .refs, .typeFromObjects,
   .args, .classRefs, .defaultRefs, .consRefs, .typeFromObjectsTable, .tableRefs, .tableClass,
   .tableOnField, .defaultInType, .serialVals, .innerNames, .constraintKind, .componentsOf,
   .universalTag, .presence, .paramGov, .paramBody, .fieldDefault, .classDef, .objSetClass,
   .unique, .objSetRefs, .mandatoryFields, .settingValRefs, .objRef, .objClass, .typeCycle,
   .valueRefs, .valueInType, .valueCycle]

theorem Rule.mem_all (r : Rule) : r ∈ Rule.all := by cases r <;> decide

/-- The message for a broken rule; `detail` is the dummy reference of X.683 8.6 and 8.10. -/
def Rule.text (detail : String) : Rule → String
  | .moduleNameTwice => "two modules with one name and no distinct object identifiers (13.7, 13.10)"
  | .importTwice => "a module imported from twice, or from itself (13.16 e) i))"
  | .unusedDummy => s!"the dummy {detail} is not used (X.683 8.6)"
  | .bodyOnlyDummy => s!"the right side is only the dummy {detail} (X.683 8.10)"
  | .classLowerCase => "a class reference with a lower-case letter (X.681 7.1)"
  | .exceptionRef => "an exception spec names no value (53.4, 14.1)"
  | .assignedTwice => "names assigned twice (3.8.88)"
  | .importMissing => "an imported symbol its module does not have (13.16 a))"
  | .exportMissing => "an exported symbol the module neither assigns nor imports (13.13 a))"
  | .atPath => "a component relation constraint's @ names no component of its structure, or one not constrained by the same object set (X.682 10.8-10.10, 10.15)"
  | .names => "distinct names (25.14, 29.10, 20.2, 19.5, 22.4)"
  | .tags => "distinct tags (25.6, 25.7, 27.3, 29.3, 52.7, 31.2.9)"
  | .autoAdditions => "textually tagged additions (25.9, 29.4)"
  | .refs => "a reference that does not resolve (13.16, 14, 30.1)"
  | .typeFromObjects => "an object set or class that does not resolve (X.681 14.1, 15)"
  | .args => "an actual parameter names a value, object or object set that does not exist (X.683 9.2, 14.1)"
  | .classRefs => "a class reference that does not resolve (X.681 14.1, Annex C)"
  | .defaultRefs => "a DEFAULT names no value (14.1, 16.2, 25.12)"
  | .consRefs => "a constraint names no value (14.1, 51)"
  | .typeFromObjectsTable => "information from objects that is not a type (X.681 15.5 Table 1)"
  | .tableRefs => "a table constraint names no object set (X.682 10.3)"
  | .tableClass => "a table constraint's object set is of another class (X.682 10.4, 10.15)"
  | .tableOnField => "a table constraint on a type that is not a class field or INSTANCE OF (X.682 10.1)"
  | .defaultInType => "a DEFAULT value outside its type (25.12)"
  | .serialVals => "a constraint value outside the parent type (50.10, 50.11)"
  | .innerNames => "WITH COMPONENTS names a component the type does not have, or one twice (51.8.6)"
  | .constraintKind => "a constraint that does not apply to the type, or selects nothing (49.7, 51.1 Table 11, Table 12, 51.3.2, 51.4.4, 51.5.3, 51.7.3, 51.8.6; X.682 11.3)"
  | .componentsOf => "COMPONENTS OF a type that is not a sequence (set) type (25.5, 27.2)"
  | .universalTag => "a tag of the UNIVERSAL class (31.2.5)"
  | .presence => "PRESENT or ABSENT on a component not marked OPTIONAL (51.8.10.1)"
  | .paramGov => "a parameter is governed by a class or type that does not resolve (X.683 8.3, 14.1)"
  | .paramBody => "the body of a parameterized type names a type or class that does not exist (X.683 8.3, 14.1)"
  | .fieldDefault => "a field's DEFAULT outside its type (X.681 9.6, 16.2)"
  | .classDef => "a field of the class names a class or type that does not exist (X.681 9.4, 14.1)"
  | .objSetClass => "the class of an object set does not resolve (X.681 12.1, 14.1)"
  | .unique => "two objects with one value of an identifier field (X.681 9.7)"
  | .objSetRefs => "an object set names an object or object set that does not exist (X.681 12)"
  | .mandatoryFields => "an object without a mandatory field (X.681 11)"
  | .settingValRefs => "an object's setting names no value (X.681 11.7, 14.1)"
  | .objRef => "an object reference that does not resolve (X.681 11.3, 14.1)"
  | .objClass => "the class of an object does not resolve (X.681 11.1, 14.1)"
  | .typeCycle => "a type defined through itself only (16.1, 3.8.61)"
  | .valueRefs => "a value reference that does not resolve (14.1, 16.2)"
  | .valueInType => "a value outside its type (16.2, C.6.1)"
  | .valueCycle => "a value defined through itself (16.2, 14.9)"

/-- Where a rule stands against `Env.Valid`. The names are fields of `TypeOk`, `Module.ValidAt` or
`Env.Valid`. -/
inductive Rule.Status where
  /-- the rule is these fields of the spec: when the checker reports it broken, they do not hold -/
  | valid (fields : List Lean.Name)
  /-- part of the rule is these fields; `missing` is the part the checker checks beyond them -/
  | partly (fields : List Lean.Name) (missing : String)
  /-- not in the spec yet (SPEC-GAP.md) -/
  | gap
  /-- about how ASN.1 is written: stays out of the spec (COVERAGE.md status `notation`) -/
  | notation
  deriving Repr, BEq

end Asn1.X680
