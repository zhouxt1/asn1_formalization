# Where the checker and the spec disagree

`Asn1/X680/Validity.lean` defines a valid specification (`Env.Valid`, `Module.ValidAt`). `Asn1/X680/Checker.lean` (`checkEnv`), together with the parser, `Resolve` and `Values`, decides it as far as it can. Differential testing against other ASN.1 front ends added about 40 checks to the program side without adding them to `Valid`, so for a while the checker rejected specifications that `Valid` accepts. This file records that gap and how it was closed.

**Status (steps 0–3 done).** `checkEnv` reports each rule as a constructor of `Rule` (`Asn1/X680/Rule.lean`, the same messages as before), and `Rule.status` (Checker.lean) names the fields of the spec each one decides, or marks it `.notation`. The match is exhaustive, so a new check cannot be added without that decision. `Tests/Rules.lean` checks that every field named exists, that every field of the spec is decided by a rule or by the grammar, and that no rule is `.gap`. `asn1check rules` prints the table: 43 rules in `Valid`, 2 notation (X.681 7.1 class names, X.683 8.6 unused dummies), none left out. Section 1 (step 1) made `Valid` range over the types the checker checks; section 2 (step 2) added the checker's rules; section 3 (step 3) classified the checks made while reading. Step 4 (section 4) is in progress: the theorem is stated and proved from per-rule lemmas, 6 of which are still `sorry`.

## 1. Structural: what `ValidAt` ranges over (done, step 1)

`Module.ValidAt` used to apply its per-type rules only to `m.lookup nm` (type assignments). It now ranges over what the checker's `moduleTypes m` lists:

| checker (`moduleTypes`) | spec |
|---|---|
| type and value set assignments | `Module.Site.type` |
| the governors of value assignments | `Module.Site.valueGov` |
| class definitions: fixed-type value and value set fields, type field DEFAULTs (`classTypes`, moved to Validity.lean) | `Module.Site.classDef` |
| object settings `&T SomeType`, in objects, object sets and nested objects (`objTypes`, `objSetTypes`) | `Module.Site.object`, `.objectSet`, through `ObjHas` / `ObjSetHas` / `OElemsHas` |
| bodies of parameterized assignments | `Env.Valid.params`, through `ParamAssign.Has`. A value set body is `.constrained t c` on both sides (the checker used to take `t` alone) |
| `occurrences` into a `paramRef`'s type arguments (X.683 9.2) | `Occurs.paramArg` |

How `Valid` reads a parameterized body: X.683 8.5 says that, to check the use of the dummy references, each "can be regarded to be defined" as an unspecified thing of its kind and governor; 9.7, that an instance is what its actual parameters make it. So `Env.Valid.params` asks for some actual parameters, the same at every large enough fuel, of the kinds the governors allow (`ArgFits`: a value is a value of its governing type, 8.12), with which every type of the body obeys the rules (`bindParams`). A rule broken whatever the dummies stand for makes the assignment invalid; a rule that depends on them is a rule on each instance. `RefsOk` now also says a dummy is not itself parameterized (8.4), as `refsOkB` does. `Tests/Sites.lean` has examples.

Left for later:
- The checker reads a body with each dummy bound to `.raw []` (`Scope.withDummies`), which resolves to nothing, so a check that needs what a dummy stands for passes. For step 4: a check that fails there fails for every actual parameter `ArgFits` allows.
- The instances themselves (X.683 9.7): `Occurs` does not go through a reference into what it resolves to, so the types of an instance `P {INTEGER}` are checked only in `P`'s body (with some actual parameter), not with the actual parameters written. The checker does not check an instance's body either; it checks only that the actual parameters name what exists (`argsOkB`). Rules of an enclosing type that go through the reference, such as the tags of a component `a P {INTEGER}`, do see the instance.
- `Occurs` does not keep the enclosing types, which the @-paths of X.682 10.8–10.10 need; `Within` does, for `SiteOk.atPaths` (section 2).

## 2. The checker's rules in `Valid` (done, step 2)

Each rule `checkEnv` reports, and the fields of the spec it decides (`Rule.status`). New definitions are in `Validity.lean`; the helpers both sides use (`resolveValTy`, `builtinName`, `mapName`, `FieldSpec.mandatory`, `compsOf`, `tableOn`, `ObjSet.unwrap`, `classKey`) moved there from the checker.

| `Rule` | clause | spec |
|---|---|---|
| `importTwice` | 13.16 e) i) | `Module.ValidAt.importsOnce` |
| `importMissing`, `exportMissing` | 13.16 a), 13.13 a) | `ImportsOk`, `ExportsOk` |
| `exceptionRef` | 53.4, 14.1 | `ExceptionRefsOk` |
| `bodyOnlyDummy` | X.683 8.10 | `ParamAssign.NotOnlyDummy` (parameterized types, as the checker) |
| `paramGov` | X.683 8.3, 14.1 | `ParamGovsOk` |
| `paramBody` | X.683 8.3, 14.1 | already: the body is read with actual parameters (section 1), where `TypeOk.refs`, `.classRefs` and `.typeFromObjects` require its references to resolve |
| `valueRefs`, `defaultRefs`, `consRefs` | 14.1 | already: `evalVal` evaluates a reference only through `resolveVal`, so `ValuesOk`, `ComponentsOk` and `ConsOk` require them |
| `valueInType`, `defaultInType`, `fieldDefault`, `constraintKind` (C.6.1 part, `refMapsB`) | C.6.1, C.4, C.5 | `RefMaps`, `ValMaps` (a value reference names a value whose type maps to the governor's, by built-in type) in `ValuesOk`, `ComponentsOk`, `FieldDefaultsOk`, and `ElemOk` for single values and range ends |
| `constraintKind` (X.682 11.3 part) | X.682 11.3 | `ConsOk` on `.contents`: the parent is a BIT STRING or OCTET STRING type |
| `classRefs` | X.681 14.1, Annex C, 9.14 | `ClassRefsOk` |
| `typeFromObjects`, `typeFromObjectsTable` | X.681 15, 15.5 Table 1 | `TypeFromObjectsOk`, `TypeFromObjectsTableOk` |
| `args` | X.683 9.2, X.681 11.3, 12.3 | `ArgsOk` |
| `tableRefs`, `tableClass`, `tableOnField` | X.682 10.3, 10.4, 10.15, 10.1 | `TableRefsOk`, `TableClassOk`, `TableOnFieldOk` (`TableTarget`) |
| `universalTag` | 31.2.5 | `UniversalTagOk` |
| `atPath` | X.682 10.8–10.10, 10.15 | `SiteOk.atPaths`: `AtPathsOk` over `Within` (the textually enclosing types, which `Occurs` does not keep), `atParent`, `AtWalk` |
| `classDef`, `fieldDefault` | X.681 9.4, 9.8, 9.10, 9.6 | `ClassOk` (`FieldClassesOk`, `FieldDefaultsOk`) |
| `objRef`, `objClass`, `mandatoryFields`, `settingValRefs` | X.681 11.1, 11.3, 11.5–11.7, 14.1 | `ObjOk` (`ORef.Resolves`, `ClassResolves`, `ObjV.FieldsSet`, `ObjV.SettingRefsOk`) |
| `objSetClass`, `objSetRefs`, `unique`, `mandatoryFields`, `settingValRefs` | X.681 12, 12.1, 9.7 | `ObjSetOk`; 9.7 is `UniqueOk`: two objects of the set with one value of a UNIQUE field are one object (`ObjV.Same`) |
| `moduleNameTwice` | 13.7, 13.10 | `ModuleNamesOk`: names are used once, except by modules with distinct definitive identifiers (13.10). `asn1check` checks it per file (section 3) |
| `classLowerCase`, `unusedDummy` | X.681 7.1, X.683 8.6 | notation: the spelling of a reference, and whether a dummy's name is written in the assignment, decided on the lexical items |

How the spec states a rule that the checker decides only in part: the spec states the whole rule (a reference *resolves*, the object set *is* the same, two objects *are* one). The checker rejects only what it decides is broken, and passes what it cannot decide (an unresolved class, a set built with INTERSECTION, a dummy). So a rejection should mean `¬ Valid`, and an acceptance need not mean `Valid`.

## 3. Checks made while reading (done, step 3)

| where | rule | clause | decision |
|---|---|---|---|
| Lexer | no leading zero in a number | 12.8 | notation |
| Lexer | no control characters in a cstring | 12.14.1 | notation |
| Grammar `exceptionSpec`, `constraint` | ExceptionSpec grammar; `!` only after `...`, with a dummy, or on a user-defined constraint | 53.4, 49.6 | notation (49.6 is approximated: "any reference in the spec" stands for "a dummy reference") |
| Grammar `moduleDef` | ENCODING-CONTROL reference not TAG, each once | 54.2, 54.3 | notation |
| Grammar `paramList`, `actualParams` | lists not empty; a lower-case dummy has a governor | X.683 8.3, 9.5 | notation |
| Grammar `syntaxListError` | words (7.9), not a reserved word (10.6) | X.681 7.9, 10.6 | notation |
| Grammar `syntaxListError` | each field exactly once (10.9), groups hold a field (10.12 a)) | X.681 10.9, 10.12 | in `Valid`: `ClassSyntaxOk.syntaxFields`, `.optionalGroups` (over `Module.ClassWritten`), decided by the grammar |
| Grammar `fieldSpec` | UNIQUE with DEFAULT | X.681 9.6 | in `Valid`: `ClassSyntaxOk.uniqueNoDefault`, decided by the grammar |
| `Resolve.rField` | UNIQUE only on a fixed-type value field | X.681 9.6, 9.11 | notation: the productions allow UNIQUE only in "FixedTypeValueFieldSpec" |
| Grammar `tyBase` | a tag's class number as a defined value | 31.2.1 | notation: the parsed tag keeps the number the value denotes. The reading is still approximate (`intAssigned` scans the text for `v INTEGER ::= k`, which fails inside sub-parses) |
| `Values` | OID value of fewer than two arcs | 32.11 NOTE, 32.6 NOTE | already semantic: `sem` of OBJECT IDENTIFIER requires `OidWf` (two arcs or more), so `ValuesOk`, `ComponentsOk` and `ConsOk` exclude such a value |
| `Values` | ValueList and NamedValueList not mixed | 26.3 | notation |
| `Values` | `.contained` on an open type read as `.typeC` | 51.6 | fixed: `Elem.contained` keeps whether INCLUDES was written; with INCLUDES it stays a contained subtype, which Table 11 forbids on an open type (`constraintKind`); without, it is a type constraint |
| Tools/Check.lean | two modules with one name | 13.7, 13.10 | `ModuleNamesOk` over an `Env`; `asn1check` takes each file as a sphere of interest (`moduleNamesTwice`), since the files of a corpus unit may hold several editions of one module. Within a file it now allows 13.10's exception (distinct definitive identifiers) |

`Tests/Rules.lean` lists the fields the grammar decides (`grammarDecided`).

## 4. Step 4: the checker rejects only what the spec rejects (done)

`Asn1/X680/Soundness.lean` proves, with no `sorry` (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`)

```lean
theorem checkEnv_sound (h : Env.Valid E H) : ∃ N, ∀ n ≥ N, ∀ v ∈ checkEnv E n, v.IsNotation
```

from one lemma per part of `checkEnv` (`moduleChecks`, `siteChecks`, `typeChecks`, `paramChecks`, `classChecks`, `objSetChecks`, `objChecks`, `typeAssignChecks`, `valueChecks`), and `moduleNamesTwice_sound` for what `asn1check` checks per file (13.7). Each rule lemma has the form "the spec's rule holds from fuel `n` on ⇒ the check passes at `n`".

How it is set up:
- The checker has no `partial def`: recursion over the syntax is by size (`Size.lean`), and the functions that chase references take fuel.
- More fuel resolves the same (`Monotone.lean`, and `builtin`, `builtinV`, class fields and the components where they are all known in `SoundValues.lean`).
- Why "from some fuel on": with too little fuel a reference does not resolve and the checker rejects. `entries` also spends one unit of fuel per component. So `N` is the larger of `Valid`'s bound and `sizeOf E + 1`.
- `checkEnv_sound_at` takes the spec at every fuel from `n` on. The spec checks a constraint's elements and values a few levels of fuel down, so the lemmas take it at a larger fuel, where it resolves at least what the checker does.

The value rules (`SoundValues.lean`):
- The checker decides an element set as the spec's `ESet` holds it, root and root with additions apart (`Dec`). `intInES_decides`, `sizeInES_decides` and `charsInES_decides` show that when it decides, it decides the spec's answer. `patEnds_mem` shows that the PATTERN matcher lists exactly the ends of the matches (Annex A).
- `notInTy_sound`: a value the walk through tags, constraints and references says is outside is outside (`sem`).
- `valOkB_of`: a value that evaluates, at arbitrarily large fuel, to a value of the type passes. When component names repeat, a pigeonhole picks the component the spec uses at infinitely many fuels.
- 49.7 (`constraintKindsOkB_of`): for INTEGER, a number in the set has a candidate the checker tries that lies alike against every number the set writes (`exists_candidate`); for strings, a set built of single values is one of them; for SIZE, its constraint selects nothing.

Parameterized bodies (`SoundParams.lean`, `siteChecks_param_nil`): the checker reads a body with its dummies bound to nothing (`Scope.withDummies`), the spec with actual parameters (`bindParams`). `ScLess sc1 sc2` says the first scope knows less: what it resolves, the second resolves alike (`resolveIn_less`, `builtin_less`, `entries_less`). Each rule the checker passes on the second it passes on the first (`refsOkB_less`, ..., `constraintKindsOkB_less`, where the decisions are monotone, `DLe`), and the tag rule follows from the spec on the second (`tagsOkB_of_less`).

Changes made to the spec while proving:
- X.681 11: mandatory fields and setting references are required of every object *written* in an object set (`OElemsWrites`), not only of the objects its set arithmetic keeps; and as an explicit setting, not through a DEFAULT (`ObjV.FieldsSet`).
- X.683 8.5 (`Env.Valid.params`, `ParamBodyOk`): the actual parameters that make a parameterized body valid are now chosen once, with which it is valid at every large enough fuel. Before, `ValidAt.params` chose them anew at each fuel, so parameters whose references the fuel does not reach could make a body "valid".

Changes made to the checker, because it rejected what the spec accepts:
- 16.1, 16.2: the cycle checks follow references with fuel instead of keying assignments by `"{module}.{name}"`, which two editions of one module share (13.10).

and, in this round, none of which changed the checker's verdicts on a corpus of published modules or on generated modules; tests in `Tests/Frontend.lean`:
- 50.5: `SIZE (1..10) EXCEPT SIZE (1..2, ..., 3)` has size 3 in its root; the checker took the inner SIZE with its additions. FROM with EXCEPT and ALL EXCEPT took characters, not strings (`"ab" EXCEPT "b"` permits b). Element sets are now decided root and all apart (`Dec`), FROM only that a character is outside (`alphaNo`).
- 51.4.2: only the values in a range need be values of the parent: `T (-1<..5)` on `INTEGER (0..10)` was rejected (`intPoints`).
- 49.7 only for the type's own constraint (and its SIZE elements): the constraint inside a SIZE in a union need not select anything.
- WITH COMPONENTS, PRESENT/ABSENT and component values: held against each component of the name, as the spec does, not the first.
- Values of a type from objects (X.681 15) are those of the objects' settings, not of the field's type: the component and time format checks do not go through one (`builtinV`).
- X.683 8.5, in a parameterized body, where a dummy is bound to nothing:
  - Tags, WITH COMPONENTS names, @-paths, PRESENT/ABSENT and C.6.1 in component values judged incomplete component lists (a COMPONENTS OF a dummy). They are now decided only when every COMPONENTS OF resolves (`entriesKnown`).
  - A selection from a dummy (`x < T`) was rejected as a reference that does not resolve.
  - A field of a dummy class (`C.&id`) had an indeterminate tag, clashing with every other. The checker's tags (`tagsOfB`) are now only those it knows; a type whose tags it does not know takes no part.
  - The path of a class field through a dummy class, the governor of a value given as an actual parameter, and the size of a value of a type that does not resolve are no longer decided.
- Value keys of UNIQUE are values (`VKey`), not strings.

Not a soundness question, but found on the way: the spec checks a parameterized body for *some* actual parameters and never checks an instance, so `P {T} ::= SEQUENCE { a [0] INTEGER OPTIONAL, b T }` with `U ::= P {[0] BOOLEAN}` is accepted by both, though `U` written out breaks 25.6. Whether X.683 requires each instance to be valid is to check against its text (completeness, part (c)).

## 5. How to check the work

- `lake build Asn1 Tests asn1check`; `Tests/Frontend.lean` uses `broken`, which sees only `checkEnv`; `Tests/Rules.lean` checks `Rule.status` against the spec's fields.
- `asn1check rules`: the rules and their status.
- `scripts/check_coverage.py COVERAGE.md` after refreshing the map.
