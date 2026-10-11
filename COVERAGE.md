# Coverage

Every numbered normative subclause of X.680 (02/2021), X.681, X.682, X.683, X.690 and X.691, and what the Lean spec does with it. The annexes that are part of a Recommendation are covered like its clauses; informative annexes get one row each. NOTEs and EXAMPLEs are not rows, but the tests check many examples (named in the Where column).

Each row has one status:

| Status | Meaning |
|---|---|
| mechanized | the rule is a definition, constructor or validity rule of the Lean spec (Where names it) |
| partial | part of the rule is; Where says what is missing |
| notation | the rule is about how ASN.1 is written (lexical items, productions, value notation). The spec works on parsed notation (`Ty`, `Val`), so there is nothing to mechanize; Where names the constructor that records the construct, if any |
| n/a | scope, references, definitions, recommendations, rules about other documents |
| open | formal content that is not mechanized yet, or a decision in the ledger (`OPEN.md`) that leaves it out |
| informative | an informative annex |

`scripts/check_coverage.py COVERAGE.md` checks the map against the sources: each status is one of these, each backticked Lean name exists, each ledger id is in `OPEN.md`, and each file exists.

## Summary

| Document | Rows | mechanized | partial | open | notation | n/a | informative |
|---|---|---|---|---|---|---|---|
| X.680 1–24 | 130 | 56 | 7 | 10 | 41 | 16 | — |
| X.680 25–37 | 96 | 48 | 3 | 2 | 33 | 10 | — |
| X.680 38–end, annexes | 188 | 90 | 11 | 9 | 50 | 21 | 7 |
| X.681 | 83 | 29 | 17 | 11 | 15 | 8 | 3 |
| X.682 | 38 | 14 | 5 | 3 | 7 | 8 | 1 |
| X.683 | 30 | 6 | 7 | 4 | 5 | 6 | 2 |
| X.690 | 55 | 48 | 3 | 1 | — | 3 | — |
| X.691 | 112 | 83 | 6 | 4 | — | 13 | 6 |
| **Total** | **732** | **374** | **59** | **44** | **151** | **85** | **19** |

Everything that decides which values a type has, the tags of a type, and whether it is extensible is mechanized. What is not falls into these groups:

1. **The encoding rules' obligations** (X.680 6, 7.1–7.3): extension-related types are defined (`ExtendsT`, `ExtRelated`), but the theorems that an encoding rule meets clause 7 belong to the encoding-rule layer: `EncodingRule.ExtensionCompatible` states them, and no rule proves them yet.
2. **The module system beyond references**: what EXPORTS restricts (13.16 b)), module object identifiers (13.8–13.12, 13.16 e) beyond i)), WITH SUCCESSORS / DESCENDANTS (13.16 f)), 14.7, and encoding instructions and references (9, 13.5), which do not change values. Imports and exports name what exists (`ImportsOk`, `ExportsOk`).
3. **Compatibility of values with their governors** (14.8–14.9, Annex C.3, C.6.2–C.6.5, X.683 8.12–8.13): values are evaluated by `evalVal` without the identical-type normal form of Annex C.
4. **Validity of information objects and parameterized assignments**: the rules the front end checks are in `Valid` (`ClassOk`, `ObjOk`, `ObjSetOk`, `UniqueOk`, `TypeOk`'s table and @-path rules, `ParamGovsOk`; SPEC-GAP.md). Still missing: objects of the governing class (X.681 8.2, 11.3, 12.10), recursion (11.2, 12.2, 9.15), variable-type settings (11.8–11.9), Table 1 for values and object sets (15.4–15.5, 15.11–15.13), INSTANCE OF's class (C.1), X.682 10.14, 10.21, 11.2, and X.683's dummy rules 8.7–8.9, 8.11–8.13.
5. **Abstract syntax parameters** (X.683 10, X.681 B.5), recorded as X683-1.
6. **Modules defined in the text but not transcribed**: ASN1-CHARACTER-MODULE (clause 42), DefinedTimeTypes (Annex B.2), ASN1-Object-Identifier-Module (Annex D.2).
7. **Smaller rules**: VersionNumber (25.16, 29.6), exception identifiers (53.5–53.6), 51.8.3, Table 11 note b), the OID-IRI label rules (34.3, 35.3), SIZE on CHARACTER STRING (X680-27), and the empty-column rule of X.681 15.12 (X681-4).

## The map

### X.680 clauses 1–24

| Clause | Subject | Status | Where |
|---|---|---|---|
| 1 | Scope | n/a | — |
| 2, 2.1–2.2 | Normative references | n/a | — |
| 3.1–3.7 | Terms defined in other documents | n/a | — |
| 3.8.1–3.8.30 | Additional definitions | n/a | — |
| 3.8.31–3.8.41 | Extension terms (addition, insertion point, extension-related, extensible) | n/a | used by `ExtendsCons`, `ExtendsT`, `ExtRelated`, `Extensible` |
| 3.8.42–3.8.97 | Additional definitions | n/a | — |
| 4 | Abbreviations | n/a | — |
| 5.1–5.10 | Conventions for productions | n/a | — |
| 5.11 | Value references and typing of values | n/a | introduces Annex C (see 14.8–14.9) |
| 6 | ASN.1 model of type extension | partial | `ExtendsT`, `ExtRelated`, `Env.Extends` define extension-related types; `VSet` separates root from additions; missing: the abstract syntax of an extensible type does not yet include values of extension-related types |
| 7.1–7.3 | Extensibility requirements on encoding rules | open | a theorem per encoding rule over `ExtRelated`; stated as `EncodingRule.ExtensionCompatible`, not proved for `X690.rule` or `X691.rule` |
| 8.1 | Tag classes | mechanized | `TagClass`, `Tag` |
| 8.2 | Tag number is a non-negative integer | mechanized | `Tag.num : Nat` |
| 8.3 | Restrictions on user tags (pointer to 31.2) | n/a | 31.2 |
| 8.4, Table 1 | Universal class tag assignments | mechanized | `Ty.universalTag?`, `tagsOf` (INSTANCE OF: UNIVERSAL 8) |
| 8.5–8.6 | Canonical order of tags | mechanized | `TagClass.rank`, `Tag.lt`; `Tests/Tags.lean` |
| 9.1–9.3 | Encoding instructions: type prefix, control section, encoding reference | open | encoding prefixes (31.3) and encoding control sections (54) are not represented in `Ty`; they do not change values (3.8.27 NOTE) |
| 9.4 | Instruction syntax given by the encoding reference's document | n/a | Annex E documents |
| 9.5 | Instructions with different references are independent | open | as 9.1–9.3 |
| 9.6 | Effect of several instructions with one reference | n/a | left to other documents |
| 9.7 | Instruction on a TypeAssignment follows its references | open | as 9.1–9.3 |
| 10.1–10.5 | Which productions are used for types, values, assignments | notation | — |
| 11.1–11.7 | ASN.1 character set, case distinction | notation | names are case-sensitive `String`s |
| 11.8 | Hyphen variants treated as identical | n/a | recommendation ("should") |
| 12.1 | General lexical rules, white-space, newline | notation | — |
| 12.2–12.5 | typereference, identifier, valuereference, modulereference | notation | names are `String` after parsing |
| 12.6–12.7 | comment, empty | notation | — |
| 12.8 | number | notation | parsed to `Int` / `Nat` |
| 12.9 | realnumber | notation | parsed to `RealVal` |
| 12.10–12.13 | bstring, xmlbstring, hstring, xmlhstring | notation | parsed to `Val.bits`, `Val.octets` |
| 12.14–12.15, Table 3 | cstring, xmlcstring and its escapes | notation | parsed to `Val.chars` |
| 12.16 | simplestring | notation | `Elem.settings` keeps its property/setting pairs as strings, checked by `settingsOk` |
| 12.17–12.18 | tstring, xmltstring | notation | contents read by `Notation.parse` (Time.lean) |
| 12.19 | psname | notation | as 12.16 |
| 12.20–12.25 | "::=", "..", "...", "[[", "]]", encodingreference | notation | — |
| 12.26–12.27 | Integer and non-integer Unicode labels | notation | arcs of `Val.iri` are `String`s |
| 12.28–12.36, Table 4 | XML items, xmlasn1typename | notation | — |
| 12.37–12.38 | Single-character items, reserved words | notation | — |
| 13.1 | ModuleDefinition productions | notation | parsed to `Module`, `ModuleHeader`; DefinitiveIdentification, EncodingReferenceDefault, Exports, EncodingControlSections not kept |
| 13.2 | Empty TagDefault is EXPLICIT TAGS | notation | `TagDefault` has no empty alternative; the parser supplies `.explicit` (its doc comment cites this as 13.3) |
| 13.3 | Automatic tagging selected by AUTOMATIC TAGS | mechanized | `TagDefault.automatic`, `autoSeq`, `autoChoice` |
| 13.4 | EXTENSIBILITY IMPLIED | mechanized | `ModuleHeader.extImplied` in `sem` (sequence, set, choice, enumerated), `conceptual`, `ExtendsT` |
| 13.5 | Default encoding reference | open | as 9.1–9.3 |
| 13.6 | Module name | mechanized | `Module.name`, `Env.find` |
| 13.7 | Module names unique in sphere of interest | mechanized | `ModuleNamesOk` (field `moduleNames` of `Env.Valid`), with 13.10's exception: two modules may share a name when their definitive identifiers differ |
| 13.8–13.9 | DefinitiveIdentification, AssignedIdentifier | partial | `Module.oid`, `Module.importOids` (object identifiers; IRIs not represented); 13.9 a), b) on defined values not checked |
| 13.10 | GlobalModuleReference names another module, perhaps under another name | mechanized | `Env.findFrom` (by object identifier, the name may differ), `Env.resolveWith`, `Env.resolveExtWith`; X680-28 |
| 13.11–13.12 | AssignedIdentifier definitive, and required | partial | 13.11: `Env.findFrom`; 13.12 (required when the module has one) not checked |
| 13.13–13.14 | Exports | partial | `Module.exports` (`none` for EXPORTS ALL or no EXPORTS, 13.14), `ExportsOk` (13.13 a)); what EXPORTS restricts is not used by imports (13.16 b)) |
| 13.15 | Implicit export of named numbers, enumerations, named bits | notation | identifiers are not references after parsing (`Val.enum`; named numbers already `Int`) |
| 13.16 a) | Imported symbol defined in, or imported once by, the source module | mechanized | `ImportsOk`, `Env.resolveWith` |
| 13.16 b) | Imported symbol must be exported | open | no exports (13.13) |
| 13.16 c) | External references only to symbols in the SymbolList | open | `Env.resolveExtWith` ignores `Module.imports` |
| 13.16 d) | Empty SymbolsImported | notation | — |
| 13.16 e) | Distinct module references and OIDs in Imports | partial | i): field `importsOnce` of `Module.ValidAt` (no module imported from twice, or from itself); the distinct object identifiers are not checked |
| 13.16 f) | WITH SUCCESSORS / WITH DESCENDANTS | open | module OIDs not represented |
| 13.17 | External references without IMPORTS | mechanized | `Ty.extRef`, `Env.resolveExt` |
| 13.18 | Implicit import of named identifiers | notation | as 13.15 |
| 13.19 | Imported symbol means what it means in its module | mechanized | `Env.resolveWith`, `resolveIn`; `Tests/Tags.lean` |
| 13.20 | Ambiguous symbol used only as external reference | mechanized | `Env.resolveWith`: a symbol imported more than once, or imported and assigned, does not resolve directly |
| 13.21 | Assignment kinds; distinct reference names | mechanized | `Module.types`, `.values`, `.classes`, `.objects`, `.objectSets`, `.params`; `AssignedOnce` (3.8.88, 3.8.93) |
| 13.22 | Encoding control sections (pointer to 54) | n/a | clause 54 |
| 14.1 | DefinedType, DefinedValue | mechanized | `Ty.ref`, `Ty.extRef`, `Ty.paramRef`, `Val.ref`, `resolveTy`, `resolveVal` |
| 14.2–14.3 | NonParameterizedTypeName (XML tag names) | notation | — |
| 14.4 | Plain references only to own or imported assignments | mechanized | `Env.resolveWith`, `RefsOk`; an unresolved value reference denotes nothing (`evalVal`) |
| 14.5 | External reference target assigned or imported there | mechanized | `Env.resolveExtWith` (a), and b) through a single import) |
| 14.6 | External reference syntax, to a different module | partial | `Ty.extRef`, `Val.ref` with a module name, `Env.resolveExt`; "different module" not checked |
| 14.7 | modulereference in exactly one SymbolsFromModule | open | not checked |
| 14.8–14.9 | DefinedType/DefinedValue compatible with governor (C.6.2) | open | Annex C value mapping not mechanized; `evalVal` does not consult the governing type |
| 15.1–15.2 | Purpose of component references | n/a | — |
| 15.3–15.10 | AbsoluteReference notation | notation | not used in modules (15.3 NOTE); not represented |
| 16.1 | TypeAssignment | mechanized | `Module.types`, `Module.lookup` |
| 16.2 | ValueAssignment, XMLValueAssignment | mechanized | `Module.values`, `resolveVal`, `ValuesOk` |
| 16.3–16.5 | Value / XMLValue in assignments, empty-element tag | notation | — |
| 16.6 | ValueSetTypeAssignment | mechanized | type assignment of `Ty.constrained` (`Module` doc); `ParamAssign.valueSet` via `resolveTy` |
| 16.7 | ValueSet has at least one value | mechanized | `NonEmpty` |
| 16.8 | Value set assignment equals constrained type | mechanized | `Ty.constrained`, `resolveTy` |
| 17.1 | Type | mechanized | `Ty` |
| 17.2 | BuiltinType | mechanized | constructors of `Ty`, `builtin`; PrefixedType is `Ty.tagged` only (encoding prefixes, 31.3, not represented) |
| 17.3 | ReferencedType | mechanized | `Ty.ref`, `Ty.extRef`, `Ty.paramRef`, `Ty.generalizedTime`, `Ty.utcTime`, `Ty.objectDescriptor`, `Ty.selection`, `Ty.fromObjects`; `builtin` |
| 17.4 | ConstrainedType | mechanized | `Ty.constrained` |
| 17.5 | NamedType | notation | `Comp.mk`, `Alt.mk` |
| 17.6 | Identifier has no effect on the type | partial | tags ignore identifiers, but `Val.seq` and `Val.choice` carry them; types differing only in identifiers have different values |
| 17.7–17.10 | Value, XMLValue, BuiltinValue, XMLBuiltinValue | notation | `Val` |
| 17.11 | ReferencedValue | notation | `Val.ref`, `Val.fromObject`, replaced by `evalVal` |
| 17.12–17.13 | Value notations for any type; NamedValue | notation | — |
| 17.14 | Extension marker does not affect value notation | notation | `Val` carries no extension information |
| 18.1 | BOOLEAN | mechanized | `Ty.boolean`, `sem` |
| 18.2 | Tag UNIVERSAL 1 | mechanized | `Ty.universalTag?` |
| 18.3–18.4 | Boolean value notation | notation | `Val.bool` |
| 19.1 | INTEGER, NamedNumberList | mechanized | `Ty.integer`, `sem` |
| 19.2 | No "-0" | notation | — |
| 19.3 | NamedNumberList not significant | mechanized | `sem` ignores the named numbers (cited there as 19.4) |
| 19.4 | DefinedValue in NamedNumber is integer | notation | named numbers are `Int` after parsing |
| 19.5–19.6 | Named numbers and their identifiers distinct | mechanized | `NamesOk` |
| 19.7 | Order of NamedNumbers not significant | mechanized | `sem`, `eqv`, `tagsOf` do not read the list |
| 19.8 | Tag UNIVERSAL 2 | mechanized | `Ty.universalTag?` |
| 19.9–19.13 | Integer value notation | notation | `Val.int` |
| 20.1 | ENUMERATED, root and additional enumeration | mechanized | `Ty.enumerated`; `sem` (extensible with an ellipsis or EXTENSIBILITY IMPLIED) |
| 20.2 | Identifiers and numbers distinct | mechanized | `NamesOk` over `enumNumbers` |
| 20.3 | Numbering of root identifiers | mechanized | `enumNumbers`, `nextFree` |
| 20.4 | Each addition greater than earlier additions | mechanized | `NamesOk` |
| 20.5 | Addition numbers differ from all earlier items | mechanized | `NamesOk`; `Tests/Enumerated.lean` |
| 20.6 | Numbering of addition identifiers | mechanized | `enumNumbers` (X680-12); `Tests/Enumerated.lean` |
| 20.7 | Tag UNIVERSAL 10 | mechanized | `Ty.universalTag?` |
| 20.8–20.9 | Enumerated value notation | notation | `Val.enum` |
| 20.10 | Value is an identifier of the type | mechanized | `sem` (`.enum` of a root or additional identifier) |
| 20.11 | Identifier preferred to a reference name | notation | — |
| 21.1 | REAL | mechanized | `Ty.real` |
| 21.2 | Tag UNIVERSAL 9 | mechanized | `Ty.universalTag?` |
| 21.3 | Abstract values of REAL | mechanized | `RealVal`, `RealVal.Wf`, `sem` |
| 21.4–21.5 | Associated type for value and subtype notation | mechanized | `realAssoc`, `RealVal.Denotes`, `ESet.byReal` (X680-23), `innerTarget`; `Tests/Applicability.lean` |
| 21.6–21.7 | Real value notation | notation | `Val.real` |
| 21.8 | realnumber denotes base 10 (base 2 if constrained) | notation | `RealVal.num` records the base |
| 22.1 | BIT STRING, NamedBitList | mechanized | `Ty.bitString` |
| 22.2 | Leading and trailing bit | mechanized | `Bits` (leading bit first) |
| 22.3 | Named bit numbers non-negative | mechanized | named bits are `Nat` in `Ty.bitString` |
| 22.4–22.5 | Named bit numbers and identifiers distinct | mechanized | `NamesOk` |
| 22.6 | NamedBitList does not change the values | mechanized | `sem` |
| 22.7 | Trailing 0 bits with named bits | mechanized | `eqv`, `stripTrailingZeros` (X680-3) |
| 22.8 | Tag UNIVERSAL 3 | mechanized | `Ty.universalTag?` |
| 22.9–22.20 | Bit string value notation, incl. CONTAINING | notation | `Val.bits`; the contents constraint is `Constraint.contents` (X.682) |
| 23.1 | OCTET STRING | mechanized | `Ty.octetString`, `sem` |
| 23.2 | Tag UNIVERSAL 4 | mechanized | `Ty.universalTag?` |
| 23.3–23.4 | Octet string value notation | notation | `Val.octets` |
| 23.5 | Octet and bit terminology for encoding rules | n/a | — |
| 23.6–23.10 | bstring/hstring padding, CONTAINING | notation | — |
| 24.1 | NULL | mechanized | `Ty.null`, `sem` |
| 24.2 | Tag UNIVERSAL 5 | mechanized | `Ty.universalTag?` |
| 24.3 | Null value notation | notation | `Val.null` |

### X.680 clauses 25–37

| Clause | Subject | Status | Where |
|---|---|---|---|
| 25.1 | SequenceType grammar | notation | `Ty.sequence`, `Comp`, `Presence`, `ExtAdd` (the exception spec is dropped) |
| 25.2 | textually tagged type | mechanized | `Ty.textuallyTagged`, `Comp.textuallyTagged` (encoding prefixes are not represented, so b) holds only through parsing) |
| 25.3 | when automatic tagging is selected | mechanized | `autoSeq`; `Tests/Tags.lean` (NOTE 1 example) |
| 25.4 | decided before COMPONENTS OF is expanded | mechanized | `autoSeq` (on the components as written), `entryTags` |
| 25.5 | COMPONENTS OF transformation | mechanized | `expand`, `entries`, `ComponentsOk` (a sequence type with at least one component); `builtin` drops constraints |
| 25.6–25.6.3 | distinct tags in OPTIONAL/DEFAULT runs | mechanized | `RunsDistinct`, `TagsOk` (the root series; the complete series with the 52.7 element) |
| 25.7 | additions vs trailing root component tags | mechanized | `TagsOk` (`.sequence`, third conjunct) |
| 25.8 | automatic tagging after COMPONENTS OF | mechanized | `entryTags` (numbers the expanded `entries`) |
| 25.9 | additions untagged under automatic tagging | mechanized | `AutoAdditionsOk` |
| 25.10 | numbering of the replacement tags | mechanized | `autoNumber`, `entryTags`, `isExplicit` (`.default_`); X680-10; `Tests/Tags.lean` |
| 25.11 | OPTIONAL/DEFAULT values may be omitted | mechanized | `SeqShape`, `seqVSet` |
| 25.12 | omitted DEFAULT equals its value | mechanized | `Presence.default_`, `SeqEqv`, `eqv`; `ComponentsOk` (the DEFAULT value is a value of the component's type) |
| 25.13 | presence within an extension addition group | mechanized | `SeqShape` |
| 25.14 | distinct component identifiers | mechanized | `NamesOk` |
| 25.15 | an addition needs earlier mandatory additions | mechanized | `SeqShape` (single-component additions; X680-25) |
| 25.16 | VersionNumber use and ordering | open | not checked (`ExtAdd.group` keeps the number) |
| 25.17 | tag UNIVERSAL 16 | mechanized | `Ty.universalTag?`, `tagsOf` |
| 25.18–25.20 | sequence value notation | notation | `Val.seq` (components in the type's order, `SeqShape`) |
| 26.1 | SequenceOfType grammar | notation | `Ty.sequenceOf` (the NamedType identifier is dropped) |
| 26.2 | tag UNIVERSAL 16 | mechanized | `Ty.universalTag?` |
| 26.3–26.12 | sequence-of value notation, XML forms, Table 5 | notation | `Val.seqOf`; element values: `sem` (`.sequenceOf`) |
| 27.1 | SetType grammar | notation | `Ty.set` |
| 27.2 | COMPONENTS OF a set type | mechanized | `expand`, `ComponentsOk` (`.set`) |
| 27.3 | distinct tags; additions in canonical order | mechanized | `TagsOk` (`.set`), `Tag.lt`, `conceptual`; additions without a single tag (untagged CHOICE, open type) are not ordered |
| 27.4 | 25.3 and 25.8–25.14 apply to SET | mechanized | `autoSeq`, `entryTags`, `SeqShape` (25.15 for SEQUENCE only), `NamesOk`, `ComponentsOk` on `.set` |
| 27.5 | tag UNIVERSAL 17 | mechanized | `Ty.universalTag?` |
| 27.6 | order of set values not significant | mechanized | `Val.seq` keeps the type's order (`SeqShape`) |
| 27.7–27.9 | set value notation | notation | `Val.seq` |
| 28.1 | SetOfType grammar | notation | `Ty.setOf` |
| 28.2 | tag UNIVERSAL 17 | mechanized | `Ty.universalTag?` |
| 28.3 | set-of value notation | notation | `Val.setOf`; order not significant: `eqv` (`.setOf`, permutation) |
| 28.4–28.5 | which SetOfValue alternative | notation | `Val.setOf` |
| 29.1 | ChoiceType grammar | notation | `Ty.choice`, `Alt`, `AltAdd`, `choiceAlts` |
| 29.2 | when automatic tagging is selected | mechanized | `autoChoice` |
| 29.3 | distinct alternative tags | mechanized | `TagsOk` (`.choice`), `altTags`, `conceptual` |
| 29.4 | additions untagged under automatic tagging | mechanized | `AutoAdditionsOk` |
| 29.5 | replacement tags for alternatives | mechanized | `altTags`, `autoNumber` |
| 29.6 | VersionNumber restrictions | open | not checked, as 25.16 |
| 29.7 | addition tags canonically increasing | mechanized | `TagsOk` (`.choice`, second conjunct), `Tag.lt`; additions without a single tag are not ordered |
| 29.8 | a CHOICE's values have different tags | mechanized | `tagsOf` (`.choice`), `choiceVSet` |
| 29.9 | all tags of an untagged CHOICE count | mechanized | `tagsOf`, `TagsOk`; `Tests/Tags.lean` (example 1) |
| 29.10 | distinct alternative identifiers | mechanized | `NamesOk` |
| 29.11–29.12 | choice value notation | notation | `Val.choice`; values: `choiceVSet` |
| 30.1 | selection names a CHOICE alternative | mechanized | `Ty.selection`, `RefsOk`, `builtin` |
| 30.2 | parent's constraint is ignored | mechanized | `builtin` (drops `.constrained`) |
| 30.3 | identifier kept when used as NamedType | notation | `Ty.selection` |
| 30.4 | denotes the selected alternative's type | mechanized | `sem`, `tagsOf`, `eqv` (`.selection`) |
| 30.5 | selection value notation | notation | — |
| 31.1.1 | prefixed type isomorphic, new tag | mechanized | `sem` and `eqv` pass through `.tagged`; `tagsOf` |
| 31.1.2 | TaggedType or EncodingPrefixedType | notation | `Ty.tagged`; EncodingPrefixedType is not represented |
| 31.1.3 | purpose of tagging | n/a | — |
| 31.1.4 | encoding instructions don't affect values | notation | encoding prefixes are dropped at parsing; `Ty` has no constructor for them |
| 31.1.5 | PrefixedType grammar | notation | `Ty.tagged` |
| 31.1.6 | prefixed value notation | notation | — |
| 31.2.1 | TaggedType grammar | notation | `Ty.tagged`, `Tag`, `TagClass`, `TagKind` |
| 31.2.2 | encodingreference TAG | notation | — |
| 31.2.3 | ClassNumber DefinedValue non-negative integer | notation | `Tag.num : Nat` |
| 31.2.4 | the new tag's class and number | mechanized | `tagsOf` (`.tagged`), `TagClass.context` |
| 31.2.5 | UNIVERSAL only for X.680's types | mechanized | `UniversalTagOk` |
| 31.2.6 | implicit or explicit tagging | mechanized | `TagKind`, `isExplicit` |
| 31.2.7 | when tagging is explicit | mechanized | `isExplicit`, `untaggedChoiceOrOpen` (with untagged DummyReference), `hasTag`; `Tests/Tags.lean` |
| 31.2.8 | context-specific tags otherwise unrestricted | n/a | — |
| 31.2.9 | no IMPLICIT on untagged CHOICE/open type/DummyReference | mechanized | `TagsOk` (`.tagged _ .implicit`), `untaggedChoiceOrOpen` |
| 31.3.1 | EncodingPrefixedType grammar | notation | not represented in `Ty` |
| 31.3.2 | EncodingInstruction defined by the referenced standard | n/a | — |
| 31.3.3 | empty EncodingReference uses the module default | notation | — |
| 31.3.4 | restrictions belong to other documents | n/a | — |
| 32.1 | ObjectIdentifierType | notation | `Ty.objectIdentifier` |
| 32.2 | tag UNIVERSAL 6 | mechanized | `Ty.universalTag?` |
| 32.3–32.9 | OID value notation, DefinedValue, NameForm | notation | `Val.oid` (the arcs after resolution) |
| 32.10 | flexibility of arc identifiers | n/a | — |
| 32.11 | semantics by X.660 (at least two arcs) | mechanized | `OidWf`, `sem` (`.objectIdentifier`) |
| 32.12–32.13 | significant part, DefinedValue prefix | notation | `Val.oid` |
| 33.1 | RelativeOIDType | notation | `Ty.relativeOid` |
| 33.2 | tag UNIVERSAL 13 | mechanized | `Ty.universalTag?` |
| 33.3–33.5 | relative OID value notation | notation | `Val.oid`; `sem` (`.relativeOid`, one or more arcs) |
| 33.6 | starting node of a relative OID | n/a | known to the application, not part of the value |
| 34.1 | IRIType | notation | `Ty.oidIri` |
| 34.2 | tag UNIVERSAL 35 | mechanized | `Ty.universalTag?` |
| 34.3 | OID-IRI value: sequence of arc labels | partial | `Val.iri`, `sem` (`.oidIri`, non-empty); labels are any strings: 12.26, 12.27 (X.660 7.5) not checked |
| 34.4–34.5 | arcs identified in the OID tree | n/a | depends on X.660 registrations; no registry is modelled |
| 35.1 | RelativeIRIType | notation | `Ty.relativeOidIri` |
| 35.2 | tag UNIVERSAL 36 | mechanized | `Ty.universalTag?` |
| 35.3 | relative OID-IRI value notation | partial | `Val.iri`, `sem` (`.relativeOidIri`, non-empty); labels not checked, as 34.3 |
| 35.4 | starting node of a relative OID-IRI | n/a | known to the application, not part of the value |
| 36.1 | EmbeddedPDVType | notation | `Ty.embeddedPdv` |
| 36.2 | tag UNIVERSAL 11 | mechanized | `Ty.universalTag?` |
| 36.3–36.5 | values; associated type | mechanized | `embeddedPdvAssoc`, `pdvLike`, `identificationAlts`, `assocModule`; `sem`, `eqv`, `elem` (`.embeddedPdv`), `innerTarget` |
| 36.6–36.7 | OSI-only alternatives | n/a | — |
| 36.8 | embedded-pdv value notation | notation | `Val.seq` of `embeddedPdvAssoc` |
| 37.1 | ExternalType | notation | `Ty.external` |
| 37.2 | tag UNIVERSAL 8 | mechanized | `Ty.universalTag?` |
| 37.3 | values, optional object descriptor | partial | `externalAssoc`; c) "not present unless a comment permits" is not modelled: the descriptor is always allowed |
| 37.4–37.5 | associated type defines the values | mechanized | `externalAssoc`; `sem`, `eqv`, `elem` (`.external`), `innerTarget`; X680-6 |
| 37.6 | 36.6, 36.7 apply | n/a | — |
| 37.7 | external value notation | notation | `Val.seq` of `externalAssoc`; NOTE: X680-6 |

### X.680 clauses 38–end and annexes

| Clause | Subject | Status | Where |
|---|---|---|---|
| 38.1.1 | TimeType notation | notation | `Ty.time` |
| 38.1.2 | TIME tag UNIVERSAL 14 | mechanized | `Ty.universalTag?` |
| 38.1.3 | TIME value notation (tstring) | notation | `Notation.parse`, `TimeV.Notates` |
| 38.2.1, Table 6 | time properties, settings, which abstract values exist | mechanized | `TimeV`, `TimeV.props`, `TimeV.Wf`, `PointV.sameShape`, `TimeOfDayV.Wf` (±15 h); X680-2, X680-14; Tests/Time.lean (G.3) |
| 38.2.2 | midnight 00:00 and 24:00 are distinct values | mechanized | `TimeOfDayV.midnight`, `TimeOfDayV.Wf`, `PointV.key` (NOTE 1); Tests/Time.lean |
| 38.2.3 | duration values; zero elements; weeks alone | mechanized | `DurationV.norm`, `timeEqv`, `DurationV.Wf`; X680-17 |
| 38.2.4 | durations ordered only within one element | mechanized | `DurationV.between` (orders the least significant element only) |
| 38.3.1–38.3.2 | notation fixed by settings; TimeValue | notation | `Notation.parse`, `TimeV.Notates` |
| 38.3.3, Table 7 | notation of time components | notation | `Notation.date`, `Notation.timeOfDay`, `Notation.zone`, `Notation.interval` |
| 38.3.4–38.3.5 | tstring contents; component order | notation | `Notation.parse`; NOTE 1's variants are equal after `TimeV.norm` |
| 38.3.6–38.3.6.13 | duration notation | notation | `Notation.duration`, `Notation.designations`, `Notation.designationNumber`, `Notation.ordered`; Tests/Time.lean |
| 38.3.6.14 | accuracy distinguishes durations | mechanized | `DurationV.norm`, `timeEqv`; Tests/Time.lean (EXAMPLES 1, 2) |
| 38.4 | useful time types (introduction) | n/a | |
| 38.4.1–38.4.4 | DATE, TIME-OF-DAY, DATE-TIME, DURATION | mechanized | `dateSettings`, `timeOfDaySettings`, `dateTimeSettings`, `durationSettings`, `timeVSet`, `sem`, `Ty.universalTag?` (31–34); Tests/Time.lean |
| 38.4.4.1 | inner subtyping of a duration subtype | mechanized | `ESet.byDuration`, `elem` (`.withComponents`), `innerTarget`, `ElemOk` (Table 12 NOTE) |
| 38.4.4.2–38.4.4.3 | DURATION-EQUIVALENT | mechanized | `durationEquivComps`, `DurationV.equiv`; X680-17; Tests/Time.lean |
| 38.4.5 | value notation of useful time types | notation | |
| 39 | a cell is an abstract character; notations a)–c) | mechanized | `Val.chars`, `Val.regChars`, `RegChar` (X680-1); the notations a)–c) are notation |
| 40.1 | CharacterStringType | notation | `Ty.restricted`, `Ty.characterString` |
| 40.2 | tags of character string types | mechanized | `Ty.universalTag?` |
| 40.3 | CharacterStringValue | notation | |
| 41, Table 8 | restricted string types and their characters | mechanized | `StrType`, `StrType.chars`, `StrType.regAllows`, `teletexEntries`, `videotexEntries`, `register`, `restrictedVSet`; X680-1, X680-19, X680-20, X680-22; Tests/Strings.lean |
| 41.1 | names, tags, synonyms (T61String, ISO646String) | mechanized | `StrType` (no constructor for the synonyms), `Ty.universalTag?` |
| 41.2, Table 9 | NumericString characters | mechanized | `numericChars` |
| 41.3 | NumericString character abstract syntax identifiers | n/a | identifiers only (listed again in Annex D) |
| 41.4, Table 10 | PrintableString characters | mechanized | `printableChars` |
| 41.5 | PrintableString character abstract syntax identifiers | n/a | as 41.3 |
| 41.6 | UniversalString: all ISO/IEC 10646 characters | mechanized | `universalChars`, `maxCodePoint`; X680-4 |
| 41.7 | ISO/IEC 10646 conformance requirements | n/a | |
| 41.8 | cstring, CharacterStringList, Quadruple, Tuple | notation | |
| 41.9–41.10 | XML value notation, escapes | notation | |
| 41.11–41.14 | DefinedValue, Quadruple and Tuple rules | notation | X680-4 (the Quadruple's 31-bit space) |
| 41.15 | BMPString | mechanized | `bmpChars`, `Ty.universalTag?` (30) |
| 41.16 | UTF8String has UniversalString's values | mechanized | `StrType.chars` (`.utf8`), `Ty.universalTag?` (12) |
| 42, 42.1–42.1.6 | ASN1-CHARACTER-MODULE: named characters, collections, Level1–3, Unicode categories | open | not transcribed: a module importing "BasicLatin", "Level1", "Lu"… does not resolve, and `\N{…}` (A.2.4) cannot name them |
| 42.1.7 | module END | notation | |
| 42.1.8 | user-defined equivalent of BasicLatin | n/a | an example of user notation |
| 42.2–42.3 | how character and collection names are formed | notation | |
| 43.1 | types with a canonical character order | mechanized | `StrType.knownOrder`, `Val.le` |
| 43.2 | a character is a cell, for ordering | n/a | definition |
| 43.3 | order by 32-bit code point | mechanized | `Val.le` (`.chars [a]`) |
| 43.4 | writing range endpoints | notation | |
| 43.5–43.8 | NumericString, PrintableString, VisibleString, IA5String orders | mechanized | `Val.le` (each listed order is the code-point order) |
| 44, 44.1 | CHARACTER STRING notation | notation | `Ty.characterString` |
| 44.2 | tag UNIVERSAL 29 | mechanized | `Ty.universalTag?` |
| 44.3–44.5 | values; associated type | mechanized | `characterStringAssoc`, `pdvLike`, `sem` (`.characterString`), `eqv`, `innerTarget` |
| 44.6 | 36.6, 36.7 (OSI usage of the alternatives) | n/a | usage in an OSI environment; does not restrict the values |
| 44.7 | value notation; string-value is an encoding | notation | `Val.seq`; string-value is any OCTET STRING value |
| 44.8 | pointer to example G.2.8 | n/a | |
| 45.1 | UsefulType notation | notation | `Ty.generalizedTime`, `Ty.utcTime`, `Ty.objectDescriptor` |
| 45.2 | tags of the useful types | mechanized | `Ty.universalTag?` |
| 46.1 | GeneralizedTime | notation | `Ty.generalizedTime` |
| 46.2–46.4 | VisibleStrings in ISO 8601 basic format; tag 24 | mechanized | `formatVSet`, `Notation.generalizedTime`, `Notation.generalizedTimeOk`, `Ty.universalTag?`; X680-7; Tests/Time.lean (46.3 EXAMPLES) |
| 46.5 | value notation | notation | |
| 47.1 | UTCTime | notation | `Ty.utcTime` |
| 47.2–47.4 | YYMMDDhhmm[ss] with Z or ±hhmm; tag 23 | mechanized | `formatVSet`, `Notation.utcTime`, `Notation.utcTimeOk`, `Ty.universalTag?`; X680-15; Tests/Time.lean (47.3 EXAMPLES) |
| 47.5 | value notation | notation | |
| 48.1 | ObjectDescriptor | notation | `Ty.objectDescriptor` |
| 48.2 | purpose of the type | n/a | |
| 48.3–48.4 | GraphicString values; tag 7 | mechanized | `sem` (`.objectDescriptor` is `restrictedVSet .graphic`), `Ty.universalTag?`; Tests/Strings.lean |
| 48.5 | value notation | notation | |
| 49.1 | ConstrainedType | notation | `Ty.constrained`; its values are `cons` |
| 49.2 | constraint after SET OF / SEQUENCE OF binds to the element | notation | |
| 49.3 | constraint after a selection type is ignored | mechanized | `sem` (`.selection` reaches the alternative through `builtin`, which drops the CHOICE's constraint) |
| 49.4 | constraint after a prefixed type | mechanized | `sem` (`.tagged` does not change values) |
| 49.5 | TypeWithConstraint | notation | `Ty.constrained` on `Ty.sequenceOf`/`Ty.setOf` |
| 49.6 | Constraint, ExceptionSpec | notation | the ExceptionSpec is not kept (`Constraint.mk`), so its "shall only be present if" rule is not checked |
| 49.7 | governor is the parent; at least one element | mechanized | `cons`, `NonEmpty` |
| 50.1 | ElementSetSpecs grammar | notation | `Constraint.mk`, `ElemSet` |
| 50.2 | set arithmetic | mechanized | `eset`, `ESet.union`, `ESet.inter`, `ESet.except`, `ESet.allExcept` |
| 50.3 | no ALL EXCEPT over objects | mechanized | `OElems` has no such constructor |
| 50.4 | extensibility of element sets | mechanized | `ESet` (`ext`), `VSet.ofSpecs`; X680-11; Tests/Constraints.lean |
| 50.5 | root and extension additions by set arithmetic | mechanized | `ESet` (`r`, `a`), `VSet.ofSpecs`; Tests/Constraints.lean (I.4) |
| 50.6 | Elements alternatives | notation | `ElemSet.elem`, `OElems` |
| 50.7 | non-extensible governor: its values only | partial | arithmetic is over the governor's values (`cons`, `eset`'s `g`); single values must be values of the parent (`ElemOk`), but range endpoints are not required to be (only the values in the range are) |
| 50.8 | extensible governor: its root only | mechanized | `cons` passes `parent.root`; `ElemOk` checks single values and ranges against the root |
| 50.9 | object set arithmetic and extensibility | mechanized | `oelems`, `OSet.union`, `OSet.inter`, `OSet.except`, `OSet.ofSpecs`; X681-2 |
| 50.10 | value notation names parent values | partial | as 50.7 |
| 50.11 | serial constraint on an extensible parent | mechanized | `cons` (the parent's root, not its constraint extensibility), `ElemOk`; NOTE: `VSet.keepExt` for general constraints |
| 51.1, Table 11, Table 12 | which subtype elements apply to which types | mechanized | `Row`, `rowOf`, `Row.allows`, `ElemOk`; X680-24; Tests/Applicability.lean |
| Table 11 note a) | value range only in a PermittedAlphabet, 7 types | mechanized | `StrType.knownOrder`, `ElemOk` (`inPA`) |
| Table 11 note b) | relative OIDs share the governor's starting node | open | a relative OID value (`Val.oid`) has no starting node |
| Table 12 NOTE | inner subtyping only on duration subtypes | mechanized | `ElemOk` (`.withComponents`, `durationSettings`) |
| 51.2.1 | SingleValue is a value of the parent | mechanized | `Elem.single`, `ElemOk` |
| 51.2.2 | selects that value | mechanized | `elem` (`.single`: `evalVal`, then `eqv` in the parent type) |
| 51.3.1 | ContainedSubtype, INCLUDES with NULL | notation | `Elem.contained` |
| 51.3.2 | parent root ∩ the type's root; same built-in type | mechanized | `elem` (`.contained`), `ElemOk` (same `rowOf`) |
| 51.3.3 | the type's extensibility is not inherited | mechanized | `elem` (`.contained` is `ESet.fixed`); Tests/Constraints.lean (I.4.4) |
| 51.4.1 | ValueRange notation | notation | `Elem.range`, `Bound` |
| 51.4.2 | where ranges apply; values in the root; REAL order | mechanized | `InRange`, `Val.le`, `RealVal.key`, `ElemOk`; Tests/Applicability.lean |
| 51.4.3–51.4.4 | open endpoints, MIN, MAX; size-1 endpoints in an alphabet | mechanized | `InRange`, `EvalBound`, `SingleChar` |
| 51.5.1 | SizeConstraint notation | notation | `Elem.size` |
| 51.5.2 | where SIZE applies | mechanized | `Row.allows` |
| 51.5.3 | a subtype constraint on INTEGER (0..MAX) | mechanized | `sizeParent`, `ElemOk` (`Constraint.isSubtype`, `ConsOk` on `.integer []`) |
| 51.5.4 | unit of measure | partial | `Val.size?` (bits, octets, characters including `RegChar` cells, elements); CHARACTER STRING has no size (X680-27); X680-8 for extensibility |
| 51.6.1 | TypeConstraint notation | notation | `Elem.typeC` |
| 51.6.2 | restricts an open type to a type | mechanized | `elem` (`.typeC`), `Row.allows` (`.openType`) |
| 51.7.1 | PermittedAlphabet notation | notation | `Elem.from_` |
| 51.7.2 | a sub-alphabet of the parent; restricted strings only | mechanized | `elem` (`.from_`), `Row.allows` |
| 51.7.3 | four element kinds; characters of the selected values | mechanized | `ESet.byAlphabet`, `ElemOk` (`inPA`, `Constraint.isSubtype`) |
| 51.7.4 | extensible permitted alphabet | mechanized | `ESet.byAlphabet` (`S.ext`, `S.all`); X680-8 |
| 51.8.1 | InnerTypeConstraints notation | notation | `Elem.withComponent`, `Elem.withComponents` |
| 51.8.2 | values satisfying all inner constraints | mechanized | `ESet.byElems`, `ESet.byComponents`, `ESet.byAlternatives`, `Row.allows` |
| 51.8.3 | GeneralConstraint inside only in first alternatives | open | not checked |
| 51.8.4 | WITH COMPONENT | mechanized | `ESet.byElems`; X680-8 |
| 51.8.5 | Full/PartialSpecification notation | notation | `Elem.withComponents` (`isPartial`) |
| 51.8.6 | named components, in order, at most once | mechanized | `ElemOk` (`Nodup`, `structComps`), `PresenceOk`; Tests/Applicability.lean |
| 51.8.7 | full specification implies ABSENT | mechanized | `SeqPresenceOk`, `AltPresenceOk` |
| 51.8.8 | ComponentConstraint notation | notation | `PresenceC` |
| 51.8.9 | value constraint on a component | mechanized | `ValueOk`; an omitted DEFAULT component through its default value (`DefaultIs`, 25.12) |
| 51.8.10 | PresenceConstraint notation | notation | `PresenceC` |
| 51.8.10.1 | PRESENT/ABSENT/OPTIONAL on OPTIONAL components | mechanized | `SeqPresenceOk`, `PresenceOk`; Tests/Applicability.lean |
| 51.8.10.2 | choice alternatives; at most one PRESENT | mechanized | `AltPresenceOk`, `PresenceOk`; Tests/Applicability.lean |
| 51.8.10.3 | empty presence constraint | mechanized | `SeqPresenceOk`, `AltPresenceOk` |
| 51.9.1 | PatternConstraint notation | mechanized | `Elem.pattern`; read from text by `Parse.parseRegex` (`Tests/Regex.lean`); a value reference after PATTERN is not read |
| 51.9.2 | the whole value matches the whole expression | mechanized | `elem` (`.pattern`), `Regex.Accepts`, `Val.patternChars`; X680-21 |
| 51.10.1–51.10.2 | PropertySettings notation | notation | `Elem.settings` |
| 51.10.3–51.10.4 | property and setting names | mechanized | `settingsOk`, `settingOk`, `propertyNames`; Tests/Time.lean |
| 51.10.5 | selection by settings | mechanized | `elem` (`.settings`), `TimeV.satisfies`; X680-13; Tests/Time.lean |
| 51.10.6, Table 13 | names prohibited with a Basic setting | mechanized | `prohibitedWith`, `settingsOk`; Tests/Applicability.lean |
| 51.11.1 | DurationRange notation | notation | `Elem.range` |
| 51.11.2–51.11.3 | duration endpoints | mechanized | `timeRangeOk`, `ElemOk`; Tests/Applicability.lean |
| 51.11.4 | durations selected | mechanized | `TimeInRange`, `DurationV.between`; Tests/Time.lean (EXAMPLE) |
| 51.12.1 | TimePointRange notation | notation | `Elem.range` |
| 51.12.2–51.12.4 | time point endpoints | mechanized | `timeRangeOk`, `PointV.sameShape`; Tests/Applicability.lean |
| 51.12.5 | time points selected | mechanized | `TimeInRange`, `PointV.between`, `PointV.key`; Tests/Time.lean |
| 51.13.1 | RecurrenceRange notation | notation | `Elem.range` |
| 51.13.2 | integer endpoints | mechanized | `timeRangeOk` |
| 51.13.3–51.13.4 | Unlimited as MAX; selection by recurrences | mechanized | `RecAbove`, `RecBelow`, `TimeInRange`; X680-16 |
| 52.1 | ellipsis: additions expected, not a decoding error | n/a | a requirement on decoders; extensibility is `VSet.ext`, `Extensible` |
| 52.2 | extension marker with exception identifier | n/a | recommendation |
| 52.3 | set arithmetic of extensible sets | mechanized | `ESet`, `OSet` (50) |
| 52.4 | contained subtype does not inherit | mechanized | `elem` (`.contained`), `VSet.ofSpecs`; Tests/Constraints.lean |
| 52.5 | a further constraint does not inherit | mechanized | `cons`; Tests/Constraints.lean (I.4.2 `B2`) |
| 52.6 | absent components; the type stays extensible | mechanized | `SeqPresenceOk`, `AltPresenceOk`; `structExt`, `VSet.keepExt` in `cons` (X680-26); `Tests/Extension.lean` |
| 52.7–52.7.4 | conceptually-added element in tag checks | mechanized | `TagsOk`, `conceptual`, `CTag.clash`, `carriesConceptual` (a nested untagged extensible CHOICE) |
| 52.8.1–52.8.4 | examples of 52.7 | n/a | `Tests/Extension.lean` checks 52.8.1 (legal), 52.8.2 and 52.8.3 (illegal) |
| 53.1–53.3 | purpose of exception identifiers | n/a | |
| 53.4 | ExceptionSpec notation | notation | not kept in `Constraint`; that its defined value names a value (14.1) is `ExceptionRefsOk`, over `Module.exceptionRefs` |
| 53.5–53.6 | which exception identifier a type has | open | exception identifiers are not kept (`Constraint.mk`); they do not change value sets |
| 54.1 | EncodingControlSections | notation | not represented in `Module` |
| 54.2–54.3 | distinct encoding references; not TAG | notation | not represented in `Module` |
| 54.4–54.5 | instructions defined by other standards | n/a | |
| Annex A.1, A.1.1 | what a regular expression is | n/a | |
| Annex A.1.2 | a character matches itself | mechanized | `Regex.cls`, `Matches.cls` |
| Annex A.1.3 | concatenation | mechanized | `Regex.cat`, `Matches.cat` |
| Annex A.2.1 | list of metacharacters; white space in them | mechanized | `Regex` is the expression after parsing; `Parse.parseRegex` reads every metacharacter sequence |
| Annex A.2.2 | bracketed lists, ranges, negation | mechanized | `Regex.cls` (`negated`, ranges by code point, 43.3), `Regex.clsMem`; the bracket syntax is notation |
| Annex A.2.3 | {g,p,r,c} | notation | parses to a one-character `Regex.cls` |
| Annex A.2.4 | \N{valuereference}, \N{typereference}, categories | partial | a `Regex.cls` after parsing; `Parse.charSetByName` knows the clause 41 string types and `BasicLatin`, nothing else (clause 42's module and Unicode categories are not defined); X680-29 |
| Annex A.2.5 | "." | mechanized | `Regex.cls` negated `newlineChars` |
| Annex A.2.6 | \d, \t, \w | mechanized | `digitChars`, `wordChars` |
| Annex A.2.7 | \r, \n, \s, \b | mechanized | `newlineChars`, `whiteSpaceChars`, `Regex.boundary`, `isWordAt`; X680-5 |
| Annex A.2.8 | quoting with "\", doubled quotation mark | notation | |
| Annex A.2.9 | alternation | mechanized | `Regex.alt` |
| Annex A.2.10 | repetition operators | mechanized | `Regex.rep`, `Times` |
| Annex A.2.11 | precedence | notation | |
| Annex A.2.12 | numbered subexpressions; no "()" | notation | |
| Annex B.1 | defined time types: general | n/a | |
| Annex B.2 | DefinedTimeTypes module | open | not transcribed; each type is expressible as `Ty.constrained .time` with `Elem.settings` |
| Annex C (intro) | purpose of the annex | n/a | |
| Annex C.1.1–C.1.8 | tutorial introduction | n/a | |
| Annex C.2.1 | types as disjoint containers of values | partial | not the Lean's model: a `Val` belongs to no type, value notation is evaluated without its governing type (`evalVal`), and the governing type then selects the value by membership (`sem … .all`) or equality (`eqv`); the value mapping is in effect the identity on `Val` |
| Annex C.2.2–C.2.4 | mappings: equivalence, one-to-one, usable across types | partial | the identity on `Val` has these properties, but it relates values of any two types whose values coincide, beyond the mappings C.4–C.5 define (see C.3, C.5.1) |
| Annex C.3.1–C.3.3 | identical type definitions (normal form) | open | no normal form of `Ty`; so value references are accepted between types that are not identical type definitions when their `Val`s coincide, e.g. C.7.4's `C` and `C1`, or SEQUENCEs differing only in a component's tag (C.4.2 NOTE) |
| Annex C.4.1 | mappings between identical type definitions | partial | the identity relates corresponding values, except for SET types whose components C.3.2.4 reorders: a `Val.seq` lists components in its type's order, so `eqv` (`SeqEqv`, by name) relates C.7.3's `B` and "B1" values but direct membership (`ValuesOk`, `ComponentsOk`, `ElemOk`) does not |
| Annex C.4.2 | tagging | mechanized | tags are not part of `Val`; `sem` (`.tagged`) |
| Annex C.4.3 | subtyping and element sets | mechanized | `cons` selects the parent's own `Val`s |
| Annex C.4.4, C.5.1–C.5.3 | character string groups A and B | partial | group A shares `Val.chars` and group B uses `Val.regChars`, so no mapping across the groups; but the four group B types share `RegChar` cells, so a TeletexString value is accepted as a GeneralString value, which C.5.1 forbids |
| Annex C.4.5 | integer types with different named numbers | mechanized | `Val.int`; named numbers do not change values (`sem` `.integer`) |
| Annex C.4.6 | bit string types with different named bits | mechanized | `Val.bits`, `eqv` (22.7, X680-3) |
| Annex C.5.4–C.5.8 | group A mapped through UniversalString | mechanized | `Val.chars` (code points), `StrType.chars`; UTF8String and UniversalString both `universalChars`, `bmpChars` ⊆ `universalChars` |
| Annex C.6, C.6.1 | a Value must identify a value of its governing type | partial | checked for value assignments (`ValuesOk`), DEFAULT values (`ComponentsOk`, `FieldDefaultsOk`) and single values in constraints (`ElemOk`, against all values, not the root: 50.8); a value reference also names a value of a type that maps to the governor by built-in type (`RefMaps`, `ValMaps`), there and at range ends; not for actual parameters (C.6.3); C.6.1's "Z1" is accepted and "Z2" rejected, as stated |
| Annex C.6.2 | a Type in set arithmetic: the governor's root values mapped from its root, at least one | partial | `elem` (`.contained`: parent root ∩ the type's root); that this part is non-empty is not checked (`ElemOk` compares `rowOf` only), so C.6.2's illegal `Z2 ::= V (Y \| 24)` is accepted |
| Annex C.6.3 | actual value parameter maps into the dummy's governor | open | `Scope.bound`/`resolveVal` ignore the governor; no validity rule |
| Annex C.6.4 | a Type as actual for a value set dummy | partial | `resolveTy` uses the actual type itself, not the governor's values mapped from it (same `Val`s when the requirement holds, but the actual's tags); the requirement is not checked |
| Annex C.6.5 | dummy governor must accept every use | open | not checked |
| Annex C.7.1–C.7.7 | examples of C.3, C.4 | n/a | no Tests file; C.7.5, C.7.6 and C.7.7 come out as stated (`evalVal`, `eqv`, `ComponentsOk`); C.7.3 and C.7.4 do not (see C.3, C.4.1) |
| Annex D.1 | object identifiers assigned in X.680 | n/a | records identifiers |
| Annex D.2 | ASN1-Object-Identifier-Module | open | not transcribed |
| Annex E.1–E.2, Table E.1 | encoding references | n/a | encoding instructions are defined by other standards; `Module` has none |
| Annex F | OID tree arcs and OID-IRIs | informative | |
| Annex G | examples and hints | informative | Tests/Time.lean checks G.3 (ledger X680-18 for two misprints) |
| Annex H | character strings tutorial | informative | |
| Annex I | type extension tutorial | informative | Tests/Constraints.lean checks I.4 (X680-9) |
| Annex J | ISO 8601 and TIME tutorial | informative | J.2.2's proleptic calendar is `isLeap`, `monthDays` |
| Annex K | time properties from value notation | informative | `Notation.parse` with `TimeV.props` does this; not tested against K |
| Annex L | summary of the notation | informative | |

## X.681, X.682 and X.683

### X.681

| Clause | Subject | Status | Where |
|---|---|---|---|
| 1 | Scope | n/a | |
| 2, 2.1 | Normative references | n/a | |
| 3.1–3.4.22 | Definitions | n/a | |
| 4 | Abbreviations | n/a | |
| 5 | Convention | n/a | |
| 6.1–6.4.1 | Where the new notations plug into X.680 | notation | `Module.classes`, `Module.objects`, `Module.objectSets`, `Ty.classField`, `Ty.instanceOf`, `Ty.fromObjects`, `Val.fromObject`, `OElems` |
| 7–7.10 | Lexical items: reference kinds, word, keywords | notation | |
| 8.1 | DefinedObjectClass, DefinedObject, DefinedObjectSet | notation | `ClassRef.ref`, `Obj.ref`, `ObjSet.ref` |
| 8.2 | Objects are of the governing class (same class reference) | open | not checked; `evalObj`/`evalObjSet` take the governor's fields without checking the object's class |
| 8.3 | References within the module, imports, external references | mechanized | `resolveIn`, `Env.resolveWith`, `Env.resolveExtWith` (the "different module" condition is not checked) |
| 8.4 | UsefulObjectClassReference | mechanized | `ClassRef.typeIdentifier`, `ClassRef.abstractSyntax`, `classFields` |
| 9.1 | ObjectClassAssignment | notation | `Module.classes` |
| 9.2 | ObjectClass: reference, definition, parameterized | mechanized | `classFields`, `resolveClass` |
| 9.3 | ObjectClassDefn, WITH SYNTAX | mechanized | `ClassRef.defn` (the SyntaxList is object notation, not kept) |
| 9.4 | FieldSpec alternatives | mechanized | `FieldSpec`; the classes of object and object set fields exist: `FieldClassesOk` |
| 9.5 | Type field; required, OPTIONAL, DEFAULT | partial | `FieldSpec.typeField`, `ObjV.setting` (DEFAULT); a required field's presence (11.5) not checked |
| 9.6 | Fixed-type value field, UNIQUE | mechanized | `FieldSpec.fixedValue`, `uniqueFields`, `ObjV.setting`; the DEFAULT value is of the type: `FieldDefaultsOk`; no DEFAULT with UNIQUE: `ClassSyntaxOk` |
| 9.7 | Identifier field values unambiguous in a set | mechanized | `UniqueOk`: two objects of a set with one value of a UNIQUE field are one object (`ObjV.Same`: the same fields, values that denote one value, types of one built-in type, other settings alike) |
| 9.8 | Variable-type value field | partial | `FieldSpec.varValue`, `TableOk` (type from the linked type field via `cell`); a) for a one-name path: `FieldClassesOk`; longer paths, b) and "link fields are object fields" not checked |
| 9.9 | Fixed-type value set field | partial | `FieldSpec.fixedValueSet`, `ObjV.setting`; DEFAULT being a subtype not checked |
| 9.10 | Variable-type value set field | partial | `FieldSpec.varValueSet`, `TableOk`; a) for a one-name path: `FieldClassesOk`; b) not checked |
| 9.11 | Object field | partial | `FieldSpec.objectField`, `fieldClass`, `cell`; the DEFAULT object's class not checked |
| 9.12 | Object set field | partial | `FieldSpec.objectSetField`, `fieldClass`, `cell`; the DEFAULT set's class not checked |
| 9.13 | PrimitiveFieldName; field names distinct | partial | `FieldSpec.name`; distinctness not checked (`fieldAt` takes the first match) |
| 9.14 | FieldName: path through link fields | mechanized | `fieldAt`, `classAt`; in `C.&f` the path names a field: `ClassRefsOk` |
| 9.15 | Recursive link-field chain needs an optional field | open | not checked |
| 10.1–10.4 | Purpose and place of defined syntax | notation | WITH SYNTAX not kept (`ClassRef.defn`) |
| 10.5–10.10 | SyntaxList grammar, literals, optional-group parsing | notation | `Obj.defn` holds the settings either syntax gives |
| 10.11 | DefinedSyntax gives every mandatory field | open | not checked (as 11.5) |
| 10.12 | Restrictions on SyntaxList and its use | partial | a): `ClassSyntaxOk` (`SynGroupsOk`, decided by the grammar); b)–d) are about writing objects and are notation |
| 11.1 | ObjectAssignment | notation | `Module.objects`; its class exists: `ClassResolves` (`ObjOk`) |
| 11.2 | No recursive object definition or instantiation | open | not checked (a recursive object denotes no object at any fuel) |
| 11.3 | Object alternatives; object is of the class | partial | `evalObj`, `resolveObj` (a–d: `Obj.ref`, `Obj.defn`, `Obj.fromObject`, parameterized); a referenced object exists: `ObjOk`, `ORef.Resolves`; class membership not checked |
| 11.4 | DefaultSyntax vs DefinedSyntax | notation | `Obj.defn` |
| 11.5 | One setting per mandatory field, at most one otherwise | partial | `Obj.defn`, `ObjV.setting`; each mandatory field has a setting: `ObjV.FieldsSet` (`ObjOk`, `ObjSetOk`); at most one setting each, and the field names, not checked |
| 11.6 | DefinedSyntax | notation | `Obj.defn` |
| 11.7 | Setting alternative matches field kind | partial | `Setting`; `TableOk`/`cell` match a setting to its field's kind, but a mismatch is not rejected; the references in settings exist: `ObjV.SettingRefsOk` |
| 11.8–11.9 | Variable-type settings are of the linked type | open | not checked |
| 12.1 | ObjectSetAssignment | notation | `Module.objectSets`; its class exists, and the objects and sets it names: `ObjSetOk` |
| 12.2 | No recursive object set definition or instantiation | open | not checked |
| 12.3 | ObjectSetSpec; non-empty unless "..." | partial | `ObjSet.spec`, `OSet.ofSpecs`, `evalObjSet`; non-emptiness and class not checked |
| 12.4 | Set arithmetic over extensible object sets | mechanized | `OSet.union`, `OSet.inter`, `OSet.except`, `oelems`; object equality X681-2 |
| 12.5 | A referenced extensible set passes on its extensibility | mechanized | `oelems` (`.set`), `evalObjSet` |
| 12.6 | ValueSetFromObjects is not extensible | mechanized | `sem` (`.fromObjects` gives `VSet.plain`) |
| 12.7 | A table-constrained type is not extensible | mechanized | `cons` (`.table`) |
| 12.8 | Inextensible set: only its objects | mechanized | `TableOk` |
| 12.9 | Extensible set: other objects with unused UNIQUE values | mechanized | `TableOk` (`fresh`), X681-3; `Tests/Params.lean` |
| 12.10 | ObjectSetElements | partial | `OElems`, `oelems`; "of the governing class" not checked |
| 13.1–13.4 | Associated table: columns, rows, link expansion | mechanized | `cell`, `fieldAt`, `classAt`, `fieldClass`, `ObjV.setting` |
| 14, 14.1 | ObjectClassFieldType | mechanized | `Ty.classField`, `classFieldOf`, `fieldAt` |
| 14.2 | Type field gives an open type; restrictions a)–d) | partial | `sem` (`.classField`, `.openType`), `tagsOf` (`none`), `CTag.clash` (b): the indeterminate tag clashes with every tag), `isExplicit`, `untaggedChoiceOrOpen` (c)). Missing: a) not checked; d) concerns encoding rules |
| 14.3 | Fixed-type field denotes the field's Type | mechanized | `builtin`, `sem`, `tagsOf`, `eqv`; the SimpleTableConstraint/SingleValue parse preference is notation |
| 14.4 | Variable-type field gives an open type | partial | `sem`, `builtin`; 14.2 a) not checked |
| 14.5 | Not for object or object set fields | mechanized | `sem` gives `VSet.empty`, `builtin` gives none, so `NonEmpty` rejects it |
| 14.6 | ObjectClassFieldValue notation | notation | `Val.open_` |
| 14.7 | Fixed-type field value is a value of its Type | mechanized | `sem` (`.classField` → the field's type) |
| 14.8 | Open type value: any type, any value of it | mechanized | `sem` (`.openType`), `Val.open_`, `eqv` |
| 14.9–14.12 | XML value notation | notation | |
| 15.1–15.3 | The five InformationFromObjects forms | mechanized | `evalVal` (`Val.fromObject`), `sem` (`Ty.fromObjects`), `evalObj` (`Obj.fromObject`), `oelems` (`OElems.fromObjects`), columns via `cell` |
| 15.4–15.5, Table 1 | Which forms are permitted | partial | for InformationFromObjects written as a type: `TypeFromObjectsTableOk`; written as a value or an object set, not checked; that the object set exists: `TypeFromObjectsOk` |
| 15.6 | XML notation of the resulting types | notation | |
| 15.7–15.8 | ValueSetFromObjects ≡ `C.&f` with a simple table constraint | partial | values: `sem` (`.fromObjects`, `cell`, `cons`); tags and built-in type: the fixed-type field's (`objSetClass`, `tagsOf`, `builtin`). Value columns are taken as written (`evalVal`), not up to `eqv` as `TableOk` takes them |
| 15.9 | An initially empty set has objects when used | n/a | run-time requirement on applications |
| 15.10 | ObjectSetFromObjects is the union of the selected sets | mechanized | `oelems` (`.fromObjects`) |
| 15.11 | Object set with variable-type or type field not permitted | open | not checked (Table 1) |
| 15.12 | Empty column gives an empty inextensible set; not in a table constraint | open (X681-4) | `oelems` (`.fromObjects`) keeps the source set's extensibility; the ban in table constraints is not checked |
| 15.13 | No InformationFromObjects from an empty column | open | not checked |
| A.1 | TYPE-IDENTIFIER's purpose | n/a | |
| A.2 | TYPE-IDENTIFIER's fields | mechanized | `typeIdentifierFields` (WITH SYNTAX is notation) |
| A.3 | Available without import | mechanized | `ClassRef.typeIdentifier`, `classFields` (`assocModule`) |
| B.1 | ABSTRACT-SYNTAX's purpose | n/a | |
| B.2 | ABSTRACT-SYNTAX's fields | mechanized | `abstractSyntaxFields` (the meaning of handles-invalid-encodings is for decoders) |
| B.3 | Available without import | mechanized | `ClassRef.abstractSyntax`, `classFields` |
| B.5 | Parameters carried by an abstract syntax | open (X683-1) | — |
| C.1 | INSTANCE OF is for a class defined as TYPE-IDENTIFIER | open | the class is not checked to be TYPE-IDENTIFIER or assigned from it |
| C.2 | InstanceOfType notation | notation | `Ty.instanceOf` |
| C.3, C.5, C.7 | The associated sequence type defines values and subtypes | mechanized | `instanceOfTy`, `builtin`, `sem`, `eqv` |
| C.4 | Tag UNIVERSAL 8 | mechanized | `tagsOf` (`.instanceOf`) |
| C.6 | Associated type read with EXPLICIT TAGS | mechanized | `instanceOfTy` (`[0]` explicit), `VSet.noExt` in `sem` (`.instanceOf`) |
| C.8–C.9 | Value notation | notation | |
| Annex D | Examples | informative | not checked by Tests |
| Annex E | Tutorial on object set extension | informative | E.2 agrees with `TableOk` (X681-3) |
| Annex F | Summary of the notation | informative | |

### X.682

| Clause | Subject | Status | Where |
|---|---|---|---|
| 1 | Scope | n/a | |
| 2, 2.1 | Normative references | n/a | |
| 3.1–3.4.9 | Definitions | n/a | |
| 4 | Abbreviations | n/a | |
| 5 | Convention | n/a | |
| 6.1 | GeneralConstraint as a ConstraintSpec | notation | `Constraint.table`, `Constraint.contents`, `Constraint.userDefined` |
| 7, 7.1 | Additional keywords | notation | |
| 8.1–8.2 | GeneralConstraint alternatives | notation | `Constraint.table`, `Constraint.contents`, `Constraint.userDefined` |
| 9.1 | UserDefinedConstraint and its value set | mechanized | `Constraint.userDefined`, `ESet.userDefined`, `cons`; X682-1 (no restriction) |
| 9.2 | State the constraint in a comment (recommendation) | n/a | |
| 9.3 | UserDefinedConstraintParameter and its governor | notation | parameters not kept (`Constraint.userDefined`) |
| 10.1 | Only on ObjectClassFieldType or INSTANCE OF | mechanized | `TableOnFieldOk`, `TableTarget`; `cons` (`.table`, via `classFieldOf`, and `instanceOfOf` for Annex A) |
| 10.2 | The object set's associated table determines values | mechanized | `cons`, `TableOk`, `cell` |
| 10.3 | TableConstraint notation | notation | `Constraint.table` (`refs = []` for a simple one); its object set exists: `TableRefsOk` |
| 10.4 | Object set governed by the field's class | mechanized | `cons` passes `classFields` of `classFieldOf`'s class to `evalObjSet`; a set of another named class is rejected: `TableClassOk` |
| 10.5–10.6 | Simple table constraint by field kind | mechanized | `TableOk` (`admits`), `cell`; `Tests/Objects.lean` |
| 10.7 | ComponentRelationConstraint, AtNotation | notation | `Constraint.table`, `AtRef` |
| 10.8–10.9 | Identifiers name components of SET/SEQUENCE/CHOICE | mechanized | `AtPathsOk`, `AtWalk`, `Within` (the textually enclosing types); `navigate`, `structComps`, `Val.component` |
| 10.10 | Parent structure for "@" and "@." | mechanized | `AtRef.resolve`, `Frame`, `FrameKind`, `sem` (enclosing values); too many dots resolve to nothing rather than being rejected; `Tests/Objects.lean` |
| 10.11–10.12 | Referencing/referenced components, constraining set/table | mechanized | `TableOk` (`refd`, `rows`) |
| 10.13 | Constrained type: innermost Type with all referenced components | partial | evaluated on the referencing component with the enclosing values (`sem`, `seqVSet`, `Frame`); the "can only be applied" restriction not checked |
| 10.14 | Referenced component not in another alternative | open | not checked (such a component reads as absent, `Val.component`) |
| 10.15 | Same class, value or value set fields, same object set | partial | the referenced component is constrained by the same object set (`AtWalk`, `ObjSet.unwrap`), of the same named class (`TableClassOk`); "value or value set fields" not checked |
| 10.16 | Introduces 10.17–10.21 | n/a | |
| 10.17 | Referencing component absent: satisfied | mechanized | `seqVSet` constrains only the components present |
| 10.18 | A referenced component absent: not satisfied | mechanized | `TableOk` (`∀ r ∈ refd, r.isSome`); `Tests/Objects.lean` |
| 10.19 | Selected rows agree with the referenced components | mechanized | `TableOk` (`selected`, `admits`) |
| 10.20 | Simple table constraint over the selected rows | mechanized | `TableOk`; `Tests/Objects.lean` |
| 10.21 | Exactly one selected row when an identifier field is referenced | open | not checked |
| 11.1 | ContentsConstraint notation | notation | `Constraint.contents` |
| 11.2 | ENCODED BY value is an OBJECT IDENTIFIER | open | not checked |
| 11.3 | Only on OCTET STRING / BIT STRING without named bits; no further constraints | partial | `ConsOk` (`.contents`: the parent is a BIT STRING or OCTET STRING type); named bits and further constraints not checked |
| 11.4 | CONTAINING: values are encodings under the applied rules | partial | `ContentsHook`, `cons` (`.contents`), X682-2; b) via the parent's root, and `NonEmpty`; a) not checked |
| 11.5 | ENCODED BY: the identified procedures | mechanized | `cons` (`.contents`, `none` type), `ContentsHook` |
| 11.6 | CONTAINING … ENCODED BY | partial | as 11.4: `ContentsHook`, `cons`, X682-2; a) not checked |
| A.1 | Purpose of Annex A | n/a | |
| A.2–A.3 | Table constraint on INSTANCE OF (constrained sequence) | mechanized | `instanceOfTable`, `cons` (`.table`, `instanceOfOf`, `ClassRef.from`); A.3: each constraint applies in turn |
| Annex B | Summary of the notation | informative | |

### X.683

| Clause | Subject | Status | Where |
|---|---|---|---|
| 1 | Scope | n/a | |
| 2, 2.1 | Normative references | n/a | |
| 3.1–3.4.9 | Definitions | n/a | |
| 4 | Abbreviations | n/a | |
| 5 | Convention | n/a | |
| 6.1–6.3 | Where the parameterized notations plug in | notation | `ParamAssign`, `Ty.paramRef`, `Val.ref`, `ClassRef.ref`, `Obj.ref`, `ObjSet.ref` |
| 7 | Lexical items | notation | |
| 8.1 | The six parameterized assignments | mechanized | `ParamAssign`, `Module.params`, `resolveIn` |
| 8.2 | Their syntax | notation | `ParamAssign` |
| 8.3 | ParameterList, Parameter, governors | partial | `Param`, `ParamGov`; governors exist: `ParamGovsOk`; a)–c) and the DummyGovernor rule not checked; a value-set dummy with a DummyGovernor does not resolve (`resolveTy` takes only a `ParamGov.type` governor) |
| 8.4 | Scope of a dummy; it hides other references | mechanized | `Scope`, `Scope.bound`, `bindParams`, `resolveIn`; `Tests/Params.lean` |
| 8.5 | Consistent use of a dummy | partial | `Module.ValidAt` (field `params`), `ArgFits`, `bindParams`: a body is valid when some actual parameters of the kinds the governors allow make it so, and a use of the wrong kind resolves to nothing (`resolveIn`); `Tests/Sites.lean`. Missing: the values and objects a body writes (only its types are checked) |
| 8.6 | Each dummy used; no self-referencing value/value set/object/object set assignments | partial | each dummy used: notation, decided on the lexical items of the assignment (`unusedDummies`); self-reference not checked |
| 8.7 | Recursive path: actual parameters only dummy or dummy-free | open | not checked |
| 8.8 | Circular definitions need OPTIONAL or a non-circular choice | partial | `NonEmpty` (for instances reached from `Module.types`); a parameterized class not checked |
| 8.9–8.11 | Governor restrictions; right side not solely a dummy | partial | 8.10 for parameterized types: `ParamAssign.NotOnlyDummy`; 8.9, 8.11 not checked |
| 8.12–8.13 | Actual value or value set compatible with the governor | open | not checked (X.680 Annex C) |
| 9.1 | ParameterizedReference in Exports/Imports | notation | `Module.imports` |
| 9.2 | Parameterized\<X\> references | mechanized | `Ty.paramRef`, `Val.ref`, `ClassRef.ref`, `Obj.ref`, `ObjSet.ref` (with `args`), `resolveIn`, `bindParams`; types given as actual parameters: `Occurs.paramArg`; objects, object sets and values given exist: `ArgsOk` |
| 9.3 | Name assigned by a ParameterizedAssignment | partial | `resolveIn` looks only in `Module.params` when there are arguments; `RefsOk` checks it for types only |
| 9.4 | Same restrictions as normal reference names | mechanized | `resolveIn` (`Env.resolveWith`, `Env.resolveExtWith`) |
| 9.5 | ActualParameterList | notation | `Arg` |
| 9.6 | One actual parameter per parameter, in order | partial | `bindParams` pairs them in order (`List.zip`); a count mismatch is not rejected (extras dropped) |
| 9.7 | The actual parameter replaces the dummy | mechanized | `bindParams`, `Scope.bound`, `resolveIn` |
| 9.8 | Actual's references and tag default from its own environment | mechanized | the binding keeps the caller's `Scope` (`bindParams`), which `resolveTy`, `tagsOf` and `isExplicit` read; the EXAMPLE's T5.b is explicit through `untaggedChoiceOrOpen` (an untagged DummyReference, X.680 31.2.7 c)) |
| 10.1 | ABSTRACT-SYNTAX recalled | n/a | |
| 10.2 | Parameters left in an abstract syntax; used only in constraints | open (X683-1) | — |
| 10.3–10.4 | Variable constraints do not constrain | open (X683-1) | — |
| Annex A | Examples | informative | not checked by Tests (`Tests/Params.lean` uses a 3GPP-shaped example) |
| Annex B | Summary of the notation | informative | |


Example subclauses are not rows: X.681 9.16, 10.13, 11.10, 11.11, 12.11, 13.5, 14.13, 15.14, A.4, B.4, C.10, and the unnumbered examples in X.682 10 and X.683 8.5–9.8. `Tests/Objects.lean` checks X.682 clause 10's ErrorReturn example (10.6, 10.10, 10.18–10.20). `Tests/Params.lean` checks a 3GPP-shaped parameterized type with an extensible set (X.683 8.4, 9.2; X.681 12.9). No test covers the X.681 examples, INSTANCE OF, TYPE-IDENTIFIER, contents constraints or user-defined constraints.

## X.690 (BER, CER, DER)

`Asn1/X690`: `Contents.lean` (identifier, length and contents octets), `Iso2022.lean` (8.23.5), `Ber.lean` (the encoding relation `ber`, the rules `X690.rule`). Checked against X.690's examples in `Tests/X690.lean`.

| Clause | Subject | Status | Where |
|---|---|---|---|
| 1–6 | Scope, references, definitions, abbreviations, notation, convention | n/a | — |
| 7.1–7.2 | Dynamic and static conformance | n/a | — |
| 7.3 | BER allows alternative encodings; receivers support all | mechanized | `ber` is a relation over every sender's option |
| 7.4 | CER and DER allow no alternatives | open | the theorem `EncodingRule.Canonical` for `X690.rule .cer` and `.der` is stated, not proved |
| 8.1.1.1–8.1.1.3 | Identifier, length, contents, end-of-contents | mechanized | `Node`, `Node.octets` |
| 8.1.1.4 | Constraints and extension markers do not affect the encoding | mechanized | `ber` (`.constrained`; extension additions are entries like any other) |
| 8.1.1.5 | No encoding instructions | n/a | — |
| 8.1.2.1–8.1.2.5 | Identifier octets, class bits, low and high tag numbers, primitive/constructed bit | mechanized | `identOctets`, `base128`, `TagClass.bits87` |
| 8.1.2.6–8.1.2.7 | Tag of a CHOICE, of an open type | mechanized | `ber` (`.choice`, `.openType`) |
| 8.1.3.1–8.1.3.6.2 | Length forms; sender's options | mechanized | `LenForm`, `lengthOctets`, `LenForm.Fits`, `LenForm.Allowed`, `Node.LenOk`; 8.1.3.2 c) is X690-1 |
| 8.1.4–8.1.5 | Contents and end-of-contents octets | mechanized | `Node.octets`, `eoc` |
| 8.2 | BOOLEAN | mechanized | `BoolContents` |
| 8.3 | INTEGER | mechanized | `IntContents`, `intContents` |
| 8.4 | ENUMERATED | mechanized | `ber` (`.enumerated`, via `enumNumbers`) |
| 8.5.1–8.5.9 | REAL: zero, special values, binary and decimal encodings | mechanized | `RealContents`, `RealBinary`, `ExpField`, `RealDecimal`, `nrValue` (X690-2, X690-3) |
| 8.6.1–8.6.4.2 | BIT STRING, primitive and segmented | mechanized | `BitsPrim`, `bitsEnc` (X690-10) |
| 8.7.1–8.7.3.2 | OCTET STRING, primitive and segmented | mechanized | `octetsEnc` |
| 8.8 | NULL | mechanized | `ber` (`.null`) |
| 8.9.1–8.9.3 | SEQUENCE | mechanized | `CompEncs`, `CompChoice`, `compTys` |
| 8.10.1–8.10.3 | SEQUENCE OF | mechanized | `ber` (`.sequenceOf`) |
| 8.11.1–8.11.3 | SET, in the sender's order | mechanized | `ber` (`.set`) |
| 8.12.1–8.12.3 | SET OF, in any order | mechanized | `ber` (`.setOf`) |
| 8.13 | CHOICE | mechanized | `ber` (`.choice`), `altTys` |
| 8.14.1–8.14.4 | Prefixed types: explicit and implicit tagging | mechanized | `ber` (`.tagged`), `Node.retag`, `isExplicit`, `autoTagged`; encoding prefixes are not represented (X.680 31.3) |
| 8.15 | Open type | mechanized | `ber` (`.openType`, `.classField`, `.fromObjects`) |
| 8.16.1–8.16.2 | INSTANCE OF | mechanized | `ber` (`.instanceOf`), `instanceOfTy` |
| 8.17.1–8.17.2 | EMBEDDED PDV | mechanized | `ber` (`.embeddedPdv`) (X690-12) |
| 8.18.1–8.18.11 | EXTERNAL, Table 2 | mechanized | `externalRefs`, `ExternalEncoding` (X690-8) |
| 8.19.1–8.19.5 | OBJECT IDENTIFIER | mechanized | `oidContents`, `base128` |
| 8.20.1–8.20.5 | RELATIVE-OID | mechanized | `relOidContents` |
| 8.21–8.22 | OID-IRI and RELATIVE-OID-IRI | mechanized | `iriContents`, `relIriContents`, `utf8` |
| 8.23.1–8.23.4 | Restricted character strings as `[UNIVERSAL x] IMPLICIT OCTET STRING` | mechanized | `StringOctets`, `ber` (`.restricted`) |
| 8.23.5–8.23.6, Table 3 | ISO/IEC 2022 escape sequences | partial | `Iso2022Enc`, `iso2022Decode`, `assumed`; ISO/IEC 2022 itself is not transcribed (X690-6) |
| 8.23.7–8.23.10 | UniversalString, BMPString, control functions, UTF8String | mechanized | `universalOctets`, `bmpOctets`, `utf8String`; 8.23.9 holds because the values are code points |
| 8.24.1–8.24.2 | CHARACTER STRING | mechanized | `ber` (`.characterString`) (X690-12) |
| 8.25 | GeneralizedTime, UTCTime, ObjectDescriptor | mechanized | `ber` (`.generalizedTime`, `.utcTime`, `.objectDescriptor`) |
| 8.26.1–8.26.5.2 | TIME, DATE, TIME-OF-DAY, DATE-TIME, DURATION | mechanized | `TimeContents`, `TimeKind.strip`, `TimeV.Notates` |
| 9.1 | CER length forms | mechanized | `LenForm.Allowed` |
| 9.2 | CER string forms, 1000-octet fragments | mechanized | `octetsEnc`, `bitsEnc`, `CerFragments` |
| 9.3 | CER SET order | mechanized | `cerKey` (X690-11) |
| 10.1 | DER length forms | mechanized | `LenForm.Allowed`, `minLenForm` |
| 10.2 | DER string forms | mechanized | `octetsEnc`, `bitsEnc` |
| 10.3 | DER SET order | mechanized | `ber` (`.set`), `Tag.lt` |
| 11 | "BER encoding" read as CER/DER encoding | mechanized | `ber` passes the profile down |
| 11.1 | BOOLEAN TRUE all ones | mechanized | `BoolContents` |
| 11.2.1–11.2.2 | Unused bits zero; trailing zeros removed | mechanized | `BitsPrim`, `ber` (`.bitString`) |
| 11.3.1–11.3.2.6 | REAL normalized | mechanized | `RealBinary`, `ExpFieldMin`, `Nr3Canon` |
| 11.4 | GeneralString escape sequences | partial | `iso2022Decode` in canonical mode (X690-7) |
| 11.5 | DEFAULT components omitted | mechanized | `CompChoice`, `IsDefault` |
| 11.6 | SET OF order | mechanized | `octLe` |
| 11.7.1–11.7.5 | GeneralizedTime | mechanized | `GenTimeCanon` (X690-4) |
| 11.8.1–11.8.5 | UTCTime | mechanized | `UtcTimeCanon` (X690-4) |
| 11.9.1–11.9.2 | TIME canonical form | mechanized | `TimePrint.time` (X690-5) |
| 12.1 | Unambiguous, undivided, self-delimiting | partial | unambiguous for the values `Decodable` and `UnambV` cover (distinct tags, mandatory components present, simple DEFAULTs): `ber_unambiguous`, `octets_unambiguous` (`Asn1/X690/Unamb.lean`: the same encoding, the same abstract value, `eqv`); self-delimiting and the rule-level `EncodingRule.Unambiguous`, `EncodingRule.PrefixFree` not proved |
| 12.2–12.4 | Object identifiers of BER, CER, DER | mechanized | `Profile.oid` |

## X.691 (PER)

`Asn1/X691`: `Field.lean` and `Procedures.lean` (field-lists, 11.1, 11.5–11.9; the bit sums of 11.3–11.4 are in `Asn1/Bits.lean`), `Visible.lean` (PER-visible constraints and the effective constraints, 10.3), `Encode.lean` (the encoding relation `per`, the rule `X691.rule`), `Time.lean` (clause 32). Checked against Annex A in `Tests/X691.lean` and against the clause 32 notation in `Tests/X691Time.lean`. The decoder: `ViewC.lean` (the PER view computed, proved equal to `Visible.lean`'s in `ViewCSound.lean`), `Decode.lean` (`pdec`, `decode`; `asn1check decode uper|aper|cuper|caper`), `DecodeSound.lean` (`decode_sound`), `ReadComplete.lean`, `DecComplete.lean`, `DecCompleteStruct.lean` (`decode_complete`, `per_unambiguous`); run on Annex A in `Tests/X691Decode.lean`.

| Clause | Subject | Status | Where |
|---|---|---|---|
| 1–2.2 | Scope, references | n/a | — |
| 3.1–3.6 | Definitions imported from other Recommendations | n/a | — |
| 3.7.1–3.7.3 | 2's-complement encoding, abstract syntax value, bit-field | n/a | — |
| 3.7.4 | Canonical encoding | partial | CANONICAL-PER is functional on the types `CanonT` admits (`per_functional`, `per_canonical`): all but open types (X691-24) and EXTERNAL (X691-11), where it is not functional as read, and ObjectDescriptor and the ISO 2022 string types (not proved); SET OF ties need `KeyInj`, which holds for components the decoder reads back (`keyInj_of_pdec`); `EncodingRule.Canonical` (with `Equiv`) not proved |
| 3.7.5–3.7.6 | Composite type and value | mechanized | `CompOut` |
| 3.7.7 | Constrained whole number | mechanized | `intRootFields`, `pInt` |
| 3.7.8 | Effective size constraint | mechanized | `pStr`, `pSize` (X691-6) |
| 3.7.9 | Effective permitted-alphabet constraint | mechanized | `pStr`, `effAlphabet` (X691-6, X691-13) |
| 3.7.10 | Enumeration index | mechanized | `enumIndex` |
| 3.7.11 | Extensible for PER encoding | mechanized | `PSet` (its `ext`), `perB` |
| 3.7.12 | Field-list | mechanized | `FieldList` |
| 3.7.13–3.7.15 | Indefinite-length, fixed-length type, fixed value | n/a | — |
| 3.7.16 | Known-multiplier character string type | mechanized | `StrType.knownMultiplier` |
| 3.7.17–3.7.21 | Length determinant, normally small number and length, non-negative-binary-integer, outermost type | n/a | — |
| 3.7.22 | PER-visible constraint | mechanized | `evalC`, `view` |
| 3.7.23 | Relay-safe encoding | n/a | — |
| 3.7.24 | Semi-constrained whole number | mechanized | `intRootFields` |
| 3.7.25 | Simple type | mechanized | `CompOut` |
| 3.7.26 | Textually dependent | partial | `tyDep` (X691-15) |
| 3.7.27 | Unconstrained whole number | mechanized | `intRootFields` |
| 4–6.3 | Abbreviations, notation, convention | n/a | — |
| 7.1–7.2 | The four rules; the type is needed to decode | n/a | — |
| 7.3 | Relay-safety | open | not stated |
| 7.4 | BASIC-PER is not canonical: sender's options | mechanized | `per` is a relation over every sender's option (`CompOut`, `perB`, `ExternalFields`) |
| 7.5 | CANONICAL-PER restricts BASIC-PER's options | partial | for the relation: `per_canonical_basic`; for the rule, fails in general as read (X691-21) |
| 7.6 | Embedded transfer syntaxes and canonicity | open | not stated |
| 7.7–7.8 | ALIGNED and UNALIGNED variants | mechanized | `Variant`, `complete` |
| 7.9 | Self-delimiting with the type; multiples of eight bits | partial | `complete` pads to octets; `per_prefixFree` for the values the decoder reads back (`PDec`), and `decodePrefix` finds where a complete encoding ends; `EncodingRule.PrefixFree` for all values not proved |
| 7.10–7.11 | The rules apply to all variants; Annex C | n/a | — |
| 8.1–8.2 | Dynamic and static conformance | n/a | — |
| 8.3 | Any procedure giving one of the specified bit strings | mechanized | `X691.rule` relates values to bit strings, not procedures |
| 8.4 | Decoders produce the value of every conforming encoding | partial | a decoder that follows `per`: `decode_sound` (what it returns, `per` relates to the input), `decode_complete` (every encoding of a `PDec` value decodes to it), and `per_unambiguous` (two `PDec` values with equal complete encodings are equal); `EncodingRule.Unambiguous` itself (all values, `Equiv`) not proved |
| 9.1–9.3.2 | PER encoding instructions | open | not represented (X691-20) |
| 10.1.1–10.1.2 | The type model PER uses | mechanized | `per`, `perB` |
| 10.2 | Canonical order of tags | mechanized | `sortTag`, `sortByTag`, `minTag` |
| 10.3.1 | Constraints in comments | n/a | — |
| 10.3.2 | Variable constraints | open | X691-15 |
| 10.3.3–10.3.5 | User-defined, table and component relation constraints | mechanized | `evalC` |
| 10.3.6 | Textual dependence on a table constraint | partial | `tyDep`, `consDep` (X691-15) |
| 10.3.7 | Constraints on other character string types | mechanized | `pStr`, `StrType.knownMultiplier` |
| 10.3.8 | PATTERN | mechanized | `strAtom` |
| 10.3.9–10.3.10 | Size constraints; the effective size constraint | mechanized | `pSize`, `sizeAtom`, `sizeOf`, `pStr` |
| 10.3.11–10.3.12 | Permitted alphabets; the effective permitted alphabet | mechanized | `strAtom`, `pairAlg`, `effAlphabet` (X691-13, X691-14) |
| 10.3.13 | Property settings on time types | mechanized | `pTime`, `timeAtom` |
| 10.3.14 | REAL | mechanized | `perB` (REAL has no PER view) |
| 10.3.15 | Inner type constraints on EMBEDDED PDV, CHARACTER STRING | mechanized | `Predefined` (X691-10) |
| 10.3.16 | Useful types | mechanized | `UsefulTimeFields` |
| 10.3.17 | Single values on character strings | mechanized | `strAtom` |
| 10.3.18 | All other constraints, on integers and known-multiplier types | mechanized | `intAtom`, `strAtom`, `view` |
| 10.3.19–10.3.21 | Serial application and set arithmetic with constraints that are not PER-visible | mechanized | `view`, `evalES`, `evalC` (X691-5) |
| 10.3.22 | ENUMERATED, SEQUENCE, SET, CHOICE extensible by their notation | mechanized | `perB`, `EnumFields`, `SeqFields`, `ChoiceFields` |
| 10.4.1–10.4.2 | Type and value model | mechanized | `per` |
| 10.4.3 | A root value listed as an addition is a root value | mechanized | `IntFields` (X691-7) |
| 10.5.1–10.5.3 | Preamble, length, contents; fields | mechanized | `Field`, `FieldList` |
| 10.6.1–10.6.4 | Types encoded; selection, tagged and prefixed types | mechanized | `per` (through `builtin`), `perB` |
| 10.6.5 | Useful types, with X.690 11.7 and 11.8 | mechanized | `UsefulTimeFields`, `GenTimeCanon`, `UtcTimeCanon` (X691-18) |
| 10.6.6 | Value set assignments | mechanized | `per` (a value set assignment is a type assignment, X.680 16.8) |
| 11.1.1–11.1.5 | The complete encoding | mechanized | `complete`, `Carrier`, `concatFields`, `pad8` |
| 11.2.1–11.2.2 | Open type fields | mechanized | `openField` |
| 11.3.1–11.3.6 | Non-negative-binary-integer | mechanized | `nnbValue`, `NnbIn`, `NnbMinOctets`, `nnbFn`, `nnbIn_unique` (X691-1) |
| 11.4.1–11.4.6 | 2's-complement-binary-integer | mechanized | `tcValue`, `TcMinOctets`, `tcMinFn` (X691-2) |
| 11.5.1–11.5.7.4 | Constrained whole number | mechanized | `constrainedWhole`, `bitsFor`, `bitsFor_spec`, `table_11_5_7_1` |
| 11.6.1–11.6.2 | Normally small non-negative whole number | mechanized | `normallySmall` (X691-4) |
| 11.7.1–11.7.4 | Semi-constrained whole number | mechanized | `semiWhole` |
| 11.8.1–11.8.3 | Unconstrained whole number | mechanized | `unconstrainedWhole` |
| 11.9.1–11.9.4.2 | Length determinants and fragmentation | mechanized | `lengthDet`, `unconstrainedLength`, `LenKind`, `Assoc` (X691-3) |
| 12.1–12.3 | BOOLEAN | mechanized | `perB` (`.boolean`) |
| 13.1–13.2.6 | INTEGER | mechanized | `IntFields`, `intRootFields`, `constrainedInt`, `semiInt`, `unconstrainedInt` (X691-7) |
| 14.1–14.3 | ENUMERATED | mechanized | `EnumFields`, `enumIndex` |
| 15.1–15.2 | REAL | mechanized | `perB` (`.real`), `RealContents`, `octetsWithLength` |
| 16.1–16.11 | BIT STRING | mechanized | `BitsFields`, `bitsRootFields`, `NamedBitsSent` (X691-7, X691-8) |
| 17.1–17.8 | OCTET STRING | mechanized | `OctetsFields`, `octetsRootFields` |
| 18 | NULL | mechanized | `perB` (`.null`) |
| 19.1–19.4 | SEQUENCE: extension bit, preamble, root components | mechanized | `SeqFields`, `seqRootFields`, `splitEntries` |
| 19.5 | DEFAULT components | mechanized | `CompOut` |
| 19.6–19.9 | Extension additions and groups | mechanized | `SeqFields`, `GroupOut`, `openField` |
| 20.1–20.6 | SEQUENCE OF | mechanized | `SeqOfFields`, `pSize` |
| 21 | SET: the root in canonical tag order | mechanized | `perB` (`.set`), `sortTag`, `sortByTag` (X691-16) |
| 22.1 | CANONICAL-PER SET OF order | mechanized | `setOfKey`, `bitsLe` (X691-17) |
| 22.2 | BASIC-PER SET OF | mechanized | `perB` (`.setOf`) |
| 23.1–23.8 | CHOICE | mechanized | `ChoiceFields`, `sortTag`, `sortByTag` (X691-16, X691-19) |
| 24–27 | OBJECT IDENTIFIER, RELATIVE-OID, OID-IRI, RELATIVE-OID-IRI | mechanized | `octetsWithLength`, `oidContents`, `relOidContents`, `iriContents`, `relIriContents` |
| 28.1–28.3 | EMBEDDED PDV, predefined and general cases | mechanized | `Predefined`, `pdvGeneral` (X691-10) |
| 29.1–29.5 | EXTERNAL as the sequence type of 29.1, Table 1 | mechanized | `ExternalFields`, `externalRefs` |
| 29.6–29.11 | EXTERNAL encoding alternatives | mechanized | `ExternalFields` (X691-11) |
| 30.1–30.3 | Known-multiplier types; "aub" and "alb" | mechanized | `StrType.knownMultiplier`, `pStr`, `KmFields` |
| 30.4 | Extensible for PER | mechanized | `KmFields` (X691-7) |
| 30.5.1–30.5.7 | Characters in "b" bits; lengths | mechanized | `effAlphabet`, `charWidth`, `charField`, `kmBody` (X691-9) |
| 30.6.1–30.6.3 | Other character string types | mechanized | `OtherStringFields`, `StringOctets` |
| 31.1–31.3 | CHARACTER STRING, predefined and general cases | mechanized | `Predefined`, `pdvGeneral` (X691-10) |
| 32.1.1 | Encoding by property settings | mechanized | `pTime`, `TimeAs` |
| 32.1.2, Table 2 | The row whose settings all values have | mechanized | `table2`, `rowsOf`, `RowApplies`, `TimeAs` (X691-54, X691-55) |
| 32.1.3 | Rows 24–32: the same n in Fn | mechanized | `isFracRow`, `fracDigitsOf` (X691-53) |
| 32.1.4 | The encoding types, AUTOMATIC TAGS | mechanized | `timeEncModule`, `timeEncTypes` |
| 32.2.1–32.2.14 | Basic=Date encoding types | mechanized | `dateTypes`, `yearEncoding`, `dateVal`, `yearEncodingVal` (X691-56, X691-57) |
| 32.3.1–32.3.18 | Basic=Time encoding types | mechanized | `timeTypes`, `timeDifference`, `timeVal`, `timeDifferenceVal` (X691-50, X691-51) |
| 32.4.1–32.4.2 | Basic=Date-Time | mechanized | `paramTypes`, `pointVal` (X691-52) |
| 32.5.1–32.5.3 | Intervals, start and end | mechanized | `paramTypes`, `intervalComps`, `shapeVal` |
| 32.6.1–32.6.5 | Durations | mechanized | `durationIntervalEncoding`, `durationVal` |
| 32.7.1–32.7.6 | Intervals with a duration | mechanized | `paramTypes`, `intervalComps` |
| 32.8.1–32.10.6 | Recurring intervals | mechanized | `paramTypes`, `recurrenceVal`, `shapeVal` |
| 32.11.1–32.11.3 | Mixed settings: the determining rows | mechanized | `mainRow`, `dateRowOf`, `timeRowOf` |
| 32.11.4–32.11.9 | MIXED-ENCODING, FRACTIONAL-TIME, DATE-TYPE, TIME-TYPE | mechanized | `mixedEncoding`, `mixedVal`, `dateType`, `timeType`, `dateTypeVal`, `timeTypeVal` |
| 33.1 | Use of the rules | n/a | — |
| 33.2 | Object identifiers of the four rules | mechanized | `variantOfOid`, `perHook` |
| 33.3–33.4 | Use with abstract syntax names | n/a | — |
| Annex A | Example of encodings | informative | checked in `Tests/X691.lean` (A.1–A.4, both variants) |
| Annex B | Combining PER-visible and non-PER-visible constraints | informative | followed in `pStr` (X691-13) |
| Annex C | Support for the PER algorithms | informative | — |
| Annex D | Support for the ASN.1 rules of extensibility | informative | — |
| Annex E | Tutorial on concatenation of PER encodings | informative | — |
| Annex F | Identification of encoding rules | informative | — |
