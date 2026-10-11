# ASN.1 formalized in Lean 4

A mechanization of ASN.1 and two of its encoding rule families in Lean 4:

- ITU-T X.680 (the notation and its abstract values), X.681 (information objects), X.682 (constraints) and X.683 (parameterization);
- ITU-T X.690: BER, CER and DER;
- ITU-T X.691: PER, ALIGNED and UNALIGNED, BASIC and CANONICAL.

Every definition cites the clause it formalizes. Encoding rules are *relations* between abstract values and encodings, so a sender's option in the text is a choice the relation allows, and a canonical rule is the same relation with the choices fixed. Executable decoders and an encoder sit next to the relations and are proved against them.

**Status.** Work in progress. This is an unofficial mechanization: the ITU-T Recommendations are the normative text, and nothing here has been reviewed by ITU-T. `COVERAGE.md` says, subclause by subclause, what is mechanized and what is not, and `OPEN.md` lists the places where the text had to be interpreted.

## Layout

```
Asn1/Parse/   lexer, parser, module resolution and value notation (the front end)
Asn1/X680/    X.680–X.683: syntax (Ty, Val), value sets (Has), validity (Env.Valid), the checker and its soundness
Asn1/Format.lean  the format model every encoding rule instantiates (EncodingRule and its properties)
Asn1/X690/    X.690: contents octets, the relation `ber`, a decoder and its proofs
Asn1/X691/    X.691: field-lists, the procedures of clause 11, the relation `per`, the PER view, a decoder, an encoder and their proofs
Tests/        X.680–X.691 examples and Annex A, checked with #guard and proofs
Tools/Check.lean  the `asn1check` command-line tool
COVERAGE.md   every numbered normative subclause and what the Lean spec does with it
OPEN.md       the ledger of interpretations
SPEC-GAP.md   how the checker's decisions line up with the spec's validity rules
```

## What is defined

**X.680–X.683 (`Asn1/X680`).**
- `Ty` is the type notation after parsing and module resolution: built-in types, references, tags, constraints as written (X.680 49–51) and extension markers. `Val` is the abstract value, independent of any encoding.
- `Has E H m t v` is the value set of a type, with its root and extensibility. It is defined by recursion on a fuel bound and taken in the limit (`Eventually`), because EXCEPT makes it non-monotone; recursive types denote their finite values. Constraints are sets of values (X.680 50, 51), including the parts no encoding rule sees. `Equiv` is equality of abstract values (DEFAULT components, SET and SET OF order, trailing zero bits of named bit strings, time notations).
- TIME is its components and property settings (X.680 38); the register-defined string types have the ISO International Register's cells as characters.
- `Env.Valid` collects the "shall" rules: distinct names and tags, applicability of subtype notations (Tables 11, 12), references that resolve, information object rules, and the rest listed in `COVERAGE.md`.
- Information objects, object sets and table constraints (X.681, X.682) are part of the same semantics; a component relation constraint sees the textually enclosing values (X.682 10.10). Parameterized assignments bind actual parameters in a scope (X.683).
- X.682 11.4 makes the values of a CONTAINING type depend on the encoding rules, so the semantics takes them as a parameter (`ContentsHook`).

**The format model (`Asn1/Format.lean`).** An `EncodingRule` relates abstract values to bit strings. The properties are stated once for every rule: `Complete`, `Unambiguous`, `PrefixFree`, `Canonical`, `Refines`, `ExtensionCompatible`. What is proved about each rule is listed below; the rule-level statements themselves are not yet proved.

**X.690 (`Asn1/X690`).** An encoding is a `Node` (identifier, length form, contents or nested encodings). `ber E p n sc t v nd` relates a value to its encodings under a `Profile` (`.ber`, `.cer`, `.der`): every sender's option of clause 8 is allowed under BER, and the restrictions of clauses 9–11 sit where each choice is made, so CER and DER are BER with the choices fixed. `X690.rule p` is the encoding rule.

**X.691 (`Asn1/X691`).** A value encodes to a field-list of unaligned and octet-aligned bit-fields (10.5): `per E v n sc t x fl`, with the procedures of 11.3–11.9. The complete encoding pads them (11.1), and `X691.rule v` is the encoding rule. ALIGNED and UNALIGNED, BASIC and CANONICAL are one definition with a `Variant` parameter. The effective constraints of 10.3 (the PER view: bounds, sizes, permitted alphabets) are part of the spec (`Visible.lean`), and so is clause 32 (`Time.lean`, transcribed from X.691's own ASN.1 in `Tests/asn1/x691-time.asn`).

## What is proved

All of the following are proved without `sorry`, on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Most statements are at a fuel bound `n`, as the definitions are.

**The checker (X.680–X.683).**
- `checkEnv_sound` (`X680/Soundness.lean`): if `Env.Valid E H`, then from some fuel on every diagnostic `checkEnv` reports is a notation rule. That is, the checker rejects only what the spec rejects. The converse is not proved. `SPEC-GAP.md` describes the correspondence rule by rule.

**X.690.**
- `decode_sound` (`X690/DecSound.lean`): whatever `decode` returns, the input octets are the layout of an encoding that `ber` relates to that value, with length forms the profile allows.
- `decode_complete` (`X690/DecComplete.lean`), with `ParseComplete.lean`: the octets of an encoding that `ber` relates to a value are decoded, to that value where values are equal only when identical. It assumes `Decodable`: distinct component names and enumeration numbers, IMPLICIT only on types with one tag, well-formed OBJECT IDENTIFIER and REAL values, characters that fit, simple DEFAULTs under CER and DER. Open types, contents constraints, EXTERNAL, the OID-IRI types and the time types are excluded.
- `ber_unambiguous`, `octets_unambiguous` (`X690/Unamb.lean`): two values with the same encoding are the same abstract value. It assumes `Decodable` and `UnambV` for both values: distinct tags (X.680 25.6, 27.3, 29.3), the mandatory components present, COMPONENTS OF expanded, simple DEFAULTs, and fixed-type class fields of types whose values are equal when identical. `Tests/X690Unamb.lean` shows the conditions hold for X.690's 8.9.3 example.
- Smaller results: `intContents_spec` (8.3), `iso2022Decode_canon` (11.4).

**X.691.**
- `decode_sound` (`X691/DecodeSound.lean`): what `decode` returns, `per` relates to the input. `decodePrefix_sound` does the same for a complete encoding followed by other octets (7.9).
- `decode_complete`, `pdec_complete` (`X691/DecCompleteStruct.lean`): the complete encoding of a value is decoded back to it. It assumes `PDec`: the PER view is computed, enumeration numbers are distinct, the value is in the form the decoder returns, and open types are picked by a table constraint. EMBEDDED PDV, EXTERNAL, CHARACTER STRING and the time types are not decoded.
- `per_unambiguous` (8.4) and `per_prefixFree` (7.9), for `PDec` values.
- `encode_sound` (`X691/EncSound.lean`): the encoder, which makes CANONICAL-PER's choices, produces an encoding `per` relates to the value.
- `per_canonical_basic` (`X691/Properties.lean`, 7.5): CANONICAL-PER encodings are BASIC-PER encodings, at the level of the relation.
- `per_functional`, `per_canonical` (`X691/Canonical.lean`, 3.7.4): under CANONICAL-PER a value has one encoding, for the types `CanonT` covers. Open types, EXTERNAL, ObjectDescriptor and the ISO 2022 string types are not covered.
- `ViewCSound.lean`: the computed PER view equals the one the spec defines.

**Not yet.** The step from a valid schema (`Has`, `Env.Valid`) to the decoders' hypotheses (`Decodable`, `UnambV`, `PDec`). The rule-level properties of `Format.lean`. An X.690 encoder, and BER prefix-freeness. The checker's completeness. Encoding rules other than BER/CER/DER and PER (OER, JER, XER, ECN).

## Coverage

`COVERAGE.md` maps every numbered normative subclause; `scripts/check_coverage.py COVERAGE.md` checks that every cited name, file and ledger id exists.

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

## The ledger

`OPEN.md` lists each place where the text is silent, ambiguous or contradicts itself, so the Lean spec had to decide: the clause, what the text says, the decision taken, what implementations do, and where the decision lives in the code (marked with `-- OPEN` comments). Ids are per Recommendation (`X680-n`, `X690-n`, `X691-n`, ...).

## Building

Install Lean with [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (Lean 4.34.1) and Mathlib in `lakefile.toml` (v4.34.1).

```
lake exe cache get          # prebuilt Mathlib
lake build                  # the library (Asn1)
lake build Tests asn1check  # the tests and the command-line tool
```

## asn1check

```
asn1check lex FILE...                     lexical items of each module file
asn1check parse FILE...                   parse each file
asn1check resolve FILE...                 parse, resolve and check a set of modules against X.680–X.683
asn1check rules                           the checker's rules and the spec fields each one decides
asn1check decode (ber|cer|der|uper|aper|cuper|caper) Module.Type [-v] [--json] [--prefix] MODULE... -- DATA...
                                          decode each DATA file as a value of Module.Type
asn1check roundtrip (uper|aper|cuper|caper) Module.Type MODULE... -- DATA...
                                          decode, re-encode with the proved encoder, compare
```

`cuper` and `caper` are CANONICAL-PER. `--prefix` (PER) accepts a complete encoding followed by other octets.

## Conventions

- Every definition, and every constructor that encodes a rule, cites its clause in its doc comment, as `X.691 11.9.3.5`.
- Relations come first: a definition reads like the text, even when the text is not an algorithm. Executable functions sit next to the relation and are proved to agree with it.
- Bits are `List Bool`, leading bit first. Integers are `Int`, whole numbers `Nat`, characters `Nat` code points (ISO/IEC 10646), except in the four types X.680 Table 8 defines by the ISO International Register.

Verified codecs, such as [vasn](https://github.com/zhouxt1/vasn), are meant to be proved against this specification; that connection is future work.

## License

MIT, see `LICENSE`.
