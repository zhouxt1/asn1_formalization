import Asn1.Parse.Basic
import Asn1.Parse.Regex
import Asn1.X680.Syntax

/-!
# The grammar (X.680 13–51, X.681 9–15, X.682 8–11, X.683 8–9)

The productions as the text writes them. What the grammar alone cannot decide is left for
`Asn1.Parse.Resolve`, which knows every module:
- whether `X.&f` is a field of a class or of an object set (X.681 14, 15), and whether `Name` on the
  right of `::=` is a type or a class (X.681 7.1 decides only for all-capital names);
- what an object written in braces says (X.681 11.5, 11.6), read through its class's syntax;
- what an actual parameter is (X.683 9.5), from its dummy;
- what value notation denotes (`RawVal`), from its governor.
-/

namespace Asn1.Parse

open Asn1.X680

/-- X.680 41, Table 8: the restricted character string types (41.1: ISO646String is VisibleString,
T61String is TeletexString). -/
def strKw : String → Option StrType
  | "BMPString" => some .bmp | "GeneralString" => some .general | "GraphicString" => some .graphic
  | "IA5String" => some .ia5 | "ISO646String" => some .visible | "NumericString" => some .numeric
  | "PrintableString" => some .printable | "TeletexString" => some .teletex
  | "T61String" => some .teletex | "UniversalString" => some .universal
  | "UTF8String" => some .utf8 | "VideotexString" => some .videotex | "VisibleString" => some .visible
  | _ => none

/-- Reserved words that begin a type (17.2). NULL is left out: as a subtype element it is a value
(51.3.1). -/
def typeKws : List String :=
  ["BOOLEAN", "INTEGER", "ENUMERATED", "REAL", "BIT", "OCTET", "SEQUENCE", "SET", "CHOICE", "OBJECT",
   "RELATIVE-OID", "OID-IRI", "RELATIVE-OID-IRI", "EMBEDDED", "EXTERNAL", "CHARACTER", "TIME", "DATE",
   "TIME-OF-DAY", "DATE-TIME", "DURATION", "GeneralizedTime", "UTCTime", "ObjectDescriptor",
   "INSTANCE", "TYPE-IDENTIFIER", "ABSTRACT-SYNTAX", "BMPString", "GeneralString", "GraphicString",
   "IA5String", "ISO646String", "NumericString", "PrintableString", "TeletexString", "T61String",
   "UniversalString", "UTF8String", "VideotexString", "VisibleString"]

/-- X.681 Annexes A and B: TYPE-IDENTIFIER and ABSTRACT-SYNTAX used as a class (not `C.&f`). -/
def builtinClass : P (Option ClassRef) := do
  if (← isKw "TYPE-IDENTIFIER") && !(← isSymAt 1 ".") then do let _ ← next; return some .typeIdentifier
  else if (← isKw "ABSTRACT-SYNTAX") && !(← isSymAt 1 ".") then do let _ ← next; return some .abstractSyntax
  else return none

/-- The governor of an object or object set assignment that is a built-in class, as a reference to
it by name (`Resolve` reads it back). -/
def builtinClassTy : ClassRef → Ty
  | .typeIdentifier => .ref "TYPE-IDENTIFIER"
  | .abstractSyntax => .ref "ABSTRACT-SYNTAX"
  | _ => .ref ""

/-- The lexical items a parser read. -/
def sliceOf {α : Type} (p : P α) : P (α × List Tok) := do
  let i ← get
  let a ← p
  let j ← get
  let ls ← read
  return (a, ((ls.extract i j).map (·.tok)).toList)

/-- X.680 19.1, 22.1: `{ a(1), b(-2) }`, numbers only. -/
partial def namedNumbers : P (List (String × Int)) := do
  sym "{"
  let rec items (acc : Array (String × Int)) : P (List (String × Int)) := do
    let nm ← lower
    sym "("
    let neg ← optSym "-"
    let k ← number
    sym ")"
    let acc := acc.push (nm, if neg then -(k : Int) else k)
    if ← optSym "," then items acc else do sym "}"; return acc.toList
  items #[]

/-- X.680 20.1: an "EnumerationItem": `a` or `a(n)`. -/
def enumItem : P (String × Option Int) := do
  let nm ← lower
  if ← optSym "(" then
    let neg ← optSym "-"
    let k ← number
    sym ")"
    return (nm, some (if neg then -(k : Int) else k))
  else return (nm, none)

/-- A field name path, `&a.&b` (X.681 14.1 "FieldName"), as `["&a", "&b"]`. -/
partial def fieldPath : P (List String) := do
  match ← peek with
  | some (.field f) =>
    let _ ← next
    if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .field _ => true | _ => false) then
      let _ ← next
      return ("&" ++ f) :: (← fieldPath)
    else return ["&" ++ f]
  | _ => fail "expected a field reference &…"

/-- X.680 13.1 "ObjectIdentifierValue" and the like: skip a balanced `{…}`. -/
def skipBraces : P Unit := do let _ ← balanced "{" "}"; return ()

/-- The non-negative number a value assignment `v INTEGER ::= k` or `v T ::= k` in the text gives `v`. -/
def intAssigned (v : String) : P (Option Nat) := do
  let ls ← read
  let toks := ls.toList.map (·.tok)
  let rec go : List Tok → Option Nat
    | .lower w :: .kw "INTEGER" :: .sym "::=" :: .number k :: rest => if w == v then some k else go rest
    | .lower w :: .upper _ :: .sym "::=" :: .number k :: rest => if w == v then some k else go rest
    | _ :: rest => go rest
    | [] => none
  return go toks

/-- X.681 10.6: the reserved words a "Literal" may not be. -/
def notLiterals : List String :=
  ["ABSTRACT-SYNTAX", "BIT", "BOOLEAN", "CHARACTER", "CHOICE", "CONTAINING", "DATE", "DATE-TIME",
   "DURATION", "EMBEDDED", "END", "ENUMERATED", "EXTERNAL", "FALSE", "INSTANCE", "INTEGER",
   "MINUS-INFINITY", "NOT-A-NUMBER", "NULL", "OBJECT", "OCTET", "OID-IRI", "PLUS-INFINITY", "REAL",
   "RELATIVE-OID", "RELATIVE-OID-IRI", "SEQUENCE", "SET", "TIME", "TIME-OF-DAY", "TRUE", "TYPE-IDENTIFIER"]

/-- What is wrong with a class's "SyntaxList", if anything: X.681 7.9, a "word" has no lower-case
letters or digits; 10.6; 10.9, each field of the class appears exactly once (and no other);
10.12 a), an optional group has a field or a group. -/
partial def syntaxListError (fs : List FieldSpec) (items : List SynItem) : Option String :=
  let fname : FieldSpec → String
    | .typeField n _ | .fixedValue n _ _ _ | .varValue n _ _ | .fixedValueSet n _ _
    | .varValueSet n _ _ | .objectField n _ _ | .objectSetField n _ _ => n
  let rec flds : List SynItem → List String
    | [] => []
    | .field f :: r => f :: flds r
    | .optional g :: r => flds g ++ flds r
    | .literal _ :: r => flds r
  let rec bad : List SynItem → Option String
    | [] => none
    | .literal w :: r =>
      if w != "," && !(w.all fun c => c.isUpper || c == '-') then some s!"{w} is not a word (X.681 7.9)"
      else if notLiterals.contains w then some s!"{w} may not be a literal (X.681 10.6)"
      else bad r
    | .optional g :: r =>
      if !(g.any fun i => match i with | .literal _ => false | _ => true) then
        some "an optional group without a field (X.681 10.12 a))"
      else (bad g).orElse fun _ => bad r
    | .field _ :: r => bad r
  let used := flds items
  let names := fs.map fname
  (bad items).orElse fun _ =>
    match used.find? (fun f => !names.contains f) with
    | some f => some s!"WITH SYNTAX names {f}, which the class does not have (X.681 10.9)"
    | none => match names.find? (fun f => (used.filter (· == f)).length != 1) with
      | some f => some s!"the field {f} is not in WITH SYNTAX exactly once (X.681 10.9)"
      | none => none

mutual
  /-- X.680 53.4 "ExceptionSpec", which does not change the values (53.3): `! SignedNumber`,
  `! DefinedValue` or `! Type : Value`. Whether a defined value names one is checked from the
  module's lexical items (`exceptionRefs`). -/
  partial def exceptionSpec : P Unit := do
    if ← optSym "!" then
      match ← peek with
      | some (.number _) => let _ ← next
      | some (.sym "-") => let _ ← next; let _ ← number
      | some (.lower _) =>
        -- a "valuereference", or a "ParameterizedValue"
        let _ ← next
        if ← isSym "{" then let _ ← actualParams
      | some (.upper _) =>
        if (← isSymAt 1 ".") && (← peekAt 2).any (fun t => match t with | .lower _ => true | _ => false) then
          -- an "ExternalValueReference"
          let _ ← next; let _ ← next; let _ ← next
        else do let _ ← ty; sym ":"; let _ ← value
      | _ => do let _ ← ty; sym ":"; let _ ← value

  /-- X.680 20.1 "Enumerations": the root, then after "..." the additions. -/
  partial def enumerations : P (List (String × Option Int) × Option (List (String × Option Int))) := do
    sym "{"
    let rec items (acc : Array (String × Option Int)) (stop : P Bool) : P (List (String × Option Int)) := do
      if ← stop then return acc.toList
      let it ← enumItem
      let acc := acc.push it
      if (← isSym ",") && !(← isSymAt 1 "...") then do let _ ← next; items acc stop
      else return acc.toList
    let root ← items #[] (isSym "...")
    if root.isEmpty then fail "expected an enumeration item (20.1)"
    if ← optSym "," then pure () else if ← isSym "..." then fail "expected , before ... (20.1)"
    if ← optSym "..." then
      exceptionSpec
      if ← optSym "," then
        let adds ← items #[] (return false)
        sym "}"
        return (root, some adds)
      else do sym "}"; return (root, some [])
    else do sym "}"; return (root, none)

  /-- X.680 17.7 "Value", as written (`RawVal`). -/
  partial def value : P RawVal := do
    match ← peek with
    | some (.number n) => let _ ← next; return .num n
    | some (.real i f e) => let _ ← next; return .real false i f e
    | some (.sym "-") =>
      let _ ← next
      match ← next with
      | .number n => return .num (-(n : Int))
      | .real i f e => return .real true i f e
      | _ => fail "expected a number after -"
    | some (.bstring b) => let _ ← next; return .bstring b
    | some (.hstring h) => let _ ← next; return .hstring h
    | some (.cstring c) => let _ ← next; return .cstring c
    | some (.kw k) =>
      -- X.681 14.6: `Type : Value`, a value of an open type
      match ← attempt (do let (_, ts) ← sliceOf tyBase; sym ":"; pure ts) with
      | some ts => return .typed ts (← value)
      | none =>
      if k ∈ ["TRUE", "FALSE", "NULL", "PLUS-INFINITY", "MINUS-INFINITY", "NOT-A-NUMBER"] then
        let _ ← next; return .kw k
      else if k == "CONTAINING" then do let _ ← next; return .containing (← value)
      else fail "expected a value"
    | some (.sym "{") => bracesValue
    | some (.lower s) =>
      let _ ← next
      if ← optSym ":" then return .choice s (← value)
      else if ← isSym "(" then
        let _ ← next
        let v ← value
        sym ")"
        return .nameNum s v
      else if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .field _ => true | _ => false) then
        let _ ← next
        return .fromObject s (← fieldPath)
      else return .ident s
    | some (.upper m) =>
      match ← attempt (do let (_, ts) ← sliceOf tyBase; sym ":"; pure ts) with
      | some ts => return .typed ts (← value)
      | none =>
      if (← isSymAt 1 ".") && (← peekAt 2).any (fun t => match t with | .lower _ => true | _ => false) then
        let _ ← next; let _ ← next
        return .ext m (← lower)
      else fail "expected a value"
    | _ => fail "expected a value"

  /-- `{ … }` value notation: comma-separated items, each a run of values. -/
  partial def bracesValue : P RawVal := do
    sym "{"
    if ← optSym "}" then return .braces []
    let rec run (acc : Array RawVal) : P (List RawVal) := do
      if (← isSym ",") || (← isSym "}") then return acc.toList
      run (acc.push (← value))
    let rec items (acc : Array (List RawVal)) : P (List (List RawVal)) := do
      let it ← run #[]
      let acc := acc.push it
      if ← optSym "," then items acc else do sym "}"; return acc.toList
    return .braces (← items #[])

  /-- X.680 17.1 "Type", with the constraints that follow it (49.1). -/
  partial def ty : P Ty := do
    let t ← tyBase
    constraintsAfter t

  partial def constraintsAfter (t : Ty) : P Ty := do
    if ← isSym "(" then
      -- a type reference may name an "ObjectClassFieldType" (X.682 10.1): `I ({S})` is read as a table
      -- constraint when the braces start with an object set reference
      let refTable := (match t with | .ref _ | .extRef .. => true | _ => false) &&
        (← isSymAt 1 "{") && (← peekAt 2).any (fun x => match x with | .upper _ => true | _ => false)
      let c ← constraint (tableable t || refTable)
      constraintsAfter (.constrained t c)
    else return t

  /-- X.681 14.3, X.682 A: a simple table constraint follows a class field type or INSTANCE OF. -/
  partial def tableable : Ty → Bool
    | .classField .. | .instanceOf _ | .fromObjects .. => true
    | .tagged _ _ t | .constrained t _ => tableable t
    | _ => false

  /-- A "Type" without the constraints after it. -/
  partial def tyBase : P Ty := do
    match ← peek with
    | some (.sym "[") =>
      -- 31.3 "EncodingPrefixedType": `[ EncodingReference EncodingInstruction ]`. What follows `[` is
      -- not a class or number. 31.3.2 NOTE 2 lets a tool ignore the whole prefix, using `]` as the
      -- terminator; the instruction never contains `[` or `]` (31.3.2 NOTE 1). 3.8.27 NOTE: encoding
      -- instructions do not change the abstract values.
      -- 31.3.3: with no "EncodingReference" the module's default applies, and when that is TAG
      -- (13.1: no "EncodingReferenceDefault") the brackets are a "Tag"
      let isEncPrefix ← do
        match ← peekAt 1 with
        | some (.upper u) =>
          if ← isSymAt 2 ":" then
            if u == "TAG" then pure false
            -- 12.25: an "encodingreference" is upper-case letters, digits and hyphens
            else if u.all fun c => c.isUpper || c.isDigit || c == '-' then pure true
            else fail "expected an encoding reference (12.25)"
          else pure !(← defaultEncIsTag)
        | _ => pure !(← defaultEncIsTag)
      if isEncPrefix then
        let _ ← next
        let rec skip : Nat → P Unit
          | 0 => throw "unterminated encoding prefix"
          | fuel + 1 => do
            if ← isSym "]" then let _ ← next else
              -- 31.3.2 NOTE 1: an encoding instruction holds no `[`
              if ← isSym "[" then fail "an encoding prefix holds no [ (31.3.2)"
              let _ ← next
              skip fuel
        skip 100000
        return (← ty)
      -- 31.2 "TaggedType"; `[TAG: 0]` states the encoding reference, TAG (31.2.1, 31.2.2)
      let _ ← next
      if (← peek) == some (.upper "TAG") && (← isSymAt 1 ":") then
        let _ ← next; let _ ← next
      let cls : TagClass ←
        if ← optKw "UNIVERSAL" then pure .universal
        else if ← optKw "APPLICATION" then pure .application
        else if ← optKw "PRIVATE" then pure .private_
        else pure .context
      -- 31.2.1 "ClassNumber ::= number | DefinedValue": a value reference to a non-negative
      -- integer, assigned in the text as `v INTEGER ::= k` (or `v T ::= k`)
      let n ← match ← peek with
        | some (.lower v) => do
          let _ ← next
          match ← intAssigned v with
          | some k => pure k
          | none => fail s!"the tag number {v} is not a number assigned in this text (31.2.1)"
        | _ => number
      sym "]"
      let kind : TagKind ←
        if ← optKw "IMPLICIT" then pure .implicit
        else if ← optKw "EXPLICIT" then pure .explicit
        else pure .default_
      return .tagged ⟨cls, n⟩ kind (← ty)
    | some (.kw k) =>
      let _ ← next
      match k with
      | "BOOLEAN" => return .boolean
      | "NULL" => return .null
      | "REAL" => return .real
      | "EXTERNAL" => return .external
      | "INTEGER" => return .integer (← if ← isSym "{" then namedNumbers else pure [])
      | "ENUMERATED" => let (r, e) ← enumerations; return .enumerated r e
      | "BIT" => kw "STRING"; return .bitString ((← if ← isSym "{" then namedNumbers else pure []).map fun (s, i) => (s, i.toNat))
      | "OCTET" => kw "STRING"; return .octetString
      | "OBJECT" => kw "IDENTIFIER"; return .objectIdentifier
      | "RELATIVE-OID" => return .relativeOid
      | "OID-IRI" => return .oidIri
      | "RELATIVE-OID-IRI" => return .relativeOidIri
      | "EMBEDDED" => kw "PDV"; return .embeddedPdv
      | "CHARACTER" => kw "STRING"; return .characterString
      | "TIME" => return .time
      | "DATE" => return .date
      | "TIME-OF-DAY" => return .timeOfDay
      | "DATE-TIME" => return .dateTime
      | "DURATION" => return .duration
      | "GeneralizedTime" => return .generalizedTime
      | "UTCTime" => return .utcTime
      | "ObjectDescriptor" => return .objectDescriptor
      | "SEQUENCE" => seqOrSet true
      | "SET" => seqOrSet false
      | "CHOICE" => let (r, e) ← alternatives; return .choice r e
      | "INSTANCE" => kw "OF"; return .instanceOf (← classRef)
      | "TYPE-IDENTIFIER" => sym "."; return .classField .typeIdentifier (← fieldPath)
      | "ABSTRACT-SYNTAX" => sym "."; return .classField .abstractSyntax (← fieldPath)
      | _ => match strKw k with
        | some s => return .restricted s
        | none => fail s!"unexpected {k}"
    | some (.lower s) =>
      if ← isSymAt 1 "<" then
        -- 30.1 "SelectionType"
        let _ ← next; let _ ← next
        return .selection s (← ty)
      else if (← isSymAt 1 ".") then
        -- X.681 15 "TypeFromObject": obj.&T
        let _ ← next; let _ ← next
        return .fromObjects (.spec (some (.obj (.ref none s []))) false none) (← fieldPath)
      else fail "expected a type"
    | some (.upper _) =>
      let (mn, name) ← definedName
      let args ← if ← isSym "{" then actualParams else pure []
      if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .field _ => true | _ => false) then
        let _ ← next
        -- X.681 14.1 "ObjectClassFieldType", or 15 "ValueSetFromObjects"/"TypeFromObject" over an
        -- object set: `Resolve` tells them apart
        return .classField (.ref mn name args) (← fieldPath)
      else if args ≠ [] then return .paramRef mn name args
      else match mn with
        | some m => return .extRef m name
        | none => return .ref name
    | _ => fail "expected a type"

  /-- `Name` or `Module.Name` (14.6). -/
  partial def definedName : P (Option String × String) := do
    let n ← upper
    if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .upper _ => true | _ => false) then
      let _ ← next
      return (some n, ← upper)
    else return (none, n)

  /-- X.683 9.5: `{ ActualParameter, … }`, each kept as lexical items. -/
  partial def actualParams : P (List Arg) := do
    let ts ← balanced "{" "}"
    -- 9.5: ActualParameterList ::= "{" ActualParameter "," + "}"
    if ts.isEmpty then fail "an actual parameter list has a parameter (X.683 9.5)"
    return (splitTopCommas ts).map Arg.raw

  /-- SEQUENCE and SET (25, 27) and their OF forms (26, 28, 49.5). -/
  partial def seqOrSet (isSeq : Bool) : P Ty := do
    let mk (r : List Comp) (e : Option (List ExtAdd)) (r2 : List Comp) : Ty :=
      if isSeq then .sequence r e r2 else .set r e r2
    let mkOf (t : Ty) : Ty := if isSeq then .sequenceOf t else .setOf t
    if ← isSym "{" then
      let (r, e, r2) ← components
      return mk r e r2
    else if ← optKw "OF" then return mkOf (← namedOrType)
    else if ← optKw "SIZE" then
      -- 49.5: SEQUENCE SIZE (…) OF T
      let c ← constraint false
      kw "OF"
      return .constrained (mkOf (← namedOrType)) (.mk (.elem (.size c)) false none)
    else if ← isSym "(" then
      let c ← constraint false
      kw "OF"
      return .constrained (mkOf (← namedOrType)) c
    else fail "expected {, OF, SIZE or ( after SEQUENCE/SET"

  /-- 26.1: `SEQUENCE OF NamedType`: an identifier before the type changes nothing. -/
  partial def namedOrType : P Ty := do
    match ← peek with
    | some (.lower _) =>
      if (← isSymAt 1 "<") || (← isSymAt 1 ".") then ty
      else do let _ ← lower; ty
    | _ => ty

  /-- 25.1 "ComponentType". -/
  partial def component : P Comp := do
    if ← optKw "COMPONENTS" then
      kw "OF"
      return .componentsOf (← ty)
    let nm ← lower
    let t ← ty
    if ← optKw "OPTIONAL" then return .mk nm t .optional
    else if ← optKw "DEFAULT" then return .mk nm t (.default_ (.raw (← value)))
    else return .mk nm t .mandatory

  /-- 25.1 "ComponentTypeLists": the root, the extension additions, the root after the second
  ellipsis. -/
  partial def components : P (List Comp × Option (List ExtAdd) × List Comp) := do
    sym "{"
    if ← optSym "}" then return ([], none, [])
    -- items, each a component, an ellipsis, or a [[ ]] group
    let rec items (root : Array Comp) (adds : Option (Array ExtAdd)) (root2 : Array Comp) (ells : Nat) :
        P (List Comp × Option (List ExtAdd) × List Comp) := do
      let (root, adds, root2, ells) ←
        if ← optSym "..." then do
          -- 25.1: at most two extension markers
          if ells ≥ 2 then fail "expected a component: a component list has at most two ... (25.1)"
          exceptionSpec
          pure (root, adds.orElse (fun _ => some #[]), root2, ells + 1)
        else if ← optSym "[[" then do
          -- 25.1: an ExtensionAdditionGroup is an ExtensionAddition, between the two markers
          if ells ≠ 1 then fail "expected a component: [[ ]] only follows the extension marker (25.1)"
          let ver ← if (← peek).any (fun t => match t with | .number _ => true | _ => false) && (← isSymAt 1 ":") then
              do let k ← number; sym ":"; pure (some k) else pure none
          let rec grp (acc : Array Comp) : P (List Comp) := do
            let c ← component
            if ← optSym "," then grp (acc.push c) else do sym "]]"; return (acc.push c).toList
          let cs ← grp #[]
          pure (root, adds.map (·.push (.group ver cs)), root2, ells)
        else do
          let c ← component
          if ells = 0 then pure (root.push c, adds, root2, ells)
          else if ells = 1 then pure (root, adds.map (·.push (.one c)), root2, ells)
          else pure (root, adds, root2.push c, ells)
      if ← optSym "," then items root adds root2 ells
      else do sym "}"; return (root.toList, adds.map (·.toList), root2.toList)
    items #[] none #[] 0

  /-- 29.1 "AlternativeTypeLists". -/
  partial def alternatives : P (List Alt × Option (List AltAdd)) := do
    sym "{"
    let rec items (root : Array Alt) (adds : Option (Array AltAdd)) (ells : Nat) :
        P (List Alt × Option (List AltAdd)) := do
      let (root, adds, ells) ←
        if ← optSym "..." then do
          exceptionSpec
          pure (root, adds.orElse (fun _ => some #[]), ells + 1)
        else if ← optSym "[[" then do
          let ver ← if (← peek).any (fun t => match t with | .number _ => true | _ => false) && (← isSymAt 1 ":") then
              do let k ← number; sym ":"; pure (some k) else pure none
          let rec grp (acc : Array Alt) : P (List Alt) := do
            let nm ← lower
            let a := Alt.mk nm (← ty)
            if ← optSym "," then grp (acc.push a) else do sym "]]"; return (acc.push a).toList
          let as ← grp #[]
          pure (root, adds.map (·.push (.group ver as)), ells)
        else do
          -- 29.1: OptionalExtensionMarker ends the list; no alternative follows a second "..."
          if ells ≥ 2 then fail "expected }: no alternative follows a CHOICE's second ... (29.1)"
          let nm ← lower
          let a := Alt.mk nm (← ty)
          if ells = 0 then pure (root.push a, adds, ells) else pure (root, adds.map (·.push (.one a)), ells)
      -- 29.1: RootAlternativeTypeList comes first and has at least one NamedType
      if root.isEmpty then fail "expected an alternative: a CHOICE's root has one (29.1)"
      if ← optSym "," then items root adds ells
      else do sym "}"; return (root.toList, adds.map (·.toList))
    items #[] none 0

  /-- X.680 49.6 "Constraint": `( ConstraintSpec ExceptionSpec )`. `tableOk`: the parent may take a
  simple table constraint (X.681 14.3). -/
  partial def constraint (tableOk : Bool) : P Constraint := do
    sym "("
    let (c, ts) ← sliceOf (constraintSpec tableOk)
    if ← isSym "!" then
      -- 49.6: without an extension marker, only where the "ConstraintSpec" has a "DummyReference"
      -- (here: any reference) or is a "UserDefinedConstraint"
      let ext := match c with | .mk _ e _ => e | .userDefined => true | _ => false
      let names := ts.any fun t => match t with | .upper _ | .lower _ => true | _ => false
      if !ext && !names then fail "an exception spec with no extension marker or dummy reference (49.6)"
    exceptionSpec
    sym ")"
    return c

  partial def constraintSpec (tableOk : Bool) : P Constraint := do
    if ← optKw "CONSTRAINED" then
      -- X.682 9
      kw "BY"
      skipBraces
      return .userDefined
    else if ← optKw "CONTAINING" then
      -- X.682 11
      let t ← ty
      if ← optKw "ENCODED" then do kw "BY"; return .contents (some t) (some (.raw (← value)))
      else return .contents (some t) none
    else if ← optKw "ENCODED" then
      kw "BY"
      return .contents none (some (.raw (← value)))
    else if tableOk && (← isSym "{") then
      match ← attempt tableConstraint with
      | some c => return c
      | none => elementSetSpecs
    else elementSetSpecs

  /-- X.682 10.3, 10.7: `{ObjectSet}` and `{ObjectSet}{@a, @.b}`. -/
  partial def tableConstraint : P Constraint := do
    let os ← objSetBraces
    let refs ← if ← isSym "{" then do
        sym "{"
        let rec ats (acc : Array AtRef) : P (List AtRef) := do
          let a ← atNotation
          if ← optSym "," then ats (acc.push a) else do sym "}"; return (acc.push a).toList
        ats #[]
      else pure []
    if !(← isSym ")") && !(← isSym "!") then fail "a table constraint ends here"
    return .table os refs

  /-- X.682 10.7 "AtNotation": `@a.b`, or `@.a`, `@..a`, … -/
  partial def atNotation : P AtRef := do
    sym "@"
    let dots : Nat ← match ← peek with
      | some (.sym ".") => do let _ ← next; pure 1
      | some (.sym "..") => do let _ ← next; pure 2
      | some (.sym "...") => do let _ ← next; pure 3
      | _ => pure 0
    let rec more (acc : Nat) : P Nat := do
      match ← peek with
      | some (.sym ".") => do let _ ← next; more (acc + 1)
      | some (.sym "..") => do let _ ← next; more (acc + 2)
      | _ => return acc
    let dots ← if dots > 0 then more dots else pure 0
    let rec path (acc : Array String) : P (List String) := do
      let nm ← lower
      if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .lower _ => true | _ => false) then
        do let _ ← next; path (acc.push nm)
      else return (acc.push nm).toList
    let p ← path #[]
    return ⟨if dots = 0 then none else some (dots - 1), p⟩

  /-- X.680 50.1 "ElementSetSpecs". -/
  partial def elementSetSpecs : P Constraint := do
    let root ← elemSet
    if (← isSym ",") && (← isSymAt 1 "...") then
      let _ ← next; let _ ← next
      exceptionSpec
      if ← optSym "," then return .mk root true (some (← elemSet))
      else return .mk root true none
    else return .mk root false none

  /-- X.680 50.1 "ElementSetSpec". -/
  partial def elemSet : P ElemSet := do
    if ← optKw "ALL" then
      kw "EXCEPT"
      return .allExcept (← elements)
    else unions

  partial def unions : P ElemSet := do
    let a ← intersections
    if (← optSym "|") || (← optKw "UNION") then return .union a (← unions) else return a

  partial def intersections : P ElemSet := do
    let a ← intersectionElements
    if (← optSym "^") || (← optKw "INTERSECTION") then return .inter a (← intersections) else return a

  partial def intersectionElements : P ElemSet := do
    let a ← elements
    if ← optKw "EXCEPT" then return .except a (← elements) else return a

  /-- X.680 50.1 "Elements". -/
  partial def elements : P ElemSet := do
    if ← isSym "(" then
      let _ ← next
      let s ← elemSet
      sym ")"
      return s
    else return .elem (← subtypeElement)

  /-- Whether a type starts here (rather than a value). -/
  partial def startsType : P Bool := do
    match ← peek with
    | some (.kw k) => return k ∈ typeKws
    | some (.sym "[") => return true
    | some (.upper _) =>
      -- `Module.value` is a value
      return !((← isSymAt 1 ".") && (← peekAt 2).any (fun t => match t with | .lower _ => true | _ => false))
    | some (.lower _) => isSymAt 1 "<"
    | _ => return false

  /-- X.680 51.1 "SubtypeElements". -/
  partial def subtypeElement : P Elem := do
    if ← optKw "SIZE" then return .size (← constraint false)
    else if ← optKw "FROM" then return .from_ (← constraint false)
    else if ← optKw "WITH" then
      if ← optKw "COMPONENT" then return .withComponent (← constraint false)
      else do kw "COMPONENTS"; withComponents
    else if ← optKw "PATTERN" then
      -- 51.9.1 "PatternConstraint ::= PATTERN Value": the value is a cstring holding an Annex A expression
      match ← next with
      | .cstring cs =>
        match parseRegex cs with
        | .ok re => return .pattern re
        | .error e => fail s!"PATTERN: {e}"
      | _ => fail "PATTERN: only a cstring is read as the expression (a value reference is not supported yet)"
    else if ← optKw "SETTINGS" then
      match ← next with
      | .cstring cs => return .settings (settingsPairs (String.ofList (cs.map Char.ofNat)))
      | _ => fail "expected a simplestring after SETTINGS"
    else if ← optKw "INCLUDES" then return .contained (← ty) true
    else if ← optKw "MIN" then rangeRest .min
    else if ← startsType then return .contained (← ty) false
    else
      let v ← value
      if (← isSym "<") || (← isSym "..") then rangeRest (.val (.raw v))
      else return .single (.raw v)

  /-- X.680 51.4 "ValueRange", after its lower end value. -/
  partial def rangeRest (lo : Bound) : P Elem := do
    let loOpen ← optSym "<"
    sym ".."
    let hiOpen ← optSym "<"
    let hi ← if ← optKw "MAX" then pure Bound.max else pure (Bound.val (.raw (← value)))
    return .range lo loOpen hi hiOpen

  /-- X.680 51.8.5 "MultipleTypeConstraints". -/
  partial def withComponents : P Elem := do
    sym "{"
    let isPartial ← if ← isSym "..." then do let _ ← next; sym ","; pure true else pure false
    let rec items (acc : Array (String × Option Constraint × PresenceC)) :
        P (List (String × Option Constraint × PresenceC)) := do
      let nm ← lower
      let c ← if ← isSym "(" then some <$> constraint false else pure none
      let p : PresenceC ←
        if ← optKw "PRESENT" then pure .present
        else if ← optKw "ABSENT" then pure .absent
        else if ← optKw "OPTIONAL" then pure .optional
        else pure .unspecified
      let acc := acc.push (nm, c, p)
      if ← optSym "," then items acc else do sym "}"; return acc.toList
    return .withComponents isPartial (← items #[])

  /-- X.680 51.10.2: "Name=Setting" pairs separated by white-space. -/
  partial def settingsPairs (s : String) : List (String × String) :=
    (s.splitOn " ").filterMap fun w =>
      match w.splitOn "=" with
      | [a, b] => if a = "" then none else some (a, b)
      | _ => none

  /-- X.681 12.3: `{ ObjectSetSpec }`. -/
  partial def objSetBraces : P ObjSet := do
    sym "{"
    let s ← objectSetSpec
    sym "}"
    return s

  /-- X.681 12.3 "ObjectSetSpec". -/
  partial def objectSetSpec : P ObjSet := do
    if ← isSym "}" then fail "expected an element of the object set (X.681 12.3: an ObjectSetSpec is not empty)"
    if ← optSym "..." then
      if ← optSym "," then return .spec none true (some (← oelems))
      else return .spec none true none
    let root ← oelems
    if (← isSym ",") && (← isSymAt 1 "...") then
      let _ ← next; let _ ← next
      if ← optSym "," then return .spec (some root) true (some (← oelems))
      else return .spec (some root) true none
    else return .spec (some root) false none

  /-- X.681 12.10, X.680 50: set arithmetic over objects. -/
  partial def oelems : P OElems := do
    let a ← ointers
    if (← optSym "|") || (← optKw "UNION") then return .union a (← oelems) else return a

  partial def ointers : P OElems := do
    let a ← oexcept
    if (← optSym "^") || (← optKw "INTERSECTION") then return .inter a (← ointers) else return a

  partial def oexcept : P OElems := do
    let a ← oelem
    if ← optKw "EXCEPT" then return .except a (← oelem) else return a

  /-- X.681 12.10 "ObjectSetElements". -/
  partial def oelem : P OElems := do
    match ← peek with
    | some (.sym "(") => let _ ← next; let e ← oelems; sym ")"; return e
    | some (.sym "{") => return .obj (.raw (← balanced "{" "}"))
    | some (.lower s) =>
      let _ ← next
      let args ← if ← isSym "{" then actualParams else pure []
      if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .field _ => true | _ => false) then
        let _ ← next
        return .fromObjects (.spec (some (.obj (.ref none s args))) false none) (← fieldPath)
      else return .obj (.ref none s args)
    | some (.upper m) =>
      if (← isSymAt 1 ".") && (← peekAt 2).any (fun t => match t with | .lower _ => true | _ => false) then
        -- X.681 11.3 "ExternalObjectReference": `Module.object`
        let _ ← next; let _ ← next
        let n ← lower
        let args ← if ← isSym "{" then actualParams else pure []
        return .obj (.ref (some m) n args)
      let (mn, name) ← definedName
      let args ← if ← isSym "{" then actualParams else pure []
      if (← isSym ".") && (← peekAt 1).any (fun t => match t with | .field _ => true | _ => false) then
        let _ ← next
        return .fromObjects (.ref mn name args) (← fieldPath)
      else return .set (.ref mn name args)
    | _ => fail "expected an object or object set"

  /-- X.681 9.2 "ObjectClass". -/
  partial def classRef : P ClassRef := do
    if ← optKw "TYPE-IDENTIFIER" then return .typeIdentifier
    else if ← optKw "ABSTRACT-SYNTAX" then return .abstractSyntax
    else if ← optKw "CLASS" then classDefn
    else
      let (mn, name) ← definedName
      let args ← if ← isSym "{" then actualParams else pure []
      return .ref mn name args

  /-- X.681 9.3 "ObjectClassDefn", with its WITH SYNTAX (10.1). -/
  partial def classDefn : P ClassRef := do
    sym "{"
    let rec fields (acc : Array FieldSpec) : P (List FieldSpec) := do
      let f ← fieldSpec
      if ← optSym "," then fields (acc.push f) else do sym "}"; return (acc.push f).toList
    let fs ← fields #[]
    if ← optKw "WITH" then
      kw "SYNTAX"
      -- X.681 10: inside a SyntaxList, "[[" and "]]" are two brackets each (nested optional
      -- groups), not X.680 12.23–12.24's version brackets
      let ts ← balanced "{" "}"
      let ts := ts.flatMap fun t =>
        if t == .sym "[[" then [.sym "[", .sym "["] else if t == .sym "]]" then [.sym "]", .sym "]"] else [t]
      let items ← subParse (synItems "}") (.sym "{" :: ts ++ [.sym "}"])
      if let some e := syntaxListError fs items then fail e
      return .defn fs (some items)
    else return .defn fs

  /-- X.681 10.1: `{ TokenOrGroupSpec … }` up to the closing `close`. -/
  partial def synItems (close : String) : P (List SynItem) := do
    sym (if close = "}" then "{" else "[")
    let rec go (acc : Array SynItem) : P (List SynItem) := do
      match ← peek with
      | some (.sym c) =>
        if c == close then do let _ ← next; return acc.toList
        else if c == "[" then go (acc.push (.optional (← synItems "]")))
        else if c == "," then do let _ ← next; go (acc.push (.literal ","))
        else fail "unexpected symbol in WITH SYNTAX"
      | some (.field f) => let _ ← next; go (acc.push (.field ("&" ++ f)))
      | some (.upper w) => let _ ← next; go (acc.push (.literal w))
      | some (.kw w) => let _ ← next; go (acc.push (.literal w))
      | _ => fail "unexpected item in WITH SYNTAX"
    go #[]

  /-- X.681 9.4 "FieldSpec". Whether a type after a field name is a class (an object or object set
  field) is left to `Resolve`. -/
  partial def fieldSpec : P FieldSpec := do
    let f ← match ← peek with
      | some (.field f) => do let _ ← next; pure f
      | _ => fail "expected a field name"
    let name := "&" ++ f
    let isUpper := f.front.isUpper
    let endsField : P Bool := return (← isSym ",") || (← isSym "}") || (← isKw "OPTIONAL") || (← isKw "DEFAULT")
    if isUpper then
      if ← endsField then
        -- 9.5 type field
        if ← optKw "OPTIONAL" then return .typeField name (some none)
        else if ← optKw "DEFAULT" then return .typeField name (some (some (← ty)))
        else return .typeField name none
      else if (← peek).any (fun t => match t with | .field _ => true | _ => false) then
        -- 9.10 variable-type value set field
        let p ← fieldPath
        if ← optKw "OPTIONAL" then return .varValueSet name p (some none)
        else if ← optKw "DEFAULT" then do sym "{"; let c ← elementSetSpecs; sym "}"; return .varValueSet name p (some (some c))
        else return .varValueSet name p none
      else if let some c ← builtinClass then
        -- 9.12 object set field of a built-in class
        if ← optKw "OPTIONAL" then return .objectSetField name c (some none)
        else if ← optKw "DEFAULT" then do let _ ← objSetBraces; return .objectSetField name c (some none)
        else return .objectSetField name c none
      else
        -- 9.9 fixed-type value set field (or 9.12 object set field)
        let t ← ty
        if ← optKw "OPTIONAL" then return .fixedValueSet name t (some none)
        else if ← optKw "DEFAULT" then do sym "{"; let c ← elementSetSpecs; sym "}"; return .fixedValueSet name t (some (some c))
        else return .fixedValueSet name t none
    else
      if (← peek).any (fun t => match t with | .field _ => true | _ => false) then
        -- 9.8 variable-type value field
        let p ← fieldPath
        if ← optKw "OPTIONAL" then return .varValue name p (some none)
        else if ← optKw "DEFAULT" then return .varValue name p (some (some (.raw (← value))))
        else return .varValue name p none
      else if let some c ← builtinClass then
        -- 9.11 object field of a built-in class
        if ← optKw "OPTIONAL" then return .objectField name c (some none)
        else if ← optKw "DEFAULT" then do let _ ← balanced "{" "}"; return .objectField name c (some none)
        else return .objectField name c none
      else
        -- 9.6 fixed-type value field (or 9.11 object field)
        let t ← ty
        let u ← optKw "UNIQUE"
        if ← optKw "OPTIONAL" then return .fixedValue name t u (some none)
        else if ← optKw "DEFAULT" then
          -- 9.6: an identifier field has no DEFAULT
          if u then fail "UNIQUE with DEFAULT (X.681 9.6)"
          return .fixedValue name t u (some (some (.raw (← value))))
        else return .fixedValue name t u none
end

/-! ## Modules (X.680 13) -/

/-- X.683 8.3 "Parameter", its governor as lexical items (a type, a class or a dummy: `Resolve`
decides). -/
structure PreParam where
  governor : Option (List Tok)
  name : String
  /-- X.683 8.3: for a dummy with no governor, whether the body uses it as a class (`some true`),
  only otherwise (`some false`), or not known (`none`, the body is still lexical items) -/
  usage : Option Bool := none
  deriving Repr

/-- An assignment as the grammar reads it, before `Resolve` knows which names are classes. -/
inductive PreAssign where
  /-- `Name ::= Type` (16.1), or a class assignment `NAME ::= OTHER` (X.681 9.1) -/
  | type (name : String) (params : List PreParam) (t : Ty)
  /-- X.681 9.1 with CLASS, TYPE-IDENTIFIER or ABSTRACT-SYNTAX -/
  | cls (name : String) (params : List PreParam) (c : ClassRef)
  /-- `name Type ::= …`: a value (16.2) or, if `Type` is a class, an object (X.681 11.1) -/
  | valueOrObject (name : String) (params : List PreParam) (gov : Ty) (rhs : List Tok)
  /-- `Name Type ::= { … }`: a value set (16.6) or, if `Type` is a class, an object set (X.681 12.1) -/
  | setOrObjectSet (name : String) (params : List PreParam) (gov : Ty) (rhs : List Tok)

def PreAssign.name : PreAssign → String
  | .type n .. | .cls n .. | .valueOrObject n .. | .setOrObjectSet n .. => n

structure PreModule where
  name : String
  header : ModuleHeader
  imports : List (String × String)
  assigns : List PreAssign
  oid : Option (List Nat) := none
  importOids : List (String × List Nat) := []
  /-- X.680 13.13: the symbols of "SymbolsExported"; none for EXPORTS ALL or no EXPORTS -/
  exports : Option (List String) := none
  /-- X.680 13.16: the module reference of each "SymbolsFromModule", in order -/
  importMods : List String := []
  /-- X.680 53.4: the defined values exception specs name -/
  exceptionRefs : List (Option String × String) := []
  /-- X.683 8.6, which does not stop the module from being read: the assignment, and its dummy
  reference that is not used -/
  unusedDummies : List (String × String) := []

/-- X.680 13.8, 32.3: an object identifier in a module header, where no defined value may be used:
number forms, name and number forms, and the names of the top arcs and of the arcs under itu-t
and iso (Annex D). -/
def oidOfToks (ts : List Tok) : Option (List Nat) :=
  let top : List (String × Nat) :=
    [("itu-t", 0), ("ccitt", 0), ("iso", 1), ("joint-iso-itu-t", 2), ("joint-iso-ccitt", 2)]
  let second : Nat → List (String × Nat)
    | 0 => [("recommendation", 0), ("question", 1), ("administration", 2), ("network-operator", 3),
            ("identified-organization", 4), ("r-recommendation", 5)]
    | 1 => [("standard", 0), ("registration-authority", 1), ("member-body", 2),
            ("identified-organization", 3)]
    | _ => []
  let rec go (ts : List Tok) (acc : Array Nat) : Option (List Nat) :=
    match ts with
    | [] => some acc.toList
    | .number n :: rest => go rest (acc.push n)
    | .lower _ :: .sym "(" :: .number n :: .sym ")" :: rest => go rest (acc.push n)
    | .lower s :: rest =>
      let names := if acc.size = 0 then top else if acc.size = 1 then second acc[0]! else []
      match names.find? (·.1 == s) with
      | some (_, k) => go rest (acc.push k)
      | none => none
    | _ => none
  go ts #[]

/-- X.680 32.3 "ObjectIdentifierValue" as lexical items: each component a name, a number, a name with its
number, or a defined value (a lower-case name, or `Module.name`). Whether the names mean anything is
not decided here. -/
def oidToksWellFormed : List Tok → Bool
  | [] => true
  | .lower _ :: .sym "(" :: .number _ :: .sym ")" :: rest => oidToksWellFormed rest
  | .number _ :: rest | .lower _ :: rest => oidToksWellFormed rest
  | .upper _ :: .sym "." :: .lower _ :: rest => oidToksWellFormed rest
  | _ => false
termination_by ts => ts.length
decreasing_by all_goals simp_wf <;> omega

/-- X.683 8.1 "ParameterList". -/
def paramList : P (List PreParam) := do
  let ts ← balanced "{" "}"
  -- 8.3: ParameterList ::= "{" Parameter "," + "}", at least one
  if ts.isEmpty then fail "a parameter list has a parameter (X.683 8.3)"
  (splitTopCommas ts).mapM fun part =>
    match part.reverse with
    | .upper n :: .sym ":" :: gov => return ⟨some gov.reverse, n, none⟩
    | .lower n :: .sym ":" :: gov => return ⟨some gov.reverse, n, none⟩
    | [.upper n] => return ⟨none, n, none⟩
    -- 8.3 b), c): a dummy for a value or an object has a governor
    | [.lower n] => fail s!"the dummy {n} stands for a value or object and has no governor (X.683 8.3)"
    | _ => fail "a parameter is a dummy reference with an optional governor"

/-- X.683 8.6: each dummy reference is used in its scope: the parameter list (as another dummy's
governor) and what follows it. The dummies that are not. -/
def unusedDummies (ps : List PreParam) (rest : List Tok) : List String :=
  (ps.filter fun p =>
    let inGov := ps.any fun q => (q.governor.getD []).any fun t => t == .upper p.name || t == .lower p.name
    !inGov && !rest.any (fun t => t == .upper p.name || t == .lower p.name)).map (·.name)

/-- X.683 8.3: whether a type uses `nm` as a class, in `nm.&field`. -/
partial def tyUsesClass (nm : String) : Ty → Bool
  | .classField (.ref none n _) _ => n == nm
  | .sequence r e r2 | .set r e r2 =>
    let adds := (e.getD []).flatMap fun a => match a with | .one c => [c] | .group _ cs => cs
    (r ++ adds ++ r2).any fun c => match c with
      | .mk _ t _ => tyUsesClass nm t
      | .componentsOf t => tyUsesClass nm t
  | .choice r e =>
    let adds := (e.getD []).flatMap fun a => match a with | .one x => [x] | .group _ xs => xs
    (r ++ adds).any fun a => match a with | .mk _ t => tyUsesClass nm t
  | .sequenceOf t | .setOf t | .tagged _ _ t | .constrained t _ | .selection _ t => tyUsesClass nm t
  | _ => false

/-- X.683 8.3: a dummy with no governor stands for a class if the body uses it as one (or another
parameter is governed by it), and for a type otherwise. -/
def markUsage (ps : List PreParam) (t : Ty) : List PreParam :=
  ps.map fun p =>
    if p.governor.isSome then p else
      let governs := ps.any fun q => match q.governor with
        | some [.upper g] => g == p.name
        | _ => false
      { p with usage := some (tyUsesClass p.name t || governs) }

/-- What follows `Name ParameterList` in a type, class, value set or object set assignment. -/
def assignmentRest (n : String) (ps : List PreParam) : P PreAssign := do
  if ← optSym "::=" then
    if (← isKw "CLASS") || ((← isKw "TYPE-IDENTIFIER") && !(← isSymAt 1 ".")) ||
        ((← isKw "ABSTRACT-SYNTAX") && !(← isSymAt 1 ".")) then
      return .cls n ps (← classRef)
    else
      let t ← ty
      return .type n (markUsage ps t) t
  else
    let gov ← match ← builtinClass with
      | some c => pure (builtinClassTy c)
      | none => ty
    sym "::="
    if ← isSym "{" then
      let (_, ts) ← sliceOf (balanced "{" "}")
      return .setOrObjectSet n ps gov ts
    else
      -- a reference to another value set or object set
      let (_, ts) ← sliceOf tyBase
      return .setOrObjectSet n ps gov ts

/-- What follows `name ParameterList` in a value or object assignment. -/
def assignmentRestLower (n : String) (ps : List PreParam) : P PreAssign := do
  let gov ← match ← builtinClass with
    | some c => pure (builtinClassTy c)
    | none => ty
  sym "::="
  if ← isSym "{" then
    let (_, ts) ← sliceOf (balanced "{" "}")
    return .valueOrObject n ps gov ts
  else
    let (_, ts) ← sliceOf (do
      let _ ← value
      -- a parameterized object reference: `obj { … }`
      if ← isSym "{" then let _ ← balanced "{" "}"; pure () else pure ())
    return .valueOrObject n ps gov ts

/-- X.680 13.1 "Assignment", with its dummy references that X.683 8.6 says are not used (the assignment
still reads). -/
def assignment : P (PreAssign × List String) := do
  match ← peek with
  | some (.upper n) =>
    let _ ← next
    let ps ← if ← isSym "{" then paramList else pure []
    let (a, rest) ← sliceOf (assignmentRest n ps)
    return (a, unusedDummies ps rest)
  | some (.lower n) =>
    let _ ← next
    let ps ← if ← isSym "{" then paramList else pure []
    let (a, rest) ← sliceOf (assignmentRestLower n ps)
    return (a, unusedDummies ps rest)
  | _ => fail "expected an assignment"

/-- X.680 13.16 "Imports": the symbols with the module each comes from, and the object identifiers
the "AssignedIdentifier"s give (13.9). -/
partial def imports : P (List (String × String) × List (String × List Nat) × List String) := do
  let rec froms (acc : Array (String × String)) (oids : Array (String × List Nat)) (mods : Array String) :
      P (List (String × String) × List (String × List Nat) × List String) := do
    if ← isSym ";" then do let _ ← next; return (acc.toList, oids.toList, mods.toList)
    -- a SymbolList
    let rec syms (s : Array String) : P (List String) := do
      let n ← match ← next with
        | .upper n | .lower n => pure n
        | _ => fail "expected an imported symbol"
      if ← isSym "{" then do sym "{"; sym "}"
      if ← optSym "," then syms (s.push n) else return (s.push n).toList
    let ss ← syms #[]
    kw "FROM"
    let m ← upper
    -- 13.17 "AssignedIdentifier": an object identifier value, or a defined value that is not the
    -- start of the next SymbolList
    let mut oids := oids
    if ← isSym "{" then
      let ts ← balanced "{" "}"
      if !oidToksWellFormed ts then fail "expected an object identifier value (13.17, 32.3)"
      if let some o := oidOfToks ts then oids := oids.push (m, o)
    else if (← peek).any (fun t => match t with | .lower _ => true | _ => false) &&
        !(← isSymAt 1 ",") && !(← isKwAt 1 "FROM") && !(← isSymAt 1 "{") then
      let _ ← next
    if ← optKw "WITH" then let _ ← next
    froms (acc ++ (ss.map (·, m)).toArray) oids (mods.push m)
  froms #[] #[] #[]

/-- X.680 13.1 "ModuleDefinition". -/
partial def moduleDef : P PreModule := do
  let name ← upper
  let oid ← if ← isSym "{" then do
      -- 13.8 "DefinitiveIdentifier": names, numbers and names with numbers
      let ts ← balanced "{" "}"
      if !oidToksWellFormed ts then fail "expected a definitive identifier (13.8)"
      pure (oidOfToks ts)
    else pure none
  if (← peek).any (fun t => match t with | .cstring _ => true | _ => false) then let _ ← next
  kw "DEFINITIONS"
  -- 13.1 "EncodingReferenceDefault"
  if (← peek).any (fun t => match t with | .upper _ => true | _ => false) && (← isKwAt 1 "INSTRUCTIONS") then
    let _ ← next; let _ ← next
  let td : TagDefault ←
    if ← optKw "EXPLICIT" then do kw "TAGS"; pure .explicit
    else if ← optKw "IMPLICIT" then do kw "TAGS"; pure .implicit
    else if ← optKw "AUTOMATIC" then do kw "TAGS"; pure .automatic
    else pure .explicit
  let ext ← if ← optKw "EXTENSIBILITY" then do kw "IMPLIED"; pure true else pure false
  sym "::="
  kw "BEGIN"
  let hasExports ← optKw "EXPORTS"
  -- 13.1 "Exports": EXPORTS ALL ; or a SymbolList (a Symbol may be a ParameterizedReference,
  -- `Name {}`)
  let exports ← if !hasExports then pure none
    else if ← optKw "ALL" then do sym ";"; pure none
    else
      -- SymbolList ::= Symbol | SymbolList "," Symbol (13.1); the list may be empty
      let rec syms (acc : Array String) : P (List String) := do
        match ← next with
        | .upper n | .lower n =>
          if ← isSym "{" then do sym "{"; sym "}"
          if ← optSym "," then syms (acc.push n)
          else do sym ";"; return (acc.push n).toList
        | _ => fail "expected an exported symbol (13.1)"
      if ← optSym ";" then pure (some []) else pure (some (← syms #[]))
  let hasImports ← optKw "IMPORTS"
  let (imps, importOids, importMods) ← if hasImports then imports else pure ([], [], [])
  let rec body (acc : Array (PreAssign × List String)) : P (List (PreAssign × List String)) := do
    if (← isKw "END") || (← isKw "ENCODING-CONTROL") then return acc.toList
    body (acc.push (← assignment))
  let (asn, bodyToks) ← sliceOf (body #[])
  let as := asn.map (·.1)
  let unused := asn.flatMap fun (a, ds) => ds.map (a.name, ·)
  -- 53.4 "ExceptionIdentification" as a "DefinedValue": `! v` or `! M.v`
  let rec excRefs : List Tok → List (Option String × String)
    | .sym "!" :: .lower v :: rest => (none, v) :: excRefs rest
    | .sym "!" :: .upper m :: .sym "." :: .lower v :: rest => (some m, v) :: excRefs rest
    | _ :: rest => excRefs rest
    | [] => []
  -- 13.1: ModuleBody ::= Exports Imports AssignmentList | empty, and an AssignmentList has at
  -- least one Assignment
  if (hasExports || hasImports) && as.isEmpty then
    fail "expected an assignment: a module body with EXPORTS or IMPORTS has one (13.1)"
  -- 54.1 "EncodingControlSections": each an encoding reference (not TAG, 54.3; each once, 54.2)
  -- and lexical items up to END or ENCODING-CONTROL (54.4), skipped
  let rec ecs (seen : List String) : P Unit := do
    if ← optKw "ENCODING-CONTROL" then
      let r ← match ← next with
        | .upper u => pure u
        | _ => fail "expected an encoding reference (54.1)"
      if !(r.all fun c => c.isUpper || c.isDigit || c == '-') then fail "expected an encoding reference (12.25)"
      if r == "TAG" then fail "an encoding control section for TAG (54.3)"
      if seen.contains r then fail s!"two encoding control sections for {r} (54.2)"
      let rec skipEC : P Unit := do
        if (← isKw "END") || (← isKw "ENCODING-CONTROL") then return () else do let _ ← next; skipEC
      skipEC
      ecs (r :: seen)
  ecs []
  kw "END"
  return ⟨name, ⟨td, ext⟩, imps, as, oid, importOids, exports, importMods, excRefs bodyToks, unused⟩

/-- All the modules in a text. -/
partial def modules : P (List PreModule) := do
  let rec go (acc : Array PreModule) : P (List PreModule) := do
    if (← peek).isNone then return acc.toList
    go (acc.push (← moduleDef))
  go #[]

def parseModules (src : String) : Except String (List PreModule) := do
  let ls ← lexString src
  let (ms, _) ← modules.run ls
  return ms

end Asn1.Parse
