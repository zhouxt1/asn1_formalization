import Asn1.Parse.Resolve

/-!
# Reading value notation against its governor (X.680 14.8, 17.7, Annex C.6)

What `{ a, b }`, `5` or `"…"` denotes depends on the type it is a value of. Once the modules are
assembled, the governor of each value notation is known: the component's type for a DEFAULT, the
parent type for a constraint, the field's type for an object setting, the dummy's governor for an
actual parameter. `readVal` reads the notation as a value of the governor's built-in type
(`builtin`). A value reference stays a reference (`Val.ref`), which `evalVal` follows.
-/

namespace Asn1.Parse

open Asn1.X680

/-- How far the front end follows references. -/
def fuel : Nat := 60

/-- X.680 Annex D, 32.3: the names of the top arcs of the OID tree, and of the arcs under them
that value notation may use without a number (32.7, 32.8). -/
def oidTopArcs : List (String × Nat) :=
  [("itu-t", 0), ("ccitt", 0), ("iso", 1), ("joint-iso-itu-t", 2), ("joint-iso-ccitt", 2)]

/-- X.660 Annex A (to which X.680 32.7 refers): under `itu-t recommendation`, the series letters `a`
to `z` are the arcs 1 to 26. -/
def oidSeriesArc (s : String) : Option Nat :=
  match s.toList with
  | [c] => if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 1) else none
  | _ => none

def oidSecondArcs : Nat → List (String × Nat)
  | 0 => [("recommendation", 0), ("question", 1), ("administration", 2), ("network-operator", 3),
          ("identified-organization", 4), ("r-recommendation", 5)]
  | 1 => [("standard", 0), ("registration-authority", 1), ("member-body", 2), ("identified-organization", 3)]
  | _ => []

abbrev V := StateT (Array String) Id

def vwarn (msg : String) : V Unit := modify (·.push msg)

/-- X.680 21.6: a realnumber, as the base 10 value it denotes. -/
def realOf (neg : Bool) (int : Nat) (frac : String) (exp : Int) : RealVal :=
  let digits := frac.toList.map fun c => c.toNat - '0'.toNat
  let m : Int := digits.foldl (fun a d => 10 * a + d) (int : Int)
  let e : Int := exp - digits.length
  let q : ℚ := (m : ℚ) * (10 : ℚ) ^ e
  if m = 0 then (if neg then .minusZero else .plusZero)
  else .num .ten (if neg then -q else q)

/-- X.680 22.9, 23.3: an hstring's semi-octets as bits, leading bit first. -/
def hexBits (hs : List Nat) : List Bool :=
  hs.flatMap fun h => [h / 8 % 2 == 1, h / 4 % 2 == 1, h / 2 % 2 == 1, h % 2 == 1]

/-- X.680 23.3: octets from bits, a final partial octet padded with 0 bits. -/
def bitsToOctets (bs : List Bool) : List (Fin 256) :=
  let rec go (bs : List Bool) (fuel : Nat) : List (Fin 256) :=
    match fuel with
    | 0 => []
    | k + 1 =>
      if bs.isEmpty then [] else
      let o := (bs.take 8 ++ List.replicate (8 - (bs.take 8).length) false).foldl (fun a b => 2 * a + (if b then 1 else 0)) 0
      ⟨o % 256, Nat.mod_lt _ (by decide)⟩ :: go (bs.drop 8) k
  go bs bs.length

/-- The characters of a cstring for a register-defined type: the ISO 646 characters as cells of
registration 6, SPACE and DELETE (X.690 Table 3 designates registration 6 as G0). -/
def regCharsOf (cs : List Nat) : List RegChar :=
  cs.map fun c => if c = 0x20 then .space else if c = 0x7F then .delete else .cell "6" [c]

mutual
  /-- X.680 17.7: the value notation `r` as a value of `gov`, the type read in scope `sc`. The value
  notation's own references are read in `vsc` (where it is written), `sc` if not given. -/
  partial def readVal (E : Env) (sc : Scope) (gov : Ty) (r : RawVal) (vsc : Option Scope := none) :
      V (Option Val) := do
    let rs := vsc.getD sc
    let bt := builtin E fuel sc gov
    -- a comma separates two items in every value notation written in braces (12.37, 22.9, 25.x, 26.3, 28.3)
    if let .braces items := r then
      if items.length ≥ 2 && items.any (·.isEmpty) then
        vwarn s!"{sc.mod.name}: an empty item between commas in a value"
        return none
    match r, bt with
    -- 14.6 and 16.2: references (an identifier that names nothing of the type)
    | .ext m s, _ => return some (.ref (some m) s [])
    | .fromObject o p, _ => return some (.fromObject (.spec (some (.obj (.ref none o []))) false none) p)
    | .ident s, some (_, .enumerated root ext) =>
      if (root ++ ext.getD []).any (·.1 == s) then return some (.enum s) else return some (.ref none s [])
    | .ident s, some (_, .integer named) =>
      match named.find? (·.1 == s) with
      | some (_, k) => return some (.int k)
      | none => return some (.ref none s [])
    | .ident s, _ => return some (.ref none s [])
    -- 18
    | .kw "TRUE", some (_, .boolean) => return some (.bool true)
    | .kw "FALSE", some (_, .boolean) => return some (.bool false)
    -- 19
    | .num i, some (_, .integer _) => return some (.int i)
    -- 21
    | .num i, some (_, .real) => return some (.real (realOf (i < 0) i.natAbs "" 0))
    | .real neg i f e, some (_, .real) =>
      -- the number is computed as a rational: an exponent this large is not (it overflows Nat.pow)
      if e.natAbs > 100000 then do vwarn s!"{sc.mod.name}: a REAL exponent too large to read"; return none
      else return some (.real (realOf neg i f e))
    | .kw "PLUS-INFINITY", some (_, .real) => return some (.real .plusInfinity)
    | .kw "MINUS-INFINITY", some (_, .real) => return some (.real .minusInfinity)
    | .kw "NOT-A-NUMBER", some (_, .real) => return some (.real .notANumber)
    -- 21.5: a value of the associated type, `{ mantissa m, base 2 or 10, exponent e }`
    | .braces [[.ident "mantissa", .num m], [.ident "base", .num b], [.ident "exponent", .num e]], some (_, .real) =>
      if b ≠ 2 ∧ b ≠ 10 then do vwarn s!"{sc.mod.name}: a REAL base other than 2 or 10"; return none
      else if e.natAbs > 100000 then do vwarn s!"{sc.mod.name}: a REAL exponent too large to read"; return none
      else if m = 0 then return some (.real .plusZero)
      else return some (.real (.num (if b = 2 then .two else .ten) ((m : ℚ) * (b : ℚ) ^ e)))
    -- 22
    | .bstring bs, some (_, .bitString _) => return some (.bits bs)
    | .hstring hs, some (_, .bitString _) => return some (.bits (hexBits hs))
    | .braces items, some (_, .bitString named) =>
      -- 22.9: the named bits that are 1
      let ks := items.filterMap fun it => match it with
        | [.ident s] => (named.find? (·.1 == s)).map (·.2)
        | _ => none
      if ks.length ≠ items.length then do vwarn s!"{sc.mod.name}: a named bit that the type does not name"; return none
      let len := (ks.foldl max 0) + (if ks.isEmpty then 0 else 1)
      -- the value is a list of `len` bits: a named bit this far out is not
      if len > 100000 then do vwarn s!"{sc.mod.name}: a named bit too large to read"; return none
      return some (.bits ((List.range len).map fun i => ks.contains i))
    -- 23
    | .hstring hs, some (_, .octetString) => return some (.octets (bitsToOctets (hexBits hs)))
    | .bstring bs, some (_, .octetString) => return some (.octets (bitsToOctets bs))
    -- 24
    | .kw "NULL", some (_, .null) => return some .null
    -- 32, 33
    | .braces [run], some (_, .objectIdentifier) =>
      match ← oidArcs E rs run true with
      -- 32.11 NOTE, 32.6 NOTE: an object identifier value has at least two arcs (X.660)
      | some a => if a.length < 2 then do vwarn s!"{sc.mod.name}: an object identifier value of fewer than two arcs (32.11)"; return none
                  else return some (.oid a)
      | none => return none
    | .braces [run], some (_, .relativeOid) => (oidArcs E rs run false).map (·.map .oid)
    -- 34, 35: "/a/b"
    | .cstring cs, some (_, .oidIri) | .cstring cs, some (_, .relativeOidIri) =>
      let s := String.ofList (cs.map Char.ofNat)
      return some (.iri ((s.splitOn "/").filter (· ≠ "")))
    -- 38
    | .cstring cs, some (_, .time) | .cstring cs, some (_, .date) | .cstring cs, some (_, .timeOfDay)
    | .cstring cs, some (_, .dateTime) | .cstring cs, some (_, .duration) =>
      match Notation.parse (cs.map Char.ofNat) with
      | some t => return some (.time t)
      | none => do vwarn s!"{sc.mod.name}: not TIME value notation"; return none
    -- 41, 46, 47, 48
    | .cstring cs, some (_, .restricted k) =>
      return some (if k.isRegister then .regChars (regCharsOf cs) else .chars cs)
    -- 41.8: a "Quadruple", a "Tuple" or a "CharacterStringList"
    | .braces items, some (_, .restricted k) =>
      match ← charsOfBraces E rs items with
      | some cs => return some (if k.isRegister then .regChars (regCharsOf cs) else .chars cs)
      | none => do vwarn s!"{sc.mod.name}: not character string value notation"; return none
    | .cstring cs, some (_, .generalizedTime) | .cstring cs, some (_, .utcTime) => return some (.chars cs)
    | .cstring cs, some (_, .objectDescriptor) => return some (.regChars (regCharsOf cs))
    -- 25, 27: `{ name value, … }`, in the type's order
    | .braces items, some (sc', .sequence ro e r2) | .braces items, some (sc', .set ro e r2) =>
      let es := entries E fuel sc' ro e r2
      let mut cs : Array (Nat × String × Val) := #[]
      for it in items do
        match it with
        | [.ident nm, v] =>
          match es.zipIdx.find? (fun (en, _) => en.name == nm) with
          | some (en, i) => match ← readVal E en.scope en.ty v (some rs) with
            | some w => cs := cs.push (i, nm, w)
            | none => return none
          | none => do vwarn s!"{sc.mod.name}: no component {nm}"; return none
        | [] => pure ()
        | _ => do vwarn s!"{sc.mod.name}: a component value is `name value`"; return none
      -- 25.11, 25.13 (Semantics.SeqShape): the root's mandatory components are all present, and
      -- an addition group's are present when any component of the group is
      let present (en : Entry) := cs.any (·.2.1 == en.name)
      let missing := es.filter fun en => en.presence.isMandatory && !present en &&
        match en.addition with
        | none => true
        | some i => es.any fun f => f.addition == some i && present f
      if let some en := missing.head? then
        vwarn s!"{sc.mod.name}: a value without the mandatory component {en.name} (25.11, 25.13)"
        return none
      let sorted := cs.toList.mergeSort (fun a b => a.1 ≤ b.1)
      return some (.seq (sorted.map fun (_, nm, w) => (nm, w)))
    -- 26, 28
    | .braces items, some (sc', .sequenceOf el) | .braces items, some (sc', .setOf el) =>
      let isSet := match bt with | some (_, .setOf _) => true | _ => false
      -- 26.3: a "ValueList" or a "NamedValueList", not both
      if items.any (·.length == 1) && items.any (·.length == 2) then
        vwarn s!"{sc.mod.name}: named and unnamed elements in one value (26.3)"; return none
      let mut vs : Array Val := #[]
      for it in items do
        let v? : Option RawVal := match it with
          | [v] => some v
          | [.ident _, v] => some v   -- 26.4: a named value
          | _ => none
        match v? with
        | some v => match ← readVal E sc' el v (some rs) with
          | some w => vs := vs.push w
          | none => return none
        | none => do vwarn s!"{sc.mod.name}: an element value is a value or `name value`"; return none
      return some (if isSet then .setOf vs.toList else .seqOf vs.toList)
    -- 29
    | .choice a v, some (sc', .choice ro ext) =>
      match findAlt (choiceAlts ro ext) a with
      | some alt => return (← readVal E sc' alt.ty v (some rs)).map (.choice a ·)
      | none => do vwarn s!"{sc.mod.name}: no alternative {a}"; return none
    -- 36.8, 37.7, 44.7: the associated type's value notation
    -- X.681 14.6: an open type's value is a value of the type written before it
    | .typed ts v, some (_, .openType) =>
      match (subParse ty ts).run #[] with
      | .ok (t, _) => return (← readVal E rs t v (some rs)).map (.open_ t ·)
      | .error e => do vwarn s!"{sc.mod.name}: {e}"; return none
    | .braces _, some (_, .embeddedPdv) => readVal E (.ofModule assocModule) embeddedPdvAssoc r (some rs)
    | .braces _, some (_, .external) => readVal E (.ofModule assocModule) externalAssoc r (some rs)
    | .braces _, some (_, .characterString) => readVal E (.ofModule assocModule) characterStringAssoc r (some rs)
    | _, none => do vwarn s!"{sc.mod.name}: the governor of a value does not resolve"; return none
    | _, _ => do vwarn s!"{sc.mod.name}: value notation {repr r} for a type it does not fit"; return none

  /-- X.680 41.8, 41.12–41.14: the characters of `{ … }` character string notation: a "Quadruple"
  `{group, plane, row, cell}` (the ISO/IEC 10646 code point), a "Tuple" `{column, row}` (an IA5String
  cell, 41.14), or a "CharacterStringList" of cstrings, quadruples, tuples and value references. -/
  partial def charsOfBraces (E : Env) (rs : Scope) (items : List (List RawVal)) : V (Option (List Nat)) := do
    match items with
    | [[.num g], [.num p], [.num r], [.num c]] =>
      return some [((g.toNat * 256 + p.toNat) * 256 + r.toNat) * 256 + c.toNat]
    | [[.num col], [.num row]] => return some [col.toNat * 16 + row.toNat]
    | _ =>
      let mut out : Array Nat := #[]
      for it in items do
        match it with
        | [.cstring cs] => out := out ++ cs.toArray
        | [.braces inner] => match ← charsOfBraces E rs inner with
          | some cs => out := out ++ cs.toArray
          | none => return none
        | [.ident s] =>
          -- a value reference to a character string value
          match resolveVal E fuel rs none s [] with
          | some (sc', .raw (.cstring cs)) => let _ := sc'; out := out ++ cs.toArray
          | some (sc', .raw (.braces inner)) => match ← charsOfBraces E sc' inner with
            | some cs => out := out ++ cs.toArray
            | none => return none
          | some (_, .chars cs) => out := out ++ cs.toArray
          | _ => return none
        | _ => return none
      return some out.toList

  /-- X.680 32.3: the arcs of an object identifier value; a leading value reference stands for its
  arcs (32.4 "DefinedValue"). -/
  partial def oidArcs (E : Env) (sc : Scope) (run : List RawVal) (absolute : Bool) : V (Option (List Nat)) := do
    let mut arcs : Array Nat := #[]
    let mut first := true
    for x in run do
      match x with
      | .num i | .nameNum _ (.num i) =>
        -- 32.3 "NumberForm": a non-negative number
        if i < 0 then
          vwarn s!"{sc.mod.name}: an object identifier component is not negative"
          return none
        arcs := arcs.push i.toNat
      | .ident s =>
        if first && absolute then
          match oidTopArcs.find? (·.1 == s) with
          | some (_, k) => arcs := arcs.push k
          | none =>
            match ← oidOfRef E sc s with
            | some pre => arcs := arcs ++ pre.toArray
            | none => do vwarn s!"{sc.mod.name}: {s} is not an object identifier value"; return none
        else
          let named : Option Nat :=
            if arcs.size = 1 then ((oidSecondArcs arcs[0]!).find? (·.1 == s)).map (·.2)
            else if arcs.size = 2 && arcs[0]! = 0 && arcs[1]! = 0 then oidSeriesArc s
            else none
          match named with
          | some k => arcs := arcs.push k
          | none =>
            -- 32.3 "DefinedValue": after the first component, a relative object identifier value
            match ← oidOfRef E sc s with
            | some more => arcs := arcs ++ more.toArray
            | none => do vwarn s!"{sc.mod.name}: {s} is neither an arc name nor a relative object identifier value"; return none
      | _ => do vwarn s!"{sc.mod.name}: not an object identifier component"; return none
      first := false
    return some arcs.toList

  /-- The arcs of a value reference in an object identifier value: an object identifier or relative
  object identifier value (32.3 "DefinedValue"), or a non-negative integer (32.3 "NumberForm"). -/
  partial def oidOfRef (E : Env) (sc : Scope) (s : String) : V (Option (List Nat)) := do
    match resolveVal E fuel sc none s [] with
    -- a reference to another value
    | some (sc', .raw (.ident s')) => oidOfRef E sc' s'
    | some (sc', .raw r) =>
      let t : Ty := match (sc'.mod.values.find? (·.1 == s)) with
        | some (_, t, _) => t
        | none => .objectIdentifier
      match ← readVal E sc' t r with
      | some (.oid a) => return some a
      | some (.int k) => return if k ≥ 0 then some [k.toNat] else none
      | _ => return none
    | some (_, .oid a) => return some a
    | _ => return none
end

/-! ## Reading every value in the modules -/

/-- X.683 9.5: an actual parameter for a dummy governed by a type is a value of that type. -/
def vArgs (E : Env) (sc : Scope) (mn : Option String) (name : String) (args : List Arg) : V (List Arg) := do
  if args.isEmpty then return args
  let ps : Option (Scope × List Param) := (resolveIn E fuel sc mn name [.type .null]
    (fun _ _ _ => none) (fun _ => none)
    (fun pa => match pa with
      | .type _ ps _ | .value _ ps _ _ | .valueSet _ ps _ _ | .cls _ ps _ | .obj _ ps _ _
      | .objSet _ ps _ _ => some (ps, ps))).map fun (s, ps) => (s, ps)
  match ps with
  | some (psc, ps) =>
    (ps.zip args).mapM fun (p, a) => do
      match a, p.governor with
      | .value (.raw r), some (.type t) =>
        match ← readVal E (.ofModule psc.mod) t r (some sc) with
        | some v => return .value v
        | none => return a
      | a, _ => return a
  | none => return args

structure VCtx where
  E : Env
  /-- the scope that type notation is read in -/
  sc : Scope

mutual
  /-- The values inside a type, each read against its governor. -/
  partial def vTy (E : Env) (sc : Scope) : Ty → V Ty
    | .sequence r e r2 => return .sequence (← r.mapM (vComp E sc)) (← e.mapM (·.mapM (vExtAdd E sc))) (← r2.mapM (vComp E sc))
    | .set r e r2 => return .set (← r.mapM (vComp E sc)) (← e.mapM (·.mapM (vExtAdd E sc))) (← r2.mapM (vComp E sc))
    | .sequenceOf t => return .sequenceOf (← vTy E sc t)
    | .setOf t => return .setOf (← vTy E sc t)
    | .choice r e => return .choice (← r.mapM (vAlt E sc)) (← e.mapM (·.mapM (vAltAdd E sc)))
    | .selection n t => return .selection n (← vTy E sc t)
    | .tagged tg k t => return .tagged tg k (← vTy E sc t)
    | .constrained t c => do let t' ← vTy E sc t; return .constrained t' (← vCons E sc t' c)
    | .paramRef mn n args => return .paramRef mn n (← vArgs E sc mn n args)
    | t => return t

  partial def vComp (E : Env) (sc : Scope) : Comp → V Comp
    | .mk n t (.default_ (.raw r)) => do
      let t' ← vTy E sc t
      match ← readVal E sc t' r with
      | some v => return .mk n t' (.default_ v)
      | none => return .mk n t' (.default_ (.raw r))
    | .mk n t p => return .mk n (← vTy E sc t) p
    | .componentsOf t => return .componentsOf (← vTy E sc t)

  partial def vExtAdd (E : Env) (sc : Scope) : ExtAdd → V ExtAdd
    | .one c => return .one (← vComp E sc c)
    | .group v cs => return .group v (← cs.mapM (vComp E sc))

  partial def vAlt (E : Env) (sc : Scope) : Alt → V Alt
    | .mk n t => return .mk n (← vTy E sc t)

  partial def vAltAdd (E : Env) (sc : Scope) : AltAdd → V AltAdd
    | .one a => return .one (← vAlt E sc a)
    | .group v as => return .group v (← as.mapM (vAlt E sc))

  partial def vVal (E : Env) (sc : Scope) (gov : Ty) : Val → V Val
    | .raw r => do
      match ← readVal E sc gov r with
      | some v => return v
      | none => return .raw r
    | v => return v

  /-- A constraint on parent type `pt`. -/
  partial def vCons (E : Env) (sc : Scope) (pt : Ty) : Constraint → V Constraint
    | .mk r ext a => return .mk (← vES E sc pt r) ext (← a.mapM (vES E sc pt))
    | .contents t e => do
      return .contents (← t.mapM (vTy E sc)) (← e.mapM (vVal E sc .objectIdentifier))
    | c => return c

  partial def vES (E : Env) (sc : Scope) (pt : Ty) : ElemSet → V ElemSet
    | .elem e => return .elem (← vElem E sc pt e)
    | .union a b => return .union (← vES E sc pt a) (← vES E sc pt b)
    | .inter a b => return .inter (← vES E sc pt a) (← vES E sc pt b)
    | .except a b => return .except (← vES E sc pt a) (← vES E sc pt b)
    | .allExcept b => return .allExcept (← vES E sc pt b)

  partial def vElem (E : Env) (sc : Scope) (pt : Ty) : Elem → V Elem
    | .single v => return .single (← vVal E sc pt v)
    | .range lo lo' hi hi' => do
      let lo ← match lo with | .val v => pure (Bound.val (← vVal E sc pt v)) | b => pure b
      let hi ← match hi with | .val v => pure (Bound.val (← vVal E sc pt v)) | b => pure b
      return .range lo lo' hi hi'
    -- 51.6: on an open type, a type in parentheses is a "TypeConstraint", which the grammar does not
    -- tell from a "ContainedSubtype". With INCLUDES it is a "ContainedSubtype", which Table 11 does
    -- not allow there
    | .contained t inc => match builtin E fuel sc pt with
      | some (_, .openType) => if inc then return .contained (← vTy E sc t) true else return .typeC (← vTy E sc t)
      | _ => return .contained (← vTy E sc t) inc
    | .typeC t => return .typeC (← vTy E sc t)
    -- 51.5.3: the size constraint is on INTEGER (0..MAX)
    | .size c => return .size (← vCons E sc (.integer []) c)
    -- 51.7.2: the alphabet constraint is on the parent type
    | .from_ c => return .from_ (← vCons E sc pt c)
    | .withComponent c => do
      match builtin E fuel sc pt with
      | some (sc', .sequenceOf et) | some (sc', .setOf et) => return .withComponent (← vCons E sc' et c)
      | _ => return .withComponent c
    | .withComponents p ncs => do
      let comps := structComps E fuel sc pt
      return .withComponents p (← ncs.mapM fun (n, c, pr) => do
        match c, comps.find? (·.1 == n) with
        | some c, some (_, csc, ct) => return (n, some (← vCons E csc ct c), pr)
        | c, _ => return (n, c, pr))
    | e => return e
end

/-- A type written in scope `fsc`, made readable from another scope: a reference by name becomes an
external reference to `fsc`'s module (14.6). Inner references resolve where their types are written. -/
def qualifyTy (fsc : Scope) : Ty → Ty
  | .ref n => if (fsc.bound n).isSome then .ref n else .extRef fsc.mod.name n
  | .constrained t c => .constrained (qualifyTy fsc t) c
  | .tagged tg k t => .tagged tg k (qualifyTy fsc t)
  | t => t

mutual
  /-- An object's settings: a value field's value is a value of the field's type (X.681 11.8); a
  variable-type value field's, of the type the object gives its type field (11.9); an object or
  object set field's objects are of the field's class (11.11, 11.12). -/
  partial def vObj (E : Env) (sc : Scope) (cls : ClassRef) : Obj → V Obj
    | .defn ss => do
      let cf := classFields E fuel sc cls
      let typeOf (f : String) : Option Ty := ss.findSome? fun (n, st) => match st with
        | .type t => if n == f then some t else none
        | _ => none
      let ss ← ss.mapM fun (n, st) => do
        let fspec := cf.bind (fun c => fieldAt E fuel c [n])
        match st, fspec with
        | .value v, _ =>
          let gov : Option (Scope × Ty) := match fspec with
            | some (fsc, .fixedValue _ t _ _) => some (fsc, t)
            | some (_, .varValue _ [tf] _) => (typeOf tf).map (sc, ·)
            | _ => none
          match gov, v with
          | some (gsc, t), .raw r => match ← readVal E gsc t r (some sc) with
            | some w => return (n, .value w)
            | none => return (n, .value v)
          | _, _ => return (n, .value v)
        | .type t, _ => return (n, .type (← vTy E sc t))
        -- 11.10: a value set setting of a fixed-type value set field is a subtype of the field's type
        | .valueSet c, some (fsc, .fixedValueSet _ t _) => return (n, .valueSet (← vCons E sc (qualifyTy fsc t) c))
        | .valueSet c, some (_, .varValueSet _ [tf] _) => match typeOf tf with
          | some t => return (n, .valueSet (← vCons E sc t c))
          | none => return (n, .valueSet c)
        | .object o, some (fsc, .objectField _ c _) => return (n, .object (← vObj E sc (qualifyClass fsc.mod.name c) o))
        | .objectSet os, some (fsc, .objectSetField _ c _) => return (n, .objectSet (← vObjSet E sc (qualifyClass fsc.mod.name c) os))
        | st, _ => return (n, st)
      return .defn ss
    -- X.683 9.5: the actual parameters of a parameterized object
    | .ref mn n args => return .ref mn n (← vArgs E sc mn n args)
    | o => return o

  partial def vObjSet (E : Env) (sc : Scope) (cls : ClassRef) : ObjSet → V ObjSet
    | .spec r e a => do
      let rec oe : OElems → V OElems
        | .obj o => return .obj (← vObj E sc cls o)
        | .union a b => return .union (← oe a) (← oe b)
        | .inter a b => return .inter (← oe a) (← oe b)
        | .except a b => return .except (← oe a) (← oe b)
        -- X.683 9.5: the actual parameters of a parameterized object set, and nested sets
        | .set s => return .set (← vObjSet E sc cls s)
        | x => return x
      return .spec (← r.mapM oe) e (← a.mapM oe)
    | .ref mn n args => return .ref mn n (← vArgs E sc mn n args)
end

/-- A class definition's types and DEFAULT settings: a fixed-type value field's DEFAULT is a value of
its type (X.681 9.6), a fixed-type value set field's a subset of it (9.9). -/
def vClass (E : Env) (sc : Scope) : ClassRef → V ClassRef
  | .defn fs ws => do
    let fs ← fs.mapM fun f => match f with
      | .fixedValue nm t u opt => do
        let t' ← vTy E sc t
        let opt' ← match opt with
          | some (some (.raw r)) => do
            match ← readVal E sc t' r with
            | some v => pure (some (some v))
            | none => pure opt
          | o => pure o
        pure (FieldSpec.fixedValue nm t' u opt')
      | .fixedValueSet nm t opt => do
        let t' ← vTy E sc t
        pure (.fixedValueSet nm t' (← opt.mapM (·.mapM (vCons E sc t'))))
      | .typeField nm (some (some t)) => do pure (.typeField nm (some (some (← vTy E sc t))))
      | f => pure f
    pure (.defn fs ws)
  | c => pure c

/-- Every value notation in the modules, read. -/
def readValues (E : Env) : Env × Array String :=
  let step (m : Module) : V Module := do
    let sc := Scope.ofModule m
    let types ← m.types.mapM fun (n, t) => do return (n, ← vTy E sc t)
    let values ← m.values.mapM fun (n, t, v) => do let t' ← vTy E sc t; return (n, t', ← vVal E sc t' v)
    let classes ← m.classes.mapM fun (n, c) => do return (n, ← vClass E sc c)
    let objects ← m.objects.mapM fun (n, c, o) => do return (n, c, ← vObj E sc c o)
    let objectSets ← m.objectSets.mapM fun (n, c, s) => do return (n, c, ← vObjSet E sc c s)
    -- inside a parameterized assignment, a dummy is a reference like any other (X.683 8.4)
    let params ← m.params.mapM fun pa => do
      match pa with
      | .type n ps t => return ParamAssign.type n ps (← vTy E sc t)
      | .value n ps t v => return .value n ps t (← vVal E sc t v)
      | .valueSet n ps t c => do let t' ← vTy E sc t; return .valueSet n ps t' (← vCons E sc t' c)
      | .obj n ps c o => return .obj n ps c (← vObj E sc c o)
      | .objSet n ps c os => return .objSet n ps c (← vObjSet E sc c os)
      | .cls n ps c => return .cls n ps (← vClass E sc c)
    return { m with types, values, classes, objects, objectSets, params }
  let (ms, ws) := (E.mapM step).run #[]
  (ms, ws)

end Asn1.Parse
