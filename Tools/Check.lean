import Asn1.Parse.Report
import Asn1.Parse.Values
import Asn1.X680.Checker
import Asn1.X690.Decode
import Asn1.X691.Decode
import Asn1.X691.Enc

open Asn1.Parse Asn1.X680

/-- A file's text: UTF-8, or, if it is not valid UTF-8, its bytes as Latin-1 characters (some
published modules have Latin-1 in their comments). -/
def readText (f : String) : IO String := do
  let bs ← IO.FS.readBinFile f
  match String.fromUTF8? bs with
  | some s => return s
  | none => return String.ofList (bs.toList.map fun b => Char.ofNat b.toNat)

/-- `asn1check lex FILE...`, `asn1check parse FILE...`: lex or parse each file and report. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "lex" :: files =>
    let mut bad := 0
    for f in files do
      let s ← readText f
      match lexString s with
      | .ok ls => IO.println s!"{f}: {ls.size} lexical items"
      | .error e => IO.println s!"{f}: ERROR {e}"; bad := bad + 1
    return (if bad = 0 then 0 else 1)
  | "parse" :: files =>
    let mut bad := 0
    for f in files do
      let s ← readText f
      match parseModules s with
      | .ok ms =>
        let desc := ms.map fun m => s!"{m.name} ({m.assigns.length} assignments, {m.imports.length} imports)"
        IO.println s!"{f}: {desc}"
      | .error e => IO.println s!"{f}: ERROR {e}"; bad := bad + 1
    return (if bad = 0 then 0 else 1)
  | "resolve" :: rest =>
    let verbose := rest.contains "-v"
    let files := rest.filter (· != "-v")
    let lim : Nat := if verbose then 1000000 else 20
    let mut mods : List PreModule := []
    for f in files do
      let s ← readText f
      match parseModules s with
      | .ok ms =>
        -- X.680 13.7, 13.10: module names are used once in a sphere of interest. Each file is one;
        -- the files of a corpus unit may hold several editions of a module
        if let some nm := (moduleNamesTwice (ms.map fun m => (m.name, m.oid))).head? then
          IO.println s!"{f}: ERROR {nm}: {Rule.moduleNameTwice.text ""}"; return 1
        mods := mods ++ ms
      | .error e => IO.println s!"{f}: ERROR {e}"; return 1
    -- X.680 3.8.5: an ASN.1 specification is a collection of one or more modules
    if mods.isEmpty then
      IO.println s!"{files.headD ""}: ERROR no ASN.1 module (X.680 3.8.5: a specification is one or more modules)"
      return 1
    let (E0, ws0) := resolveAll mods
    let (E, ws1) := readValues E0
    let ws := ws0 ++ ws1
    for m in E do
      IO.println s!"{m.name}: {m.types.length} types, {m.values.length} values, {m.classes.length} classes, {m.objects.length} objects, {m.objectSets.length} object sets, {m.params.length} parameterized"
    let c := report E
    IO.println s!"unread: {c.rawVals} values, {c.rawObjs} objects, {c.rawArgs} actual parameters"
    for u in c.unreadAt.toList.take lim do IO.println s!"  in {u}"
    IO.println s!"type references that do not resolve: {c.unresolved.size}"
    for u in c.unresolved.toList.take lim do IO.println s!"  {u}"
    IO.println s!"diagnostics: {ws.size}"
    for w in ws.toList.take lim do IO.println s!"  {w}"
    let vs := checkEnv E 60
    IO.println s!"validity rules broken: {vs.length}"
    for v in vs.take lim do IO.println s!"  {v.mod}.{v.name}: {v.text}"
    return (if ws.isEmpty && c.unresolved.isEmpty && vs.isEmpty then 0 else 1)
  | ["rules"] =>
    -- the rules `resolve` reports, and where each stands against `Env.Valid` (SPEC-GAP.md)
    let short (f : Lean.Name) : String := (toString f).replace "Asn1.X680." ""
    for r in Rule.all do
      let st := match r.status with
        | .valid fs => s!"valid {fs.map short}"
        | .partly fs miss => s!"partly {fs.map short}; beyond: {miss}"
        | .gap => "gap"
        | .notation => "notation"
      IO.println s!"{(reprStr r).replace "Asn1.X680.Rule." ""}\t{st}\t{r.text "d"}"
    return 0
  | "decode" :: prof :: target :: rest =>
    -- `asn1check decode (ber|cer|der) Module.Type [-v] MODULE-FILE... -- DATA-FILE...`: decode each
    -- data file as one encoding of the type (X.690), with the relation's decoder
    let verbose := rest.contains "-v"
    let json := rest.contains "--json"
    -- PER only: the complete encoding may be followed by other octets (X.691 7.9)
    let prefixMode := rest.contains "--prefix"
    let rest := rest.filter fun a => a != "-v" && a != "--json" && a != "--prefix"
    let (mfiles, dfiles) := (rest.takeWhile (· != "--"), (rest.dropWhile (· != "--")).drop 1)
    -- X.690 profiles, or the four PER variants (X.691 7)
    let per : Option Asn1.X691.Variant := match prof with
      | "aper" => some ⟨true, false⟩ | "uper" => some ⟨false, false⟩
      | "caper" => some ⟨true, true⟩ | "cuper" => some ⟨false, true⟩
      | _ => none
    let p : Asn1.X690.Profile ← match prof with
      | "ber" => pure .ber | "cer" => pure .cer | "der" => pure .der
      | _ => if per.isSome then pure .ber else do
        IO.println "profile: ber, cer, der, aper, uper, caper or cuper"; return 2
    let mut mods : List PreModule := []
    for f in mfiles do
      match parseModules (← readText f) with
      | .ok ms => mods := mods ++ ms
      | .error e => IO.println s!"{f}: ERROR {e}"; return 2
    let (E0, _) := resolveAll mods
    let (E, _) := readValues E0
    let (mn, tn) := match target.splitOn "." with
      | [m, t] => (m, t)
      | _ => ("", target)
    let some m := E.find? (·.name == mn) | IO.println s!"no module {mn}"; return 2
    let mut bad := 0
    for f in dfiles do
      let bs ← IO.FS.readBinFile f
      let os : Asn1.Octets := bs.toList.map fun b => ⟨b.toNat, b.toNat_lt⟩
      let r : Except String (Asn1.X680.Val × Nat) := match per with
        | some v => if prefixMode then Asn1.X691.decodePrefix E v 400 m (.ref tn) os
          else (Asn1.X691.decode E v 400 m (.ref tn) os).map (·, 0)
        | none => (Asn1.X690.decode E p 400 m (.ref tn) os).map (·, 0)
      match r with
      | .ok (v, k) => IO.println s!"{f}: OK{if k > 0 then s!" (+{k} octets)" else ""}{if json then " " ++ Asn1.X690.showJson v else if verbose then " " ++ Asn1.X690.showVal v else ""}"
      | .error e => IO.println s!"{f}: REJECT {e}"; bad := bad + 1
    return (if bad = 0 then 0 else 1)
  | "roundtrip" :: prof :: target :: rest =>
    -- `asn1check roundtrip (uper|aper|cuper|caper) Module.Type MODULE-FILE... -- DATA-FILE...`:
    -- decode each data file with the PER decoder, encode the value with the PER encoder (same
    -- variant), and compare the octets
    let (mfiles, dfiles) := (rest.takeWhile (· != "--"), (rest.dropWhile (· != "--")).drop 1)
    let v : Asn1.X691.Variant ← match prof with
      | "aper" => pure ⟨true, false⟩ | "uper" => pure ⟨false, false⟩
      | "caper" => pure ⟨true, true⟩ | "cuper" => pure ⟨false, true⟩
      | _ => do IO.println "variant: aper, uper, caper or cuper"; return 2
    let mut mods : List PreModule := []
    for f in mfiles do
      match parseModules (← readText f) with
      | .ok ms => mods := mods ++ ms
      | .error e => IO.println s!"{f}: ERROR {e}"; return 2
    let (E0, _) := resolveAll mods
    let (E, _) := readValues E0
    let (mn, tn) := match target.splitOn "." with
      | [m, t] => (m, t)
      | _ => ("", target)
    let some m := E.find? (·.name == mn) | IO.println s!"no module {mn}"; return 2
    let mut bad := 0
    for f in dfiles do
      let bs ← IO.FS.readBinFile f
      let os : Asn1.Octets := bs.toList.map fun b => ⟨b.toNat, b.toNat_lt⟩
      match Asn1.X691.decode E v 400 m (.ref tn) os with
      | .error e => IO.println s!"{f}: REJECT decode: {e}"; bad := bad + 1
      | .ok x => match Asn1.X691.encode E v 400 m (.ref tn) x with
        | .error e => IO.println s!"{f}: REJECT encode: {e}"; bad := bad + 1
        | .ok os' =>
          if os' == os then IO.println s!"{f}: SAME"
          else
            let i := ((os.zip os').takeWhile fun (a, b) => a == b).length
            IO.println s!"{f}: DIFF {os.length} vs {os'.length} octets, first difference at octet {i}"
            bad := bad + 1
    return (if bad = 0 then 0 else 1)
  | _ => IO.println "usage: asn1check (lex|parse|resolve) FILE... | asn1check rules | asn1check roundtrip (aper|uper|caper|cuper) Module.Type MODULE... -- DATA... | asn1check decode (ber|cer|der|aper|uper|caper|cuper) Module.Type [-v] [--json] MODULE... -- DATA..."; return 2
