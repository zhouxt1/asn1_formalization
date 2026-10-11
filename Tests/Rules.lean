import Asn1.X680.Checker

/-! The rules the checker reports against the fields of `Env.Valid` (`Rule.status`). -/

open Lean Meta Asn1.X680

/-- The structures whose fields are the rules of the spec. -/
def specStructs : List Name :=
  [``TypeOk, ``SiteOk, ``ClassOk, ``ClassSyntaxOk, ``ObjOk, ``ObjSetOk, ``Module.ValidAt, ``Env.Valid]

/-- The fields that only quantify the others. -/
def specWrappers : List Name :=
  [``SiteOk.types, ``Module.ValidAt.types, ``Env.Valid.params, ``Module.ValidAt.classes,
   ``Module.ValidAt.classSyntax, ``Module.ValidAt.objects, ``Module.ValidAt.objectSets, ``Env.Valid.modules]

/-- The fields the grammar decides: a module that breaks one does not read (SPEC-GAP.md section 3). -/
def grammarDecided : List Name :=
  [``ClassSyntaxOk.uniqueNoDefault, ``ClassSyntaxOk.syntaxFields, ``ClassSyntaxOk.optionalGroups]

-- each field a rule names is a field of the spec; each rule of the spec is named by a rule of the
-- checker, or decided by the grammar
run_meta do
  let env ← getEnv
  let named := Rule.all.flatMap fun r => match r.status with
    | .valid fs | .partly fs _ => fs
    | _ => []
  for f in named do
    match env.getProjectionFnInfo? f with
    | some i =>
      unless specStructs.contains i.ctorName.getPrefix do throwError "{f} is not a field of the spec"
    | none => throwError "{f} is not a field"
  let fields := specStructs.flatMap fun s => (getStructureFields env s).toList.map (s ++ ·)
  let undecided := fields.filter fun f =>
    !named.contains f && !specWrappers.contains f && !grammarDecided.contains f
  unless undecided.isEmpty do throwError "fields no rule decides: {undecided}"

-- no rule is left out of the spec
#guard Rule.all.all fun r => r.status != .gap

-- the messages are distinct, so a report names its rule
#guard (Rule.all.map (Rule.text "d")).Nodup
