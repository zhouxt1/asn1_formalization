import Asn1.Parse.Resolve

/-!
# What the front end left unread, and references that do not resolve

A report on resolved modules, for testing the front end and the specification on real schemas.
-/

namespace Asn1.Parse

open Asn1.X680

structure Counts where
  rawVals : Nat := 0
  rawObjs : Nat := 0
  rawArgs : Nat := 0
  /-- type references that do not resolve, by module -/
  unresolved : Array String := #[]
  /-- where unread notation is: module.assignment -/
  unreadAt : Array String := #[]

/-- Walk the notation of module `m` read in scope `sc`, counting what is unread and checking type
references. `dummies` are the dummy references in scope, which are not resolved here. -/
partial def walkTy (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : Ty → Counts
  | .sequence r e r2 | .set r e r2 =>
    let cs := r ++ (e.getD []).flatMap ExtAdd.comps ++ r2
    cs.foldl (fun c x => match x with
      | .mk _ t p => walkPresence (walkTy E sc dummies c t) p
      | .componentsOf t => walkTy E sc dummies c t) c
  | .sequenceOf t | .setOf t | .selection _ t | .tagged _ _ t => walkTy E sc dummies c t
  | .choice r e => (choiceAlts r e).foldl (fun c a => walkTy E sc dummies c a.ty) c
  | .constrained t k => walkCons E sc dummies (walkTy E sc dummies c t) k
  | .ref n =>
    if dummies.contains n || (resolveTy E 40 sc none n []).isSome then c
    else { c with unresolved := c.unresolved.push s!"{sc.mod.name}: {n}" }
  | .extRef m n =>
    if (resolveTy E 40 sc (some m) n []).isSome then c
    else { c with unresolved := c.unresolved.push s!"{sc.mod.name}: {m}.{n}" }
  | .paramRef mn n args =>
    let c := args.foldl (walkArg E sc dummies) c
    if (resolveTy E 40 sc mn n args).isSome then c
    else { c with unresolved := c.unresolved.push s!"{sc.mod.name}: {n}{"{…}"}" }
  | .classField cls _ | .instanceOf cls => walkClass E sc dummies c cls
  | .fromObjects s _ => walkObjSet E sc dummies c s
  | _ => c
where
  walkPresence (c : Counts) : Presence → Counts
    | .default_ v => walkVal c v
    | _ => c
  walkVal (c : Counts) : Val → Counts
    | .raw _ => { c with rawVals := c.rawVals + 1 }
    | _ => c
  walkArg (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : Arg → Counts
    | .raw _ => { c with rawArgs := c.rawArgs + 1 }
    | .type t => walkTy E sc dummies c t
    | .value v => walkVal c v
    | .valueSet k => walkCons E sc dummies c k
    | .objSet s => walkObjSet E sc dummies c s
    | .obj o => walkObj E sc dummies c o
    | .cls k => walkClass E sc dummies c k
  walkCons (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : Constraint → Counts
    | .mk r _ a => (a.map (walkES E sc dummies (walkES E sc dummies c r))).getD (walkES E sc dummies c r)
    | .table os _ => walkObjSet E sc dummies c os
    | .contents t e => let c := (t.map (walkTy E sc dummies c)).getD c; (e.map (walkVal c)).getD c
    | .userDefined => c
  walkES (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : ElemSet → Counts
    | .elem e => walkElem E sc dummies c e
    | .union a b | .inter a b | .except a b => walkES E sc dummies (walkES E sc dummies c a) b
    | .allExcept b => walkES E sc dummies c b
  walkElem (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : Elem → Counts
    | .single v => walkVal c v
    | .contained t _ | .typeC t => walkTy E sc dummies c t
    | .range lo _ hi _ =>
      let c := match lo with | .val v => walkVal c v | _ => c
      match hi with | .val v => walkVal c v | _ => c
    | .size k | .from_ k | .withComponent k => walkCons E sc dummies c k
    | .withComponents _ ncs => ncs.foldl (fun c (_, k, _) => (k.map (walkCons E sc dummies c)).getD c) c
    | _ => c
  walkClass (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : ClassRef → Counts
    | .ref _ _ args => args.foldl (walkArg E sc dummies) c
    | _ => c
  walkObjSet (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : ObjSet → Counts
    | .ref _ _ args => args.foldl (walkArg E sc dummies) c
    | .spec r _ a =>
      let c := (r.map (walkOE E sc dummies c)).getD c
      (a.map (walkOE E sc dummies c)).getD c
  walkOE (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : OElems → Counts
    | .obj o => walkObj E sc dummies c o
    | .set s | .fromObjects s _ => walkObjSet E sc dummies c s
    | .union a b | .inter a b | .except a b => walkOE E sc dummies (walkOE E sc dummies c a) b
  walkObj (E : Env) (sc : Scope) (dummies : List String) (c : Counts) : Obj → Counts
    | .raw _ => { c with rawObjs := c.rawObjs + 1 }
    | .defn ss => ss.foldl (fun c (_, st) => match st with
        | .type t => walkTy E sc dummies c t
        | .value v => walkVal c v
        | .valueSet k => walkCons E sc dummies c k
        | .object o => walkObj E sc dummies c o
        | .objectSet s => walkObjSet E sc dummies c s) c
    | .ref _ _ args => args.foldl (walkArg E sc dummies) c
    | .fromObject o _ => walkObj E sc dummies c o

/-- The report for an environment. -/
def report (E : Env) : Counts := Id.run do
  let mut c : Counts := {}
  let total (c : Counts) := c.rawVals + c.rawObjs + c.rawArgs
  let mark (before : Nat) (where_ : String) (c : Counts) : Counts :=
    if total c > before then { c with unreadAt := c.unreadAt.push where_ } else c
  for m in E do
    let sc := Scope.ofModule m
    for (n, t) in m.types do let b := total c; c := mark b s!"{m.name}.{n}" (walkTy E sc [] c t)
    for (n, t, v) in m.values do let b := total c; c := mark b s!"{m.name}.{n}" (walkTy.walkVal (walkTy E sc [] c t) v)
    for (n, _, o) in m.objects do let b := total c; c := mark b s!"{m.name}.{n}" (walkTy.walkObj E sc [] c o)
    for (n, _, s) in m.objectSets do let b := total c; c := mark b s!"{m.name}.{n}" (walkTy.walkObjSet E sc [] c s)
    for p in m.params do
      let ds := match p with
        | .type _ ps _ | .value _ ps _ _ | .valueSet _ ps _ _ | .cls _ ps _ | .obj _ ps _ _
        | .objSet _ ps _ _ => ps.map (·.name)
      c := match p with
        | .type _ _ t => walkTy E sc ds c t
        | .value _ _ t v => walkTy.walkVal (walkTy E sc ds c t) v
        | .valueSet _ _ t k => walkTy.walkCons E sc ds (walkTy E sc ds c t) k
        | .obj _ _ _ o => walkTy.walkObj E sc ds c o
        | .objSet _ _ _ s => walkTy.walkObjSet E sc ds c s
        | .cls _ _ _ => c
  return c

end Asn1.Parse
