import Lean

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab

private partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p::ps, oldHyps, h::newHyps => do
    let pt ← inferType p
    let t ← inferType h
    --dbg_trace "{pt} {t}"
    if (← isDefEq pt t) then
      matchHyps ps [] (oldHyps ++ newHyps)
    else
      matchHyps (p::ps) (h::oldHyps) newHyps
  | [], _, _    => pure true
  | _::_, _, [] => pure false

-- from Lean.Server.Completion
private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRec declName
  <||> isMatcher declName

initialize findCache : IO.Ref (Option (Std.HashMap HeadIndex (Array Name))) ← IO.mkRef none

def findType (t : Expr) : TermElabM Unit := withReducible do
  let env ← getEnv
  let headMap ← match (← findCache.get) with
    | some headMap => pure headMap
    | none => profileitM Exception "#find: init cache" (← getOptions) do
      let mut headMap := Std.HashMap.empty
      -- TODO: `ForIn` for `SMap`
      for (_, c) in env.constants.map₁.toList do
        if (← isBlackListed c.name) then
          continue
        let (_, _, ty) ← forallMetaTelescopeReducing c.type
        let head := ty.toHeadIndex
        headMap := headMap.insert head (headMap.findD head #[] |>.push c.name)
      findCache.set headMap
      pure headMap

  let t ← instantiateMVars t
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat ← abstractMVars t

  let mut numFound := 0
  for n in headMap.findD head #[] ++ env.constants.map₂.toList.toArray.map (·.1) do
    let c := env.find? n |>.get!
    let us ← mkFreshLevelMVars c.numLevelParams
    let cTy ← c.instantiateTypeLevelParams us
    let found ← forallTelescopeReducing cTy fun cParams cTy' => do
      let pat ← pat.expr.instantiateLevelParamsArray pat.paramNames (← mkFreshLevelMVars pat.numMVars).toArray
      let (_, _, pat) ← lambdaMetaTelescope pat
      let (patParams, _, pat) ← forallMetaTelescopeReducing pat
      --dbg_trace "{cTy'}\n{pat}"
      isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList
    if found then
      numFound := numFound + 1
      if numFound > 20 then
        logInfo m!"maximum number of search results reached"
        break
      logInfo m!"{n}: {cTy}"

open Lean.Elab.Command in
/-
The `find` command finds definitions & lemmas using pattern matching on the type. For instance:
```lean
#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
```
Inside tactic proofs, the `find` tactic can be used instead.
-/
elab "#find" t:term : command =>
  liftTermElabM none do
    let t ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    findType t

--#find _ + _ = _ + _
--#find _ + _ = _ + _
--#find ?n + _ = _ + ?n
--#find (_ : Nat) + _ = _ + _
--#find Nat → Nat
--#find _ ≤ _ → _ + _ ≤ _ + _  -- TODO

open Lean.Elab.Tactic
/-
Display theorems (and definitions) whose result type matches the current goal, i.e. which should be `apply`able.
```lean
example : True := by find
```
`find` will not affect the goal by itself and should be removed from the finished proof.

For a command that takes the type to search for as an argument, see `#find`, which is also available as a tactic.
-/
elab "find" : tactic => do
  findType (← getMainTarget)

/-
Tactic version of the `#find` command. See also the `find` tactic to search for theorems matching the current goal.
-/
elab "#find" t:term : tactic => do
  let t ← Term.elabTerm t none
  Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
  findType t
