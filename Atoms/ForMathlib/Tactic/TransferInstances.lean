import Lean.Elab.Command
import Lean.Elab.DeclNameGen
import Lean.Elab.PreDefinition.Main
import Lean.Meta.Closure
import Lean.Meta.Coe
import Lean.Meta.Eqns
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Tactic.Delta
import Lean.Meta.WrapInstance

open Lean Elab Command Term Meta

namespace Atoms.ForMathlib.TransferInstances

def toType (e : Expr) : MetaM Expr := do
  if (← whnfR (← inferType e)).isSort then return e
  let some t ← coerceToSort? e | throwError "transfer_instances: {e} is not a type"
  return t

def mkClassApp (cls : Name) (e : Expr) : MetaM Expr := do
  let t ← toType e
  let c ← mkConstWithFreshMVarLevels cls
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType c)
  let some i := bis.findIdx? (· == .default)
    | throwError "transfer_instances: `{cls}` has no explicit argument"
  unless ← isDefEq xs[i]! t do
    throwError "transfer_instances: `{cls}` does not apply to{indentExpr t}"
  for x in xs, bi in bis do
    if bi.isInstImplicit then
      x.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType x)))
  instantiateMVars (mkAppN c xs)

def withHyps {α : Type} [Inhabited α] (hyps : Array Expr) (k : Array Expr → MetaM α) :
    MetaM α := do
  let names ← hyps.mapM fun _ => mkFreshUserName `inst
  withLCtx (← getLCtx) #[] <|
    withLocalDecls (names.zipWith (fun n t => (n, .instImplicit, fun _ => pure t)) hyps) k

def solvable (goal : Expr) (hyps : Array Expr) : MetaM Bool :=
  withHyps hyps fun _ => return (← synthInstance? goal).isSome

def isAtomGoal (goal : Expr) : MetaM Bool := do
  let .const cls _ := goal.getAppFn | return false
  let bis ← forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels cls))
    fun xs _ => xs.mapM fun x => x.fvarId!.getBinderInfo
  let some i := bis.findIdx? (· == .default) | return false
  let some s := goal.getAppArgs[i]? | return false
  match ← whnfR s with
  | .fvar _ | .sort _ | .lam .. => return true
  | .proj .. => return true
  | s => match s.getAppFn with
    | .const f _ => isProjectionFn f
    | _ => return false

def etaArgs (goal : Expr) : MetaM Expr := do
  let fn := goal.getAppFn
  let info ← getFunInfo fn
  let args ← goal.getAppArgs.mapIdxM fun i a => do
    unless (info.paramInfo[i]?.map (·.binderInfo.isExplicit)).getD false do return a
    if a.isLambda then return a
    forallTelescopeReducing (← inferType a) fun xs _ => do
      if xs.isEmpty then return a
      let names := #[`x, `y, `z]
      let lctx := xs.size.fold (init := ← getLCtx) fun i _ lctx =>
        lctx.setUserName xs[i]!.fvarId! (names[i]?.getD (Name.mkSimple s!"x{i}"))
      withLCtx lctx (← getLocalInstances) do
        mkLambdaFVars xs (mkAppN a xs)
  return mkAppN fn args

def fvarPositions (e : Expr) : MetaM (List Nat) := do
  let lctx ← getLCtx
  return (collectFVars {} e).fvarIds.toList.filterMap fun id => (lctx.find? id).map (·.index)

partial def discover (goal : Expr) (hyps : Array Expr) (depth : Nat := 0) :
    MetaM (Option (Array Expr)) := do
  let goal ← instantiateMVars goal
  if ← solvable goal hyps then return some hyps
  if depth > 0 && !goal.hasExprMVar && (← isAtomGoal goal) then return some (hyps.push goal)
  if depth > 32 then return none
  forallTelescopeReducing goal fun xs body => do
    let insts ← withLCtx (← getLCtx) #[] (SynthInstance.getInstances body)
    for inst in insts.reverse do
      let s ← saveState
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType inst.val)
      if ← withTransparency .instances (isDefEq concl body) then
        let mut hs := hyps
        let mut ok := true
        for i in inst.synthOrder do
          let m := ms[i]!
          if (← instantiateMVars m).isMVar then
            let t ← instantiateMVars (← inferType m)
            if t.hasExprMVar || t.hasAnyFVar (fun id => xs.any (·.fvarId! == id)) then
              match ← withLCtx (← getLCtx) #[] (synthInstance? t) with
              | some v => m.mvarId!.assign v
              | none => ok := false; break
            else
              match ← discover t hs (depth + 1) with
              | some hs' =>
                hs := hs'
                if let some v ← withLCtx (← getLCtx) #[] (synthInstance? t) then
                  m.mvarId!.assign v
              | none => ok := false; break
        if ok then return some hs
      restoreState s
    return none

def inferAs (cls : Name) (source tyT : Expr) : MetaM Expr := do
  let val ← instantiateMVars (← wrapInstance (← synthInstance (← mkClassApp cls source)) tyT)
  unless ← isDefEq (← inferType val) tyT do
    throwError "transfer_instances: the instance of `{cls}` on{indentExpr source}\n\
      does not have type{indentExpr tyT}"
  return val

def instName (type : Expr) : TermElabM Name := do
  let base ← NameGen.mkBaseNameWithSuffix "inst" type
  liftMacroM <| mkUnusedBaseName ((← getCurrNamespace) ++ base)

def transferUnfolding (c : Expr) (cls : Name) : TermElabM Unit := do
  let some head := c.getAppFn.constName?
    | throwError "transfer_instances: expected an application of a constant"
  let t ← toType c
  let k ← whnfR (← deltaExpand t (· == head))
  if k == t then
    throwError "transfer_instances: `{head}` does not unfold in{indentExpr t}"
  let (tyT, tyK) ← withLCtx (← getLCtx) #[] do
    return (← mkClassApp cls t, ← mkClassApp cls k)
  let some hyps ← discover tyK #[]
    | throwError "transfer_instances: no instance of{indentExpr tyK}\nunder hypotheses on \
        atoms; write this instance by hand"
  let keyed ← hyps.mapM fun h => return ((← fvarPositions h).foldl max 0, ← etaArgs h)
  let hyps := (keyed.insertionSort fun a b => a.1 < b.1).map (·.2)
  let (type, value) ← withHyps hyps fun _ => do
    let val ← inferAs cls k tyT
    let r ← Closure.mkValueTypeClosure tyT val (zetaDelta := true)
    return (r.type, r.value)
  let name ← instName type
  let lparams := (collectLevelParams (collectLevelParams {} type) value).params
  addAndCompile <| .defnDecl
    { name, levelParams := lparams.toList, type, value,
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
  setReducibilityStatus name .instanceReducible
  addInstance name .global (eval_prio default)

partial def collectCalls (head : Name) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOf head then
    if acc.contains e then acc else acc.push e
  else match e with
    | .app f a => collectCalls head a (collectCalls head f acc)
    | .mdata _ b => collectCalls head b acc
    | .proj _ _ b => collectCalls head b acc
    | _ => acc

def transferRecursive (head cls : Name) : TermElabM Unit := withLCtx {} {} do
  let some unfold ← getUnfoldEqnFor? head
    | throwError "transfer_instances: `{head}` has no unfolding equation"
  let unfoldInfo ← getConstInfo unfold
  let lparams := unfoldInfo.levelParams
  let (type, value, name) ← forallTelescopeReducing unfoldInfo.type fun xs eq => do
    let some (_, lhs, rhs) := eq.eq?
      | throwError "transfer_instances: `{unfold}` is not an equation"
    let some m ← matchMatcherApp? rhs
      | throwError "transfer_instances: `{head}` is not defined by pattern matching"
    unless m.discrs.all xs.contains do
      throwError "transfer_instances: `{head}` must match on its own arguments"
    let type ← mkForallFVars xs (← mkClassApp cls lhs)
    let name ← instName type
    let localInsts ← getLocalInstances
    withLocalDeclD `rec type fun rec => do withLCtx (← getLCtx) localInsts do
      let m ← m.transform
        (onMotive := fun motiveArgs _ => mkClassApp cls (lhs.replaceFVars m.discrs motiveArgs))
        (onAlt := fun _ altType _ alt => do
          let calls := collectCalls head alt
          let hyps ← calls.mapM fun call => return (`ih, (← mkClassApp cls call))
          withLocalDeclsDND hyps fun hs => do
            withDeclNameForAuxNaming name do
              let val ← inferAs cls alt altType.headBeta
              return val.replaceFVars hs (calls.map fun call => mkAppN rec call.getAppArgs))
      let value ← mkLambdaFVars xs m.toExpr
      return (type, value.replaceFVar rec (mkConst name (lparams.map mkLevelParam)), name)
  if type.hasMVar || value.hasMVar then
    throwError "transfer_instances: the instance on `{head}` has unassigned universes"
  addPreDefinitions ({}, #[]) #[{
    ref := ← getRef, kind := .def, levelParams := lparams, modifiers := {}, declName := name,
    binders := .missing, type, value, termination := .none }]
  setReducibilityStatus name .instanceReducible
  addInstance name .global (eval_prio default)

end TransferInstances

open TransferInstances

syntax (name := transferInstances) "transfer_instances " term " with " ident+ : command

@[command_elab transferInstances] def elabTransferInstances : CommandElab
  | `(transfer_instances $c with $cls*) => do
    for cl in cls do
      runTermElabM fun _ => withRef cl do
        let e ← elabTerm c none
        synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let clsName ← realizeGlobalConstNoOverloadWithInfo cl
        if let .const head _ := e then
          if (← getUnfoldEqnFor? head).isSome && (← getEqnsFor? head).any (·.size > 1) then
            return ← transferRecursive head clsName
        transferUnfolding e clsName
  | _ => throwUnsupportedSyntax

end Atoms.ForMathlib
