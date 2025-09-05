import Lean

open Lean Meta Elab Term Expr

def elabStringAsExpr (code : String) : TermElabM Expr := do
  -- parse the string as a syntax tree
  let stx := (Parser.runParserCategory (← getEnv) `term code).toOption.get!
  -- elaborate it into an expression
  let expr ← elabTerm stx none
  return expr

/-- Extern ML model (via webserver, or whatever.) -/
opaque letDrafter : String → IO (String × String)

elab "print_expr " code:str : tactic => do
  let code := code.getString
  let expr ← elabStringAsExpr code
  logInfo m!"{expr}"

example (x : Nat) : True := by
  print_expr "x + x"
  trivial



partial def drafter (goal : MVarId) : TermElabM (Option Expr) := do
  -- if we exceed bounds then return none
  -- goal ← introNP goal (typeArity1 goal.getType)
  -- exposeNames?
  goal.withContext do
    -- attempt closers (in parallel)
    let input := (← Meta.ppGoal goal).pretty
    let (name, draft) ← letDrafter input
    let output ← elabStringAsExpr draft
    let subgoal ← mkFreshExprMVar output
    let (x, newGoal) ← goal.note name.toName subgoal
    if let some value ← drafter subgoal.mvarId! then
      if let some body ← drafter newGoal then
        return some (.letE name.toName output value
          (body.abstract #[.fvar x]) false)
    return none
