import Lean

open Lean Meta Elab Term Expr

def applyOptions : Options → Options :=
  (pp.proofs.set · false |>
  (pp.motives.all.set · true |>
  (pp.coercions.types.set · true |>
  (pp.unicode.fun.set · true))))

def elabStringAsExpr (code : String) : TermElabM Expr := do
  -- parse the string as a syntax tree
  let stx := (Parser.runParserCategory (← getEnv) `term code).toOption.get!
  -- elaborate it into an expression
  let expr ← elabTerm stx none
  return expr

def send {α β : Type} [ToJson α] [FromJson β] (req : α) (url : String) : IO β := do
  let reqStr := (toJson req).pretty 99999999999999999
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["-X", "POST", url, "-H", "accept: application/json", "-H", "Content-Type: application/json", "-d", reqStr]
  }
  if out.exitCode != 0 then
     throw $ IO.userError s!"Request failed. Please check if the server is up at `{url}`."
  let some json := Json.parse out.stdout |>.toOption
    | throw $ IO.userError "Failed to parse response"
  let some res := (fromJson? json : Except String β) |>.toOption
    | throw $ IO.userError "Failed to parse response"
  return res

-- /-- Extern ML model (via webserver, or whatever.) -/
-- def letDrafter (tacticState : String) : IO (String × String) := send (Json.mkObj [("input_text", tacticState)]) "http://localhost:8000/generate"

def jsonToHashMap (s : String) : Except String (Std.HashMap String String) :=
  match Json.parse s with
  | Except.ok j =>
    match j.getObj? with
    | .ok kvs =>
      -- Build the HashMap from the list of key-value pairs
      let map := kvs.fold (init := Std.HashMap.emptyWithCapacity) fun acc k v =>
        match v.getStr? with
        | .ok strVal => acc.insert k strVal
        | _        => acc  -- skip non-string values
      Except.ok map
    | _ => Except.error "JSON is not an object"
  | Except.error err => Except.error err

#eval jsonToHashMap "{ \"a\":\"b\", \"c\":\"d\"}"


/-- Extern ML-style function: given a key, return (key, value) from JSON file -/
def letDrafter (tacticState : String) (filePath : String := "data.json") : IO (String × String) := do
  let content ← IO.FS.readFile filePath
  match jsonToHashMap content with
  | Except.ok map =>
    IO.println map.toList.length
    IO.println tacticState
    match map.get? tacticState with
    | some val => pure ("q", val)
    | none     => pure ("failed could not find tactic state", "sorry")
  | Except.error e => pure ("failed map invalid" ++ e, "sorry")


-- elab "try_drafter " : tactic => do
--   let expr ← elabStringAsExpr code
--   logInfo m!"{expr}"


syntax (name := draft) "draft" : tactic

open Meta Tactic
@[tactic draft] def evalDraft : Tactic
| `(tactic| draft) => do
  withMainContext do
    let goal ← getMainGoal
    let ty ← goal.getType
    -- make a *fresh metavariable* with the same type, but no userName
    let fresh ← mkFreshExprMVar ty
    let freshId := fresh.mvarId!
    let input := (← MonadWithOptions.withOptions applyOptions do Meta.ppGoal freshId).pretty
    let (name, draft) ← letDrafter input
    let _ ← admitGoal goal
    logInfo m!"let {name} : {draft} := ?{name}"
    -- let output ← elabStringAsExpr draft
    -- let subgoal ← mkFreshExprMVar output
    -- let (x, newGoal) ← goal.note name.toName subgoal
    -- replaceMainGoal [subgoal.mvarId!, newGoal]
| _ => throwUnsupportedSyntax

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
