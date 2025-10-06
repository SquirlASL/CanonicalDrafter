import Lean
import Aesop

open Lean Meta Elab Term Expr Meta Tactic

namespace Typewriter

def elabStringAsExpr (code : String) : TermElabM Expr := do
  -- parse the string as a syntax tree
  let stx := (Parser.runParserCategory (← getEnv) `term code).toOption.get!
  -- elaborate it into an expression
  withoutErrToSorry do
    let expr ← elabTerm stx none
    return expr

unsafe def drafter (goal : MVarId) (ref : IO.Ref String) : TermElabM (Option Expr) := do
  -- if we exceed bounds then return none
  -- goal ← introNP goal (typeArity1 goal.getType)
  -- exposeNames?
  goal.withContext do
    let duplicate := ← mkFreshExprMVar (← goal.getType)
    let (remaining, stats) ← Aesop.search duplicate.mvarId!
    if remaining.isEmpty then
      return ← instantiateMVars duplicate -- return the `aesop` syntax

    -- attempt closers (in parallel)
    let input := (← Meta.ppGoal goal).pretty
    let (name, draft) : String × String := ("test", ← ref.take) -- ← letDrafter input
    let output ← elabStringAsExpr draft
    let subgoal ← mkFreshExprMVar output
    let (x, newGoal) ← goal.note name.toName subgoal
    if let some value ← drafter subgoal.mvarId! ref then
      if let some body ← drafter newGoal ref then
        return some (.letE name.toName output value
          (body.abstract #[.fvar x]) false)
    return none

#check TryThis.tryThisWidget

def printForce (s : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk "output.txt" IO.FS.Mode.append
  handle.putStrLn s
  handle.flush

structure RpcData where
  ref : IO.Ref String
deriving TypeName

structure Params where
  pos : Lsp.Position
  text : String
  rpcData : Server.WithRpcRef RpcData
deriving Server.RpcEncodable

open Server RequestM in
@[server_rpc_method]
def sendText (params : Params) : RequestM (RequestTask Json) := do
  withWaitFindSnapAtPos params.pos fun snap => do runTermElabM snap do
    let _ ← printForce params.text
    params.rpcData.val.ref.set params.text
    return default

@[widget_module]
def refineWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { useRpcSession, EditorContext, EnvPosContext } from '@leanprover/infoview';

export default function (props) {
  const pos = React.useContext(EnvPosContext);
  const rs = useRpcSession();

  const [value, setValue] = React.useState(\"\");

  const onEnter = async (e) => {
    e.preventDefault();
    const result = await rs.call('Typewriter.sendText', { pos: props.pos, text: value, rpcData: props.rpcData });
    setValue(\"\");
  };

  return React.createElement(
    \"form\",
    { onSubmit: onEnter },
    React.createElement(\"input\", {
      type: \"text\",
      value: value,
      onChange: (e) => setValue(e.target.value),
      placeholder: \"Type something and press Enter…\",
    })
  );
}
"


unsafe def elabTypeWriteImpl : TacticM Unit := do
  let ref ← IO.mkRef ""
  let _ ← ref.take
  let x ← Server.WithRpcRef.mk (RpcData.mk ref)
  Lean.Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef)
    (props := do
      let rpcData ← Server.RpcEncodable.rpcEncode x
      pure (Json.mkObj [("rpcData", rpcData)]))

  let goal ← getMainGoal
  if let some expr ← drafter goal ref then
    goal.assign expr
    replaceMainGoal []

@[implemented_by elabTypeWriteImpl]
opaque elabTypeWrite : TacticM Unit


elab "typewrite" : tactic => elabTypeWrite

example : 0 + n = n ^ n := by
  typewrite
