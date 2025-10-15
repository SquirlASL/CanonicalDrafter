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

def printForce (s : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk "output.txt" IO.FS.Mode.append
  handle.putStrLn s
  handle.flush


unsafe def drafter (goal : MVarId) (draftIn draftOut draftErr : Std.Channel.Sync String): TermElabM (Option Expr) := do
  -- if we exceed bounds then return none
  -- let goal ← introNP goal (typeArity1 goal.getType)
  -- exposeNames?
  goal.withContext do
    let duplicate := ← mkFreshExprMVar (← goal.getType)
    let (remaining, stats) ← Aesop.search duplicate.mvarId!
    if remaining.isEmpty then
      return ← instantiateMVars duplicate -- return the `aesop` syntax

    -- attempt closers (in parallel)
    -- let input := (← Meta.ppGoal goal).pretty
    let type ← draftIn.recv
    let (name, draft) : String × String := ("test", type) -- ← letDrafter input
    printForce "wee"
    try
      let output ← elabStringAsExpr draft
      let subgoal ← mkFreshExprMVar output
      let (x, newGoal) ← goal.note name.toName subgoal
      if let some value ← drafter subgoal.mvarId! draftIn draftOut draftErr then
        if let some body ← drafter newGoal draftIn draftOut draftErr then
          return some (.letE name.toName output value
            (body.abstract #[.fvar x]) false)
    catch e =>
      printForce (← e.toMessageData.format).pretty
    draftOut.send ("goal: ")
    printForce "womp"
    return none

structure RpcChannel where
  channel : Std.Channel.Sync String
deriving TypeName

open Server RequestM

structure SendParams where
  pos : Lsp.Position
  text : String
  channel : Server.WithRpcRef RpcChannel
deriving Server.RpcEncodable

@[server_rpc_method]
def send (params : SendParams) : RequestM (RequestTask Json) := do
  withWaitFindSnapAtPos params.pos fun snap => runTermElabM snap do
    params.channel.val.channel.send params.text
    return default

structure RecvParams where
  pos : Lsp.Position
  channel : Server.WithRpcRef RpcChannel
deriving Server.RpcEncodable

structure RpcString where
  response : String
deriving Lean.Server.RpcEncodable

@[server_rpc_method]
def recv (params : RecvParams) : RequestM (RequestTask RpcString) := do
  withWaitFindSnapAtPos params.pos fun snap => runTermElabM snap do
    printForce "recv"
    let temp ← params.channel.val.channel.recv
    printForce temp
    return ⟨temp⟩

@[widget_module]
def refineWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { useRpcSession, EditorContext, EnvPosContext } from '@leanprover/infoview';

export default function (props) {
  const pos = React.useContext(EnvPosContext);
  const rs = useRpcSession();

  const [value, setValue] = React.useState('');

  React.useEffect(() => {
    let cancelled = false;
    async function poll(){
      while (!cancelled) {
        const res = await rs.call('Typewriter.recv', { pos: pos, channel: props.draftOut });
        setValue(res.response);
      }
    }
    poll();

    return () => {
      cancelled = true;
    };
  }, []);

  const onEnter = async (e) => {
    e.preventDefault();
    await rs.call('Typewriter.send', { pos: pos, text: value, channel: props.draftIn });
  };

  return React.createElement(
    'form',
    { onSubmit: onEnter },
    React.createElement('input', {
      type: 'text',
      value: value,
      onChange: (e) => setValue(e.target.value),
      placeholder: 'Type something and press Enter…',
    })
  );
}
"

open Lean Meta Elab Tactic

unsafe def elabTypeWriteImpl : TacticM Unit := do
  let draftIn ← Std.Channel.Sync.new (α := String)
  let draftOut ← Std.Channel.Sync.new (α := String)
  let draftErr ← Std.Channel.Sync.new (α := String)
  let channelRefs ← [draftIn, draftOut, draftErr].mapM (fun c => Server.WithRpcRef.mk (RpcChannel.mk c))
  Lean.Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef)
    (props := do
      let encoded ← channelRefs.mapM (fun c => Server.RpcEncodable.rpcEncode c)
      pure (Json.mkObj (["draftIn", "draftOut", "draftErr"].zip encoded)))

  let goal ← getMainGoal
  goal.admit
  let ctxCore : Core.Context ← monadLift (read : CoreM Core.Context)
  let sCore : Core.State ← monadLift (get : CoreM Core.State)
  let ctxMeta : Meta.Context ← monadLift (read : MetaM _)
  let sMeta : Meta.State ← monadLift (get : MetaM _)
  let ctx ← readThe Term.Context
  let x ← IO.asTask (Lean.Elab.Term.TermElabM.toIO (drafter goal draftIn draftOut draftErr) ctxCore sCore ctxMeta sMeta ctx {})


@[implemented_by elabTypeWriteImpl]
opaque elabTypeWrite : TacticM Unit


elab "typewrite" : tactic => elabTypeWrite

example : 0 + n = n ^ n := by
  typewrite
