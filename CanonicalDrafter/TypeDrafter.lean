import Lean
import Aesop

open Lean Meta Elab Term Expr Meta Tactic

namespace Typewriter

def elabStringAsExpr (code : String) : TermElabM Expr := do
  let stx := (Parser.runParserCategory (← getEnv) `term code).toOption.get!
  withoutErrToSorry do elabTermAndSynthesize stx none

def printForce (s : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk "output.txt" IO.FS.Mode.append
  handle.putStrLn s
  handle.flush

structure RpcChannel where
  channel : Std.Channel.Sync MessageData
  lastMessage : IO.Ref MessageData
deriving TypeName

def RpcChannel.send (c : RpcChannel) (msg : MessageData) : IO Unit := do
  c.channel.send msg
  c.lastMessage.set msg

def RpcChannel.new : IO RpcChannel := do
  let chan ← Std.Channel.Sync.new (α := MessageData)
  let ref ← IO.mkRef ("" : MessageData)
  return { channel := chan, lastMessage := ref }

partial def userTerm (goal : MVarId) (draftIn draftOut draftErr : RpcChannel) : TermElabM (String × Expr) := do
  let type ← draftIn.channel.recv
  let (name, draft) : String × String := ("test", (← type.format).pretty)
  try
    return (name, ← elabStringAsExpr draft)
  catch e =>
    draftErr.send e.toMessageData
    return ← userTerm goal draftIn draftOut draftErr

partial def drafter (goal : MVarId) (draftIn draftOut draftErr : RpcChannel) : TermElabM (Option Expr) := do
  -- if we exceed bounds then return none
  -- let goal ← introNP goal (typeArity1 goal.getType)
  -- exposeNames?
  goal.withContext do
    let mdc := MessageDataContext.mk (← getEnv) (← getMCtx) (← getLCtx) (← getOptions)
    draftOut.send (MessageData.withContext mdc goal)
    let duplicate ← mkFreshExprMVar (← goal.getType)
    let remaining ←
      try
        let (remaining, _stats) ← Aesop.search duplicate.mvarId!
        pure remaining
      catch _ =>
        pure #[duplicate.mvarId!]

    if remaining.isEmpty then
      return ← instantiateMVars duplicate -- return the `aesop` syntax

    let (name, output) ← userTerm goal draftIn draftOut draftErr
    let subgoal ← mkFreshExprMVar output
    let (x, newGoal) ← goal.note name.toName subgoal
    if let some value ← drafter subgoal.mvarId! draftIn draftOut draftErr then
      if let some body ← drafter newGoal draftIn draftOut draftErr then
        return some (.letE name.toName output value
          (body.abstract #[.fvar x]) false)
    return none
  -- attempt closers (in parallel)


open Server RequestM

structure SendParams where
  pos : Lsp.Position
  text : String
  channel : Server.WithRpcRef RpcChannel
deriving Server.RpcEncodable

@[server_rpc_method]
def send (params : SendParams) : RequestM (RequestTask Json) := do
  withWaitFindSnapAtPos params.pos fun snap => runTermElabM snap do
    params.channel.val.send params.text
    return default

structure RecvParams where
  pos : Lsp.Position
  channel : Server.WithRpcRef RpcChannel
deriving Server.RpcEncodable

structure RpcMessageData where
  response : Server.WithRpcRef MessageData
deriving Lean.Server.RpcEncodable

@[server_rpc_method]
def recv (params : RecvParams) : RequestM (RequestTask RpcMessageData) := do
  withWaitFindSnapAtPos params.pos fun snap => runTermElabM snap do
    return ⟨← Server.WithRpcRef.mk (← params.channel.val.channel.recv)⟩

@[server_rpc_method]
def last (params : RecvParams) : RequestM (RequestTask RpcMessageData) := do
  withWaitFindSnapAtPos params.pos fun snap => runTermElabM snap do
    return ⟨← Server.WithRpcRef.mk (← params.channel.val.lastMessage.get)⟩

@[widget_module]
def refineWidget : Widget.Module where
  javascript := include_str "TypeDrafter.js"

open Lean Meta Elab Tactic

elab "typewrite" : tactic => do
  let draftIn ← RpcChannel.new
  let draftOut ← RpcChannel.new
  let draftErr ← RpcChannel.new
  let channelRefs ← [draftIn, draftOut, draftErr].mapM (fun c => Server.WithRpcRef.mk c)
  let emptyMessage ← Server.WithRpcRef.mk ("" : MessageData)
  Lean.Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef)
    (props := do
      let emptyMessage ← Server.RpcEncodable.rpcEncode (RpcMessageData.mk emptyMessage)
      let encoded ← channelRefs.mapM (fun c => Server.RpcEncodable.rpcEncode c)
      pure (Json.mkObj (("empty", emptyMessage) :: (["draftIn", "draftOut", "draftErr"].zip encoded))))

  let goal ← getMainGoal
  goal.admit
  let duplicate := (← mkFreshExprMVar (← goal.getType)).mvarId!
  let ctxCore : Core.Context ← monadLift (read : CoreM Core.Context)
  let sCore : Core.State ← monadLift (get : CoreM Core.State)
  let ctxMeta : Meta.Context ← monadLift (read : MetaM _)
  let sMeta : Meta.State ← monadLift (get : MetaM _)
  let ctx ← readThe Term.Context
  let _ ← IO.asTask (Lean.Elab.Term.TermElabM.toIO (drafter duplicate draftIn draftOut draftErr) ctxCore sCore ctxMeta sMeta ctx {})

example (a b : Nat) : a + b = b + a := by
  typewrite
