import Lean
import Lake

-- example test
-- lake env lean --run ../CanonicalDrafter/ExtractData.lean Mathlib/Combinatorics/Hindman.lean
-- cat .lake/build/ir/Mathlib/Combinatorics/Hindman.ast.json
-- https://github.com/lean-dojo/LeanDojo/issues/247

-- based on https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean from LeanDojo
-- unlike LeanDojo we only care about tracing tactics so we remove commands and premises to reduce storage cost and increase speed.

open Lean

def subscriptToNum (c : Char) : Char :=
  match c with
  | '₀' => '0'
  | '₁' => '1'
  | '₂' => '2'
  | '₃' => '3'
  | '₄' => '4'
  | '₅' => '5'
  | '₆' => '6'
  | '₇' => '7'
  | '₈' => '8'
  | '₉' => '9'
  | _   => c

def increment (s : String) : String :=
  let pre := s.dropRightWhile (fun c => isNumericSubscript c)
  let num := s.takeRightWhile (fun c => isNumericSubscript c)
  pre ++ ((num.map (subscriptToNum)).toNat?.getD 0 + 1).toSubscriptString

partial def disambiguate (s : String) : MetaM String := do
  if ((← getLCtx).findFromUserName? s.toName).isSome then disambiguate (increment s) else return s

def desiredName (userName : Name) (tactic : String) : String :=
  match userName.getRoot with
  | .str _ s => s
  | _ => ((tactic.splitOn).firstM (fun s : String =>
    if !s.isEmpty && isIdFirst (s.get 0) && (s.toSubstring.drop 1).all isIdRest then some s else none
  )).getD "this"

open Lean Elab System

set_option maxHeartbeats 2000000  -- 10x the default maxHeartbeats.


instance : ToJson Substring where
  toJson s := toJson s.toString

instance : ToJson String.Pos where
  toJson n := toJson n.1

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax
deriving instance ToJson for Position


namespace LeanDojo


/--
The trace of a tactic.
-/
structure TacticTrace where
  goalsBefore: Array String
  goalsAfter: Array String
  pos: String.Pos      -- Start position of the tactic.
  endPos: String.Pos   -- End position of the tactic.
  tactic: String       -- The actual tactic text.
deriving ToJson

/-
 Given a current goal tactic state string the next relevant sublemmas/hypothesis to be "have drafted"
-/
structure HaveDraft where
  tactic : String
  name : String
  goal : String
  haveDraft : String
  deriving ToJson

/--
The trace of a Lean file.
-/
structure Trace where
  haveDrafts : Array HaveDraft   -- All have drafts in the file
deriving ToJson


abbrev TraceM := StateT Trace MetaM

namespace Pp


private def addLine (s : String) : String :=
  if s.isEmpty then s else s ++ "\n"

def applyOptions : Options → Options :=
  (pp.proofs.set · false |>
  (pp.motives.all.set · true |>
  (pp.coercions.types.set · true |>
  (pp.unicode.fun.set · true))))
open Lean Meta

def ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO String :=
  if goals.isEmpty then
    return "no goals"
  else
    let fmt := ctx.runMetaM {} (return Std.Format.prefixJoin "\n\n" (← goals.mapM (ppGoal ·)))
    return (← fmt).pretty.trim


end Pp

open Lean Meta Elab Tactic

def mkCurriedImplication (hyps : Array LocalDecl) (goal : Expr) : MetaM Expr := do
  -- Extract the `Expr.fvarId` for each hypothesis
  let fvars ← hyps.mapM fun hyp => return mkFVar hyp.fvarId

  -- Use mkForallFVars to abstract the goal over the fvars
  mkForallFVars fvars goal

def extractHypsFromGoal (mvarId : MVarId) : MetaM (Array LocalDecl) := do
  mvarId.withContext do
    pure <| (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isAuxDecl || decl.isImplementationDetail then acc else acc.push decl

open Lean Meta in

def newHyps (goalBefore : MVarId) (goalAfter : MVarId) : MetaM (Array LocalDecl) := do
  -- let beforeTypes := (← extractHypsFromGoal goalBefore).map (·.type) -- TODO ordering
  let beforeFVars := (← extractHypsFromGoal goalBefore).map (·.fvarId)
  (← extractHypsFromGoal goalAfter).filterM fun h => do return !(beforeFVars.contains (h.fvarId))

/-
 returns tuple and Array of (goal, name, type)
-/
def haveDrafts
  (goalsBefore : List MVarId)
  (goalsAfter : List MVarId) (tacticText : String) : MetaM (Array (String × String × String)) :=
  let intersection := goalsBefore.filter (fun g => goalsAfter.contains g)
  let goalsBefore := goalsBefore.filter (fun g => !intersection.contains g)
  let goalsAfter := goalsAfter.filter (fun g => !intersection.contains g)
  MonadWithOptions.withOptions Pp.applyOptions do
  match goalsBefore with
  | [gBefore] => do
    if let [gAfter'] := goalsAfter then
      if ← isDefEqGuarded (← gAfter'.getType) (← gBefore.getType) then -- isDefEq used instead of == for mdata
        let newHyps ← newHyps gBefore gAfter'
        let fvarNewHyps := newHyps.filter (fun h => !h.isLet)
        let letNewHyps := newHyps.filter (fun h => h.isLet)
        if ← fvarNewHyps.allM (fun h => isProp h.type) then
          let mut goal := (← gBefore.withContext do mkFreshExprMVar (← gBefore.getType)).mvarId!
          let mut result : Array (String × String × String) := #[]
          let mut fvars := #[]
          for (h, idx) in fvarNewHyps.zipIdx do
            let goalString := (← Meta.ppGoal goal).pretty.replace "⋯" "sorry"
            let name := ← goal.withContext do disambiguate (desiredName h.userName tacticText)
            let typeString ← gAfter'.withContext do pure ((← ppExpr h.type).pretty.replace "⋯" "sorry")
            let subseq := ((fvarNewHyps.take idx).map (.fvar ·.fvarId))
            let replaced ← gAfter'.withContext do mkCurriedImplication letNewHyps (h.type.replaceFVars subseq fvars)
            let noted := (← goal.note name.toName (← Meta.mkSorry replaced false) (replaced))
            fvars := fvars.push (.fvar noted.1)
            goal := noted.2
            result := result.push (goalString, name, typeString)
          return result

    let mut out : Array (String × String × String) := #[]
    let mut goal := (← gBefore.withContext do mkFreshExprMVar (← gBefore.getType)).mvarId!

    IO.println s!"{← gBefore.withContext do ppExpr (← gBefore.getType)} num goals after: {goalsAfter.length}"

    for gAfter in goalsAfter do
      let newHyps ← newHyps gBefore gAfter
      let gAfterName := ((← getMCtx).getDecl gAfter).userName
      let imp ← gAfter.withContext do mkCurriedImplication newHyps (← gAfter.getType)
      let goalString := (← Meta.ppGoal goal).pretty.replace "⋯" "sorry"
      let name := ← goal.withContext do disambiguate (desiredName gAfterName tacticText)
      let typeString := ← gAfter.withContext do return ((← ppExpr imp).pretty.replace "⋯" "sorry")
      out := out.push (goalString, name, typeString)
      goal := (← goal.note name.toName (← Meta.mkSorry imp false) imp).2
    return out
  | _ => return #[]

namespace Path

/--
Return the path of `path` relative to `parent`.
-/
def relativeTo (path parent : FilePath) : Option FilePath :=
  let rec componentsRelativeTo (pathComps parentComps : List String) : Option FilePath :=
    match pathComps, parentComps with
    | _, [] => mkFilePath pathComps
    | [], _ => none
    | (h₁ :: t₁), (h₂ :: t₂) =>
      if h₁ == h₂ then
        componentsRelativeTo t₁ t₂
      else
        none

    componentsRelativeTo path.components parent.components


/--
Return if the path `path` is relative to `parent`.
-/
def isRelativeTo (path parent : FilePath) : Bool :=
  match relativeTo path parent with
  | some _ => true
  | none => false


/--
Convert the path `path` to an absolute path.
-/
def toAbsolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path


private def trim (path : FilePath) : FilePath :=
  assert! path.isRelative
  mkFilePath $ path.components.filter (· != ".")


def packagesDir : FilePath :=
  if Lake.defaultPackagesDir == "packages"  then
    ".lake" / Lake.defaultPackagesDir
  else
    Lake.defaultPackagesDir


def buildDir : FilePath :=
  if Lake.defaultPackagesDir.fileName == "packages" then  -- Lean >= v4.3.0-rc2
    ".lake/build"
  else  -- Lean < v4.3.0-rc2
   "build"


def libDir : FilePath := buildDir / "lib" / "lean"


/--
Convert the path of a *.lean file to its corresponding file (e.g., *.olean) in the "build" directory.
-/
def toBuildDir (subDir : FilePath) (path : FilePath) (ext : String) : Option FilePath :=
  let path' := (trim path).withExtension ext
  match relativeTo path' $ packagesDir / "lean4/src" with
  | some p =>
    match relativeTo p "lean/lake" with
    | some p' => packagesDir / "lean4/lib/lean" / p'
    | none => packagesDir / "lean4/lib" / p
  | none => match relativeTo path' packagesDir with
    | some p =>
      match p.components with
      | [] => none
      | hd :: tl => packagesDir / hd / buildDir / subDir / (mkFilePath tl)
    | none => buildDir / subDir / path'


/--
The reverse of `toBuildDir`.
-/
-- proofwidgets/build/lib/ProofWidgets/Compat.lean
-- proofwidgets/.lake/build/lib
def toSrcDir! (path : FilePath) (ext : String) : FilePath :=
  let path' := (trim path).withExtension ext
  match relativeTo path' $ packagesDir / "lean4/lib" with
  | some p =>  -- E.g., `.lake/packages/lean4/lib/lean/Init/Prelude.olean` -> `.lake/packages/lean4/src/lean/Init/Prelude.lean`
    packagesDir / "lean4/src" / p
  | none =>
    match relativeTo path' packagesDir with
    | some p =>  -- E.g., `.lake/packages/aesop/.lake/build/lib/lean/Aesop.olean`-> `.lake/packages/aesop/Aesop.lean`
      let pkgName := p.components.head!
      let sep := "build/lib/lean/"
      packagesDir / pkgName / (p.toString.splitOn sep |>.tail!.head!)
    | none =>
      -- E.g., `.lake/build/lib/lean/Mathlib/LinearAlgebra/Basic.olean` -> `Mathlib/LinearAlgebra/Basic.lean`
      relativeTo path' libDir |>.get!


/--
Create all parent directories of `p` if they don't exist.
-/
def makeParentDirs (p : FilePath) : IO Unit := do
  let some parent := p.parent | throw $ IO.userError s!"Unable to get the parent of {p}"
  IO.FS.createDirAll parent


/--
Return the *.lean file corresponding to a module name.
-/
def findLean (mod : Name) : IO FilePath := do
  let modStr := mod.toString
  if modStr.startsWith "«lake-packages»." then
    return FilePath.mk (modStr.replace "«lake-packages»" "lake-packages" |>.replace "." "/") |>.withExtension "lean"
  if modStr.startsWith "«.lake»." then
    return FilePath.mk (modStr.replace "«.lake»" ".lake" |>.replace "." "/") |>.withExtension "lean"
  if modStr == "Lake" then
    return packagesDir / "lean4/src/lean/lake/Lake.lean"
  let olean ← findOLean mod
  -- Remove a "build/lib/lean/" substring from the path.
  let lean := olean.toString.replace ".lake/build/lib/lean/" ""
    |>.replace "build/lib/lean/" "" |>.replace "lib/lean/Lake/" "lib/lean/lake/Lake/"
  let mut path := FilePath.mk lean |>.withExtension "lean"
  let leanLib ← getLibDir (← getBuildDir)
  if let some p := relativeTo path leanLib then
    path := packagesDir / "lean4/src/lean" / p
  assert! ← path.pathExists
  return path

end Path


namespace Traversal

partial def getSubNodePositions (infotree : InfoTree) (startPos : String.Pos) (endPos : String.Pos) (ctx? : Option ContextInfo) : IO (List MVarId) := do
  match infotree with
  | .context ctx t => getSubNodePositions t startPos endPos (ctx.mergeIntoOuter? ctx?)
  | .node info children =>
    match info.stx.getRange? with
    | some r =>
      match ctx? with
      | some ctx =>
        let flag ← ctx.runMetaM {} try
          match info with
          | .ofTacticInfo  info =>
            return info.goalsBefore
          | _                   => return []
        catch _ =>
          pure []
        if (startPos < r.start ∨ r.stop < endPos) ∧ flag != [] then
          return flag
        else
          return (← (children.mapM (getSubNodePositions · startPos endPos ctx?))).toList.foldr (· ++ ·) []
      | none => pure []
    | none => pure []
  | .hole mvarId => pure []

/--
Extract tactic information from `TacticInfo` in `InfoTree`.
-/
private def visitTacticInfo (ctx : ContextInfo) (ti : TacticInfo) (parent : InfoTree) : TraceM Unit := do
  match ti.stx.getKind with
  | ``Lean.Parser.Term.byTactic =>
    match ti.stx with
    | .node _ _ #[.atom _ "by", .node _ ``Lean.Parser.Tactic.tacticSeq _] => pure ()
    | _ => assert! false

  | ``Lean.Parser.Tactic.tacticSeq =>
    match ti.stx with
    | .node _ _ #[.node _ ``Lean.Parser.Tactic.tacticSeq1Indented _] => pure ()
    | .node _ _ #[.node _ ``Lean.Parser.Tactic.tacticSeqBracketed _] => pure ()
    | _ => assert! false

  | _ => pure ()

  match parent with
  | .node (Info.ofTacticInfo i) children =>
    match i.stx.getKind with
    | ``Lean.Parser.Tactic.tacticSeq1Indented | ``Lean.Parser.Tactic.tacticSeqBracketed | ``Lean.Parser.Tactic.rewriteSeq =>
      let ctxBefore := { ctx with mctx := ti.mctxBefore }
      let ctxAfter := { ctx with mctx := ti.mctxAfter }
      let goalsBefore ← ctxBefore.runMetaM {} (ti.goalsBefore.toArray.mapM Meta.ppGoal)
      let goalsAfter ← ctxAfter.runMetaM {} (ti.goalsAfter.toArray.mapM Meta.ppGoal)
      -- if goalsBefore.map (·.pretty) == #[] || goalsBefore.map (·.pretty) == goalsAfter.map (·.pretty) then
      --   pure ()
      -- else
      let some posBefore := ti.stx.getPos? true | pure ()
      let some posAfter := ti.stx.getTailPos? true | pure ()

      -- Extract the actual tactic text from the source
      let tacticText := ctx.fileMap.source.extract posBefore posAfter

      IO.println s!"tactic text: {tacticText}"

      let haveDrafts' ← try
        if ["intro", "intros", "rintro"].any (·.isPrefixOf tacticText) then
          pure #[]
        else
          ctx.runMetaM {} (haveDrafts ti.goalsBefore ti.goalsAfter tacticText)
        catch e =>
          IO.println (f!"Failed to process tactic pair.\nGoals before: {goalsBefore}.\nGoals after: {goalsAfter} errr: {← e.toMessageData.format}\n\n")
          pure #[]

      IO.println s!"goalsBefore: {goalsBefore} goalsAfter: {goalsAfter} haveDrafts': {haveDrafts'}"

      match ti.stx with
      | .node _ _ _ =>
        modify fun trace => {
          trace with
            -- tactics := trace.tactics.push {
            --   goalsBefore := goalsBefore,
            --   goalsAfter := goalsAfter,
            --   pos := posBefore,
            --   endPos := posAfter,
            --   tactic := tacticText,
            -- },
            haveDrafts := if haveDrafts'.isEmpty then trace.haveDrafts else trace.haveDrafts.append (haveDrafts'.map (fun (x, n, y) => {
              goal := x,
              name := n,
              haveDraft := y,
              tactic := tacticText,
            })),
        }
      | _ => pure ()

    | ``Lean.Parser.Tactic.induction =>
      match i.stx.getRange? with
      | some r =>
        let goalsAfter' ← getSubNodePositions parent r.start r.stop ctx
        let goalsAfter ← ctx.runMetaM {} (goalsAfter'.mapM Meta.ppGoal)
        IO.println s!"pattern match goalsAfter: {goalsAfter}"
        let ctxBefore := { ctx with mctx := ti.mctxBefore }
        let goalsBefore ← ctxBefore.runMetaM {} (ti.goalsBefore.toArray.mapM Meta.ppGoal)
        let some posBefore := ti.stx.getPos? true | pure ()
        let some posAfter := ti.stx.getTailPos? true | pure ()

        let tacticText := ctx.fileMap.source.extract posBefore posAfter

        IO.println s!"tactic text: {tacticText}"

        let haveDrafts' ← try
          ctx.runMetaM {} (haveDrafts ti.goalsBefore goalsAfter' tacticText)
        catch e =>
          IO.println (f!"Failed to process tactic pair.\nGoals before: {goalsBefore}.\nGoals after: {goalsAfter} errr: {← e.toMessageData.format}\n\n")
          pure #[]

        IO.println s!"ind match goalsBefore: {goalsBefore} goalsAfter: {goalsAfter} haveDrafts': {haveDrafts'}"

        modify fun trace => {
          trace with
            haveDrafts := if haveDrafts'.isEmpty then trace.haveDrafts else trace.haveDrafts.append (haveDrafts'.map (fun (x, n, y) => {
              goal := x,
              name := n,
              haveDraft := y,
              tactic := tacticText,
            })),
        }
      | none => pure ()
      pure ()
    | _ => pure ()
  | _ => pure ()

private def visitInfo (ctx : ContextInfo) (i : Info) (parent : InfoTree) (_ : Environment) : TraceM Unit := do
  match i with
  | .ofTacticInfo ti => visitTacticInfo ctx ti parent
  | _ => pure ()


private partial def traverseTree (ctx: ContextInfo) (tree : InfoTree)
(parent : InfoTree) (env : Environment) : TraceM Unit := do
  match tree with
  | .context ctx' t =>
    match ctx'.mergeIntoOuter? ctx with
    | some ctx' => traverseTree ctx' t tree env
    | none => panic! "fail to synthesis contextInfo when traversing infoTree"
  | .node i children =>
    visitInfo ctx i parent env
    for x in children do
      traverseTree ctx x tree env
  | _ => pure ()


private def traverseTopLevelTree (tree : InfoTree) (env : Environment) : TraceM Unit := do
  match tree with
  | .context ctx t =>
    match ctx.mergeIntoOuter? none with
    | some ctx => traverseTree ctx t tree env
    | none => panic! "fail to synthesis contextInfo for top-level infoTree"
  | _ => pure ()


/--
Process an array of `InfoTree` (one for each top-level command in the file).
-/
def traverseForest (trees : Array InfoTree) (env : Environment) : TraceM Trace := do
  for t in trees do
    traverseTopLevelTree t env
  get


end Traversal


open Traversal


def getImports (header: TSyntax `Lean.Parser.Module.header) : IO String := do
  -- Similar to `lean --deps` in Lean 3.
  let mut s := ""

  for dep in headerToImports header do
    -- let oleanPath ← findOLean dep.module
    let leanPath ← Path.findLean dep.module
    s := s ++ "\n" ++ leanPath.toString
    /-
    if oleanPath.isRelative then
      let leanPath := Path.toSrcDir! oleanPath "lean"
      assert! ← leanPath.pathExists
      s := s ++ "\n" ++ leanPath.toString
    else if ¬(oleanPath.toString.endsWith "/lib/lean/Init.olean") then
      let mut p := (Path.packagesDir / "lean4").toString ++ FilePath.pathSeparator.toString
      let mut found := false
      for c in (oleanPath.withExtension "lean").components do
        if c == "lib" then
          found := true
          p := p ++ "src"
          continue
        if found then
          p := p ++ FilePath.pathSeparator.toString ++ c
      p := p.replace "/lean4/src/lean/Lake" "/lean4/src/lean/lake/Lake"
      assert! ← FilePath.mk p |>.pathExists
      s := s ++ "\n" ++ p
  -/

  return s.trim


/--
Trace a *.lean file.
-/
unsafe def processFile (path : FilePath) : IO Unit := do
  println! path
  let input ← IO.FS.readFile path
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← moduleNameOfFileName path none)
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let env' := s.commandState.env
  let trees := s.commandState.infoState.trees.toArray

  let traceM := (traverseForest trees env').run' ⟨#[]⟩
  let (trace, _) ← traceM.run'.toIO {fileName := s!"{path}", fileMap := FileMap.ofString input} {env := env}

  let cwd ← IO.currentDir
  assert! cwd.fileName != "lean4"

  let some relativePath := Path.relativeTo path cwd | throw $ IO.userError s!"Invalid path: {path}"
  let json_path := Path.toBuildDir "ir" relativePath "ast.json" |>.get!
  Path.makeParentDirs json_path
  IO.FS.writeFile json_path (toJson trace).pretty

  let dep_path := Path.toBuildDir "ir" relativePath "dep_paths" |>.get!
  Path.makeParentDirs dep_path
  IO.FS.writeFile dep_path (← getImports header)


end LeanDojo


open LeanDojo

/--
Whether a *.lean file should be traced.
-/
def shouldProcess (path : FilePath) (noDeps : Bool) : IO Bool := do
  if (← path.isDir) ∨ path.extension != "lean" then
    return false

  let cwd ← IO.currentDir
  let some relativePath := Path.relativeTo path cwd |
    throw $ IO.userError s!"Invalid path: {path}"

  if noDeps ∧ Path.isRelativeTo relativePath Path.packagesDir then
    return false

  let some oleanPath := Path.toBuildDir "lib/lean" relativePath "olean" |
    throw $ IO.userError s!"Invalid path: {path}"
  return ← oleanPath.pathExists


/--
Trace all *.lean files in the current directory whose corresponding *.olean file exists.
-/
def processAllFiles (noDeps : Bool) : IO Unit := do
    let cwd ← IO.currentDir
    assert! cwd.fileName != "lean4"
    println! "Extracting data at {cwd}"

    let mut tasks := #[]
    for path in ← System.FilePath.walkDir cwd do
      if ← shouldProcess path noDeps then
        let t ← IO.asTask $ IO.Process.run
          {cmd := "lake", args := #["env", "lean", "--run", "ExtractData.lean", path.toString]}
        tasks := tasks.push (t, path)

    for (t, path) in tasks do
      match ← IO.wait t with
      | Except.error _ =>
        println! s!"WARNING: Failed to process {path}"
        pure ()
        -- throw e
      | Except.ok _ => pure ()


unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["noDeps"] => processAllFiles (noDeps := true)
  | [path] => processFile (← Path.toAbsolute ⟨path⟩)
  | [] => processAllFiles (noDeps := false)
  | _ => throw $ IO.userError "Invalid arguments"
