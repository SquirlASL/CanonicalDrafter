import Lean
import Lake

-- example test
-- lake env lean --run ../CanonicalDrafter/ExtractData.lean Mathlib/Combinatorics/Hindman.lean
-- cat .lake/build/ir/Mathlib/Combinatorics/Hindman.ast.json
-- https://github.com/lean-dojo/LeanDojo/issues/247

-- based on https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean from LeanDojo
-- unlike LeanDojo we only care about tracing tactics so we remove commands and premises to reduce storage cost and increase speed.


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
  goal : String
  haveDraft : String
  deriving ToJson

/--
The trace of a Lean file.
-/
structure Trace where
  tactics: Array TacticTrace    -- All tactics in the file.
  haveDrafts : Array HaveDraft   -- All have drafts in the file
deriving ToJson


abbrev TraceM := StateT Trace MetaM


namespace Pp


private def addLine (s : String) : String :=
  if s.isEmpty then s else s ++ "\n"

def applyOptions : Options → Options :=
  (pp.proofs.set · true |>
  (pp.motives.all.set · true |>
  (pp.coercions.types.set · true |>
  (pp.unicode.fun.set · true))))

-- Similar to `Meta.ppGoal` but uses String instead of Format to make sure local declarations are separated by "\n".
private def ppGoal (mvarId : MVarId) (additionalHyps : Array Expr := #[]): MetaM String := do
  MonadWithOptions.withOptions applyOptions do
    match (← getMCtx).findDecl? mvarId with
    | none          => return "unknown goal"
    | some mvarDecl =>
      let indent         := 2
      let lctx           := mvarDecl.lctx
      let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
      Meta.withLCtx lctx mvarDecl.localInstances do
        -- The followint two `let rec`s are being used to control the generated code size.
        -- Then should be remove after we rewrite the compiler in Lean
        let rec pushPending (ids : List Name) (type? : Option Expr) (s : String) : MetaM String := do
          if ids.isEmpty then
            return s
          else
            let s := addLine s
            match type? with
            | none      => return s
            | some type =>
              let typeFmt ← Meta.ppExpr type
              return (s ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group).pretty
        let rec ppVars (varNames : List Name) (prevType? : Option Expr) (s : String) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × String) := do
          match localDecl with
          | .cdecl _ _ varName type _ _ =>
            let varName := varName.simpMacroScopes
            let type ← instantiateMVars type
            if prevType? == none || prevType? == some type then
              return (varName :: varNames, some type, s)
            else do
              let s ← pushPending varNames prevType? s
              return ([varName], some type, s)
          | .ldecl _ _ varName type val _ _ => do
            let varName := varName.simpMacroScopes
            let s ← pushPending varNames prevType? s
            let s  := addLine s
            let type ← instantiateMVars type
            let typeFmt ← Meta.ppExpr type
            let mut fmtElem  := format varName ++ " : " ++ typeFmt
            let val ← instantiateMVars val
            let valFmt ← Meta.ppExpr val
            fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
            let s := s ++ fmtElem.group.pretty
            return ([], none, s)
        let (varNames, type?, s) ← lctx.foldlM (init := ([], none, "")) fun (varNames, prevType?, s) (localDecl : LocalDecl) =>
          if localDecl.isAuxDecl || localDecl.isImplementationDetail then
            -- Ignore auxiliary declarations and implementation details.
            return (varNames, prevType?, s)
          else
            ppVars varNames prevType? s localDecl
        let mut varNames := varNames
        let mut type? := type?
        let mut s ← pushPending varNames type? s
        for addHyp in additionalHyps do
          let name ← mkFreshUserName `synth
          s := s ++ "\n" ++ s!"{name.toString} : " ++ (← Meta.ppExpr addHyp).pretty
        let goalTypeFmt ← Meta.ppExpr (← instantiateMVars mvarDecl.type)
        let goalFmt := Meta.getGoalPrefix mvarDecl ++ Format.nest indent goalTypeFmt
        let s' := s ++ "\n" ++ goalFmt.pretty
        return s'


def ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO String :=
  if goals.isEmpty then
    return "no goals"
  else
    let fmt := ctx.runMetaM {} (return Std.Format.prefixJoin "\n\n" (← goals.mapM (ppGoal ·)))
    return (← fmt).pretty.trim


end Pp

open Lean Meta Elab Tactic

def mkCurriedImplication (hyps : List LocalDecl) (goal : Expr) : MetaM Expr := do
  hyps.foldrM (init := goal) fun hyp acc =>
    return mkForall hyp.userName hyp.binderInfo hyp.type acc

def extractHypsFromGoal (mvarId : MVarId) : MetaM (List LocalDecl) := do
  let mctx ← getMCtx
  let some mdecl := mctx.findDecl? mvarId | return []
  let lctx := mdecl.lctx
  Meta.withLCtx lctx mdecl.localInstances do
    pure <| lctx.foldl (init := []) fun acc decl =>
      if decl.isAuxDecl || decl.isImplementationDetail then acc else decl :: acc

open Lean Meta in

def haveDrafts
  (goalsBefore : List MVarId)
  (goalsAfter : List MVarId) : MetaM (Array (String × String)) := do

  match goalsBefore with
  | [gBefore] =>
    -- get metavariable decl for before
    let mctx ← getMCtx
    let some declBefore := mctx.findDecl? gBefore | throwError "unknown mvar {gBefore.name}"

    -- run inside lctx of before
    let hypsBefore ← Meta.withLCtx declBefore.lctx declBefore.localInstances do
      extractHypsFromGoal gBefore

    let beforeTypes := hypsBefore.map (·.type)

    let goalB ← Meta.withLCtx declBefore.lctx declBefore.localInstances do
      gBefore.getType

    let mut out : Array (String × String) := #[]
    let mut drafts : Array Expr := #[]

    for gAfter in goalsAfter do
      let some declAfter := mctx.findDecl? gAfter | throwError "unknown mvar {gAfter.name}"

      let hypsAfter ← Meta.withLCtx declAfter.lctx declAfter.localInstances do
        extractHypsFromGoal gAfter


      let newHyps ← hypsAfter.filterM fun h => do
        let isOld ← beforeTypes.anyM fun b => do
          return b == h.type
        return !isOld

      let goalA ← Meta.withLCtx declAfter.lctx declAfter.localInstances do
        gAfter.getType

      if goalA == goalB then
        let newHypsStrs ← Meta.withLCtx declAfter.lctx declAfter.localInstances do
          newHyps.mapM ((fun x => MonadWithOptions.withOptions Pp.applyOptions do ppExpr x) ∘ LocalDecl.type)
        out := out.append (← newHypsStrs.toArray.mapM (fun x => do return ⟨← Pp.ppGoal gBefore drafts, Format.pretty x⟩))
        drafts := drafts.append (newHyps.toArray.map (·.type))
      else
        let imp ← Meta.withLCtx declAfter.lctx declAfter.localInstances do
          mkCurriedImplication newHyps goalA
        out := out.push ⟨← Pp.ppGoal gBefore drafts, ← Meta.withLCtx declAfter.lctx declAfter.localInstances do return (← ppExpr imp).pretty⟩

        drafts := drafts.push imp

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
      let goalsBefore ← ctxBefore.runMetaM {} (ti.goalsBefore.toArray.mapM Pp.ppGoal)
      let goalsAfter ← ctxAfter.runMetaM {} (ti.goalsAfter.toArray.mapM Pp.ppGoal)
      if goalsBefore == #[] || goalsBefore == goalsAfter then
        pure ()
      else
        let some posBefore := ti.stx.getPos? true | pure ()
        let some posAfter := ti.stx.getTailPos? true | pure ()

        -- Extract the actual tactic text from the source
        let tacticText := ctx.fileMap.source.extract posBefore posAfter

        let haveDrafts' ← try
          ctx.runMetaM {} (haveDrafts ti.goalsBefore ti.goalsAfter)
        catch _ =>
          IO.println (f!"Failed to process tactic pair.\nGoals before: {goalsBefore}.\nGoals after: {goalsAfter}\n\n")
          pure #[]

        match ti.stx with
        | .node _ _ _ =>
          modify fun trace => {
            trace with
              tactics := trace.tactics.push {
                goalsBefore := goalsBefore,
                goalsAfter := goalsAfter,
                pos := posBefore,
                endPos := posAfter,
                tactic := tacticText,
              },
              haveDrafts := if haveDrafts'.isEmpty then trace.haveDrafts else trace.haveDrafts.append (haveDrafts'.map (fun (x, y) => {
                goal := x,
                haveDraft := y,
                tactic := tacticText,
              })),
          }
        | _ => pure ()
    | ``Lean.Parser.Tactic.induction =>
      match i.stx.getRange? with
      | some r =>
        let goalsAfter' ← getSubNodePositions parent r.start r.stop ctx
        let goalsAfter ← ctx.runMetaM {} (goalsAfter'.mapM Pp.ppGoal)
        let ctxBefore := { ctx with mctx := ti.mctxBefore }
        let goalsBefore ← ctxBefore.runMetaM {} (ti.goalsBefore.toArray.mapM Pp.ppGoal)
        let some posBefore := ti.stx.getPos? true | pure ()
        let some posAfter := ti.stx.getTailPos? true | pure ()

        let haveDrafts' ← try
          ctx.runMetaM {} (haveDrafts ti.goalsBefore goalsAfter')
        catch _ =>
          IO.println (f!"Failed to process tactic pair.\nGoals before: {goalsBefore}.\nGoals after: {goalsAfter}\n\n")
          pure #[]

        let tacticText := ctx.fileMap.source.extract posBefore posAfter

        modify fun trace => {
          trace with
            tactics := trace.tactics.push {
              goalsBefore := goalsBefore,
              goalsAfter := goalsAfter.toArray,
              pos := posBefore,
              endPos := posAfter,
              tactic := tacticText
            },
            haveDrafts := if haveDrafts'.isEmpty then trace.haveDrafts else trace.haveDrafts.append (haveDrafts'.map (fun (x, y) => {
              goal := x,
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

  let traceM := (traverseForest trees env').run' ⟨#[], #[]⟩
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
