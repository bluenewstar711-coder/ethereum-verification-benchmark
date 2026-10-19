/-
Warm-import Lean checker.

Reads one request per line on stdin: `<output path>\t<lean file>`, where the file path is
relative to the working directory exactly as it would be passed to `lake env lean <file>`.
For each request it elaborates the whole file and writes to `<output path>` the bytes the
`lean` command line would have printed, then answers one line on stdout:

  `ok <exit code>`   the file was checked; <exit code> is what `lean` would return
  `fallback`         the header could not be handled here (e.g. it reports diagnostics);
                     the caller must run the real `lean`

What is reused between requests is only the imported environment, keyed by the import
list. Everything else mirrors `Lean.Elab.runFrontend` (cmdline snapshots, async
elaboration, default options, `moduleNameOfFileName`, default trust level) and the header
step of `Lean.Language.Lean.process` (`Command.mkState` with the same info-tree root), and
messages are printed by `SnapshotTree.runAndReport`, the function the command line uses.
-/
import Lean

open Lean Elab Language

namespace WarmLean

/-! Same C entry points the `lean` shell uses (`Lean.Shell` keeps its bindings private). -/
@[extern "lean_internal_get_default_options"]
opaque getDefaultOptions (_ : Unit) : Options
@[extern "lean_decode_lossy_utf8"]
opaque decodeLossyUTF8 (a : @& ByteArray) : String
@[extern "lean_internal_get_believer_trust_level"]
opaque getBelieverTrustLevel (_ : Unit) : UInt32
def defaultTrustLevel : UInt32 := getBelieverTrustLevel () + 1

structure Cached where
  env : Environment

/-- Mirrors `Lean.Shell`'s defaults and the options `runFrontend` forces. -/
def frontendOpts : IO Options := do
  let opts := getDefaultOptions ()
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  return Elab.async.setIfNotSet opts true

/-- Elaborates `fileName` (relative to the cwd) with a cached header environment.
Returns `none` when the request must go to the real `lean`. -/
def checkFile (cache : IO.Ref (Std.HashMap String Cached)) (fileName : String) : IO (Option UInt32) := do
  let contents ← decodeLossyUTF8 <$> IO.FS.readBinFile fileName
  if contents.startsWith "#lang" then return none
  let opts ← frontendOpts
  let inputCtx := Parser.mkInputContext contents fileName
  let mainModuleName ← try moduleNameOfFileName fileName none catch _ => pure `_stdin
  let (origStx, parserState, msgLog) ← Parser.parseHeader inputCtx
  unless msgLog.toList.isEmpty do
    IO.eprintln s!"fallback: header parse messages: {← msgLog.toList.mapM (·.toString)}"
    return none
  -- `process` hands the header with trailing whitespace stripped to `processHeader`
  let stx : Elab.HeaderSyntax := ⟨origStx.raw.unsetTrailing⟩
  let imports := stx.imports
  let key := toString (repr (stx.isModule, imports.map fun i => (i.module, i.importAll, i.isExported, i.isMeta)))
  let headerStx := stx.raw
  let env ← match (← cache.get)[key]? with
    | some c => pure c.env
    | none =>
      let (env, hdrLog) ← Elab.processHeaderCore (leakEnv := true)
        stx.startPos imports stx.isModule opts .empty inputCtx
        (trustLevel := defaultTrustLevel) (mainModule := mainModuleName)
        (headerStx? := stx) (origHeaderStx? := some ⟨origStx.raw⟩)
      unless hdrLog.toList.isEmpty do
        IO.eprintln s!"fallback: header messages: {← hdrLog.toList.mapM (·.toString)}"
        return none
      cache.modify (·.insert key { env })
      pure env
  let env := env.setMainModule mainModuleName
  let opts ← Language.Lean.reparseOptions opts
  let cmdState := Command.mkState env {} opts
  let cmdState := { cmdState with
    infoState := {
      enabled := true
      trees := #[InfoTree.context (.commandCtx {
        env     := env
        fileMap := inputCtx.fileMap
        ngen    := { namePrefix := `_import }
      }) (InfoTree.node
          (Info.ofCommandInfo { elaborator := `header, stx := headerStx })
          (headerStx[2].getArgs.toList.map (fun importStx =>
            InfoTree.node (Info.ofCommandInfo {
              elaborator := `import
              stx := importStx
            }) #[].toPArray'
          )).toPArray'
      )].toPArray'
    }
  }
  let firstCmd ← Language.Lean.processCommands inputCtx parserState cmdState
  let hasErrors ← (toSnapshotTree firstCmd.get).runAndReport opts
  return some (if hasErrors then 1 else 0)

unsafe def serve : IO Unit := do
  -- What the `lean` binary does before elaborating: search path = LEAN_PATH + the
  -- toolchain's own library dir (we are not the toolchain binary, so locate it), and
  -- running `initialize` declarations of imported modules.
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let cache ← IO.mkRef ({} : Std.HashMap String Cached)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.toString
    match line.splitOn "\t" with
    | [outPath, fileName] =>
      let result ← IO.FS.withFile outPath .write fun h => do
        let stream := IO.FS.Stream.ofHandle h
        let prev ← IO.setStdout stream
        try
          checkFile cache fileName
        finally
          discard <| IO.setStdout prev
      match result with
      | some code => stdout.putStrLn s!"ok {code}"
      | none => stdout.putStrLn "fallback"
    | _ => stdout.putStrLn "fallback"
    stdout.flush

end WarmLean

unsafe def main : IO Unit := WarmLean.serve
