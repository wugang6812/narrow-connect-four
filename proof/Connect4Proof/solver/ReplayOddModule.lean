/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of LeanChecker's replayFromImports: Kim Morrison, Sebastian Ullrich

The replay body is copied from this pinned Lean toolchain's LeanChecker.lean.
This entry point takes one exact module name and avoids scanning the entire
search path for module-name prefixes. It uses the same Lean kernel replay API.
This is an audit utility, not an imported part of the mathematical proof.
-/
import Lean.Replay

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [arg] := args | throw <| IO.userError "Expected exactly one module name"
  initSearchPath (← findSysroot)
  let module := arg.toName
  if module.isAnonymous then throw <| IO.userError "Invalid module name"
  IO.println s!"replaying {module}"
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  if newConstants.size == 0 then throw <| IO.userError "Expected a nonempty proof module"
  discard <| env.toKernelEnv.replay newConstants
  IO.println s!"kernel replay passed: {module}; declarations={newConstants.size}"
  env.freeRegions
  return 0
