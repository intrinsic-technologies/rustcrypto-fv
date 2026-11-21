import Lean

/-!
Fails if a module named on the command line reaches lean-x86-proofs through its imports. Run as
`lake env lean --run ci/ClaimImports.lean <Crate>.Spec <Crate>.Statements` after building those
modules. It reads the import graph recorded in the compiled `.olean` files, so unlike the source
scans in `ci/crates.py` and `ci/comparator.py` it does not depend on how imports are written.
-/

open Lean

/-- Root modules of lean-x86-proofs' libraries, which proofs may import but the claim may not. -/
def proofLibraries : List Name := [`X86Proofs, `X86ProofsExamples]

def isProofLibrary (module : Name) : Bool :=
  proofLibraries.contains module.getRoot

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run ci/ClaimImports.lean <module>..."
    return 2
  initSearchPath (← findSysroot)
  let roots := args.toArray.map fun arg => ({ module := arg.toName } : Import)
  let env ← importModules roots {}
  let mut found := roots.filterMap fun root =>
    if isProofLibrary root.module then some s!"{root.module} is in the proof library" else none
  for name in env.header.moduleNames, data in env.header.moduleData do
    unless isProofLibrary name do
      for imported in data.imports do
        if isProofLibrary imported.module then
          found := found.push s!"{name} imports {imported.module}"
  if found.isEmpty then
    IO.println s!"{env.header.moduleNames.size} modules reachable from {args} \
      do not include the proof library"
    return 0
  for line in found do
    IO.eprintln s!"error: {line}; the specification and statement must not import the proof \
      library ({proofLibraries}), which only proofs may use"
  return 1
