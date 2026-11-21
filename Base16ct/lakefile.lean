import Lake
open Lake DSL

/-!
`base16ct` as its own Lake package, so it can pin its own lean-x86 and lean-x86-proofs. Run every
command from this directory. Sources stay where they are in the repository: the libraries read
them from the repository root, including the shared `Standards` definitions, which this package
builds with its own pins.
-/

package base16ct where
  enableArtifactCache := true
  restoreAllArtifacts := true

require x86 from git
  "git@github.com:intrinsic-technologies/lean-x86.git" @ "v0.0.2"

/-- Proof library for lean-x86 programs, available to proofs only. -/
require x86proofs from git
  "git@github.com:intrinsic-technologies/lean-x86-proofs.git" @ "v0.0.2"

/-- The repository root, which holds the sources. An absolute path rather than `".."`, so that Lake
can map a source file back to its module (`lake setup-file`, which editors and
`ci/check_spec_dependencies.py` use, compares real paths). -/
def repositoryRoot : System.FilePath := (__dir__).parent.get!

/-- Runs this crate's executable specification tests. -/
@[default_target, test_driver]
lean_exe tests where
  srcDir := "."
  root := `TestDriver

/-- The shared definitions of published standards, built from the repository root's sources. -/
lean_lib Standards where
  srcDir := repositoryRoot
  roots := #[`Standards]

/-- The `.bin` files embedded with `include_bytes` and `include_chunked_bytes`, so that a byte
change rebuilds their users: those in `Spec/` and, when present, `Proofs/`, which comparator's
spec-only workspace leaves out. Not the crate directory itself, which would also walk `.lake/`. -/
target base16ct_bins pkg : Array System.FilePath := do
  let dirs ← #[pkg.dir / "Spec", pkg.dir / "Proofs"].filterM (·.isDir)
  let jobs ← dirs.mapM fun dir => inputDir dir false (·.extension == some "bin")
  return (Job.collectArray jobs).map (·.flatten)

@[default_target]
lean_lib Base16ct where
  srcDir := repositoryRoot
  roots := #[`Base16ct.Spec, `Base16ct.Statements, `Base16ct.Proofs, `Base16ct.Tests]
  needs := #[base16ct_bins]
