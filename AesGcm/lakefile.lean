import Lake
open Lake DSL

/-!
`aes-gcm` as its own Lake package, so it can pin its own lean-x86 and lean-x86-proofs. Run every
command from this directory. Sources stay where they are in the repository: the libraries read
them from the repository root, including the shared `Standards` definitions, which this package
builds with its own pins.
-/

package aes_gcm where
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

/-- The extracted sections embedded with `include_bytes`. Only `Spec/` holds `.bin` files: the
crate directory itself would also take those in `.lake/`. -/
input_dir aes_gcm_bins where
  path := "Spec"
  filter := .extension "bin"

@[default_target]
lean_lib AesGcm where
  srcDir := repositoryRoot
  roots := #[`AesGcm.Spec, `AesGcm.Statements, `AesGcm.Proofs, `AesGcm.Tests]
  needs := #[aes_gcm_bins]
