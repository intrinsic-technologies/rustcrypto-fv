import Lake
open Lake DSL

/-!
The shared Lean definitions of published standards (`Standards`) and their tests. Each crate
directory is its own Lake package (`<Crate>/lakefile.lean`) with the same pins, so this package
declares no crate. `scripts/extract.py` builds the extractor from this package's lean-x86 checkout.
-/

package rustcrypto where
  enableArtifactCache := true
  restoreAllArtifacts := true

require x86 from git
  "git@github.com:intrinsic-technologies/lean-x86.git" @ "v0.0.2"

/-- Proof library for lean-x86 programs, available to proofs only: `ci/crates.py check` rejects
specification and statement modules that import it. -/
require x86proofs from git
  "git@github.com:intrinsic-technologies/lean-x86-proofs.git" @ "v0.0.2"

/-- Runs the `Standards` tests; `lake test -- Standards.NIST.SHA2` selects one subject. -/
@[default_target, test_driver]
lean_exe tests where
  root := `Tests

/-- Lean definitions of published cryptographic standards, shared by the crates. -/
@[default_target]
lean_lib Standards where
  roots := #[`Standards, `Standards.Tests]

-- BEGIN CRATES
-- END CRATES
