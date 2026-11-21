import Sha1.Tests

/-! Test driver of this package: `lake test` runs `Sha1.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  Sha1.Tests.run
