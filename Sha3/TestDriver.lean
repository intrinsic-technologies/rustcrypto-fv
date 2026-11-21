import Sha3.Tests

/-! Test driver of this package: `lake test` runs `Sha3.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  Sha3.Tests.run
