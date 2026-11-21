import P256.Tests

/-! Test driver of this package: `lake test` runs `P256.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  P256.Tests.run
