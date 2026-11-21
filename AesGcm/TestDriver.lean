import AesGcm.Tests

/-! Test driver of this package: `lake test` runs `AesGcm.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  AesGcm.Tests.run
