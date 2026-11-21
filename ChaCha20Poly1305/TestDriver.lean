import ChaCha20Poly1305.Tests

/-! Test driver of this package: `lake test` runs `ChaCha20Poly1305.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  ChaCha20Poly1305.Tests.run
