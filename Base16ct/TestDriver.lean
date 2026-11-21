import Base16ct.Tests

/-! Test driver of this package: `lake test` runs `Base16ct.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  Base16ct.Tests.run
