import Md5.Tests

/-! Test driver of this package: `lake test` runs `Md5.Tests.run` from the repository root, where
the suite's vector paths start. -/

def main : IO Unit := do
  IO.Process.setCurrentDir ".."
  Md5.Tests.run
