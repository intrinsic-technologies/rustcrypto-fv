-- BEGIN CRATE IMPORTS
-- END CRATE IMPORTS
import Standards.Tests

/-!
# Test driver

In the root package, `lake test` runs the `Standards` suite, and
`lake test -- Standards.NIST.SHA2` one subject of it (`Standards.Tests.subjects`). Each crate is its
own package and runs its suite with `lake test` in its directory (`<Crate>/TestDriver.lean`).
-/

/-- Suites this package runs: the crates it builds, by directory name in alphabetical order, then
`Standards`. Standalone crates run their own suites (`<Crate>/TestDriver.lean`). -/
def suites : List (String × IO Unit) := [
  -- BEGIN CRATE SUITES
  -- END CRATE SUITES
  ("Standards", Standards.Tests.run),
]

/-- Suites that can be selected by name: the crates', `Standards`, and each `Standards` subject -/
def selectable : List (String × IO Unit) := suites ++ Standards.Tests.subjects

def main (args : List String) : IO UInt32 := do
  let unknown := args.filter fun name => !selectable.any (·.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"Unknown test suites: {unknown}; available: {selectable.map (·.1)}"
    return 2
  let selected := if args.isEmpty then suites else selectable.filter (args.contains ·.1)
  if selected.isEmpty then
    IO.println "No crate test suites registered"
  let mut failed := #[]
  for (name, suite) in selected do
    IO.println s!"== {name}"
    try
      suite
    catch error =>
      IO.eprintln s!"{name}: {error}"
      failed := failed.push name
  if failed.isEmpty then
    IO.println s!"{selected.length} suite(s) passed"
    return 0
  IO.eprintln s!"Failed suites: {failed}"
  return 1
