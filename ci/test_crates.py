"""Check which crates a change selects for each kind of check."""

from pathlib import Path
import json
import subprocess
import tempfile
import unittest

from crates import changed_crates, check, foreign_imports, matrix, test_suites, trust_escapes

LAKEFILE = """\
import Lake
open Lake DSL

package rustcrypto where

-- BEGIN CRATES
-- alpha
lean_lib Alpha where
  roots := #[`Alpha.Spec, `Alpha.Statements, `Alpha.Proofs, `Alpha.Tests]

-- beta
lean_lib Beta where
  roots := #[`Beta.Spec, `Beta.Statements, `Beta.Proofs, `Beta.Tests]
-- END CRATES
"""

DRIVER = """\
-- BEGIN CRATE IMPORTS
import Alpha.Tests
import Beta.Tests
-- END CRATE IMPORTS
import Standards.Tests

def suites : List (String × IO Unit) := [
  -- BEGIN CRATE SUITES
  ("Alpha", Alpha.Tests.run),
  ("Beta", Beta.Tests.run),
  -- END CRATE SUITES
  ("Standards", Standards.Tests.run),
]
"""

FILES = {
    "lakefile.lean": LAKEFILE,
    "lean-toolchain": "leanprover/lean4:v4.0.0\n",
    "Standards.lean": "import Standards.Hash\nimport Standards.Curve\n",
    "Standards/Hash.lean": "def hash := 0\n",
    "Standards/Curve.lean": "import Standards.Field\n",
    "Standards/Field.lean": "def field := 0\n",
    "Standards/Unused.lean": "def unused := 0\n",
    "Alpha/Spec.lean": "import Standards.Hash\n",
    "Alpha/Statements.lean": "import Alpha.Spec\n",
    "Alpha/Proofs.lean": "import Alpha.Spec\n",
    "Alpha/Tests.lean": "import Alpha.Spec\n-- reads \"Alpha/Tests/Vectors/kat.txt\"\n",
    "Alpha/Tests/Vectors/kat.txt": "00\n",
    "Beta/Spec.lean": "import Standards.Curve\n",
    "Beta/Statements.lean": "import Beta.Spec\n",
    "Beta/Proofs.lean": "import Beta.Spec\n" + "-- padding\n" * 100,
    "Beta/Tests.lean": "import Beta.Spec\n",
    "Alpha/comparator.config.json": json.dumps({"theorem_names": ["Alpha.Statements.t"]}),
    "Beta/comparator.config.json": json.dumps({"theorem_names": ["Beta.Statements.t"]}),
    "ci/comparator.py": "",
    "ci/crates.py": "",
    "Tests.lean": DRIVER,
    "Standards/Tests.lean": "import Standards.Hash.Tests\nimport Standards.Curve.Tests\n",
    "Standards/Hash/Tests.lean": "import Standards.Hash\n-- reads \"Standards/Hash/Vectors/vectors.txt\"\n",
    "Standards/Hash/Vectors/vectors.txt": "00\n",
    "Standards/Curve/Tests.lean": "import Standards.Curve\n",
}


class ChangedCrates(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.git("init", "-q", "-b", "main")
        for path, text in FILES.items():
            self.write(path, text)
        self.commit()
        self.base = self.git("rev-parse", "HEAD")

    def tearDown(self):
        self.directory.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                                       cwd=self.root, text=True).strip()

    def write(self, path, text):
        (self.root / path).parent.mkdir(parents=True, exist_ok=True)
        (self.root / path).write_text(text)

    def commit(self):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "change")

    def change(self, path, text):
        self.write(path, text)
        self.commit()

    def selected(self, kind="comparator", eligible=("Alpha", "Beta")):
        return changed_crates(self.root, self.base, kind, list(eligible))

    def test_unimported_standard_selects_nothing(self):
        self.change("Standards/Unused.lean", "def unused := 1\n")
        self.assertEqual(self.selected(), [])
        self.assertEqual(self.selected("build"), [])

    def test_new_standard_selects_nothing(self):
        self.change("Standards/New.lean", "def new := 0\n")
        self.change("Standards.lean", FILES["Standards.lean"] + "import Standards.New\n")
        self.assertEqual(self.selected(), [])

    def test_standard_selects_crates_importing_it(self):
        self.change("Standards/Field.lean", "def field := 1\n")
        self.assertEqual(self.selected(), ["Beta"])

    def test_deleted_standard_selects_crates_importing_it(self):
        (self.root / "Standards/Hash.lean").unlink()
        self.commit()
        self.assertEqual(self.selected(), ["Alpha"])

    def test_new_crate_block_selects_only_that_crate(self):
        self.change("lakefile.lean", LAKEFILE.replace("-- END CRATES", "\n-- gamma\nlean_lib Gamma where\n  roots := #[]\n-- END CRATES"))
        self.write("Gamma/comparator.config.json", json.dumps({"theorem_names": []}))
        self.commit()
        self.assertEqual(self.selected("build", ("Alpha", "Beta", "Gamma")), ["Gamma"])
        self.assertEqual(self.selected(), [])

    def test_changed_crate_block_selects_that_crate(self):
        self.change("lakefile.lean", LAKEFILE.replace("`Beta.Tests]", "`Beta.Tests]\n  needs := #[]"))
        self.assertEqual(self.selected(), ["Beta"])

    def test_package_change_in_lakefile_selects_every_crate(self):
        self.change("lakefile.lean", LAKEFILE.replace("package rustcrypto where", "package rustcrypto where\n  x := 1"))
        self.assertEqual(self.selected(), ["Alpha", "Beta"])

    def test_unattributed_lakefile_change_selects_every_crate(self):
        self.change("lakefile.lean", LAKEFILE.replace("`Beta.Tests]", "`Beta.Tests]\n-- note\n  needs := #[]"))
        self.assertEqual(self.selected(), ["Alpha", "Beta"])

    def test_toolchain_selects_every_crate(self):
        self.change("lean-toolchain", "leanprover/lean4:v4.1.0\n")
        self.assertEqual(self.selected(), ["Alpha", "Beta"])

    def test_crate_selection_changes_select_nothing(self):
        self.change("ci/crates.py", "# changed\n")
        self.assertEqual(self.selected(), [])
        self.assertEqual(self.selected("build"), [])

    def test_comparator_tooling_selects_the_smallest_crate(self):
        self.change("ci/comparator.py", "# changed\n")
        self.assertEqual(self.selected(), ["Alpha"])
        self.assertEqual(self.selected(eligible=("Beta",)), ["Beta"])
        self.assertEqual(self.selected("build"), [])

    def test_comparator_tooling_with_a_selected_crate_adds_no_other(self):
        self.change("ci/comparator.py", "# changed\n")
        self.change("Beta/Proofs.lean", "import Beta.Spec\n")
        self.assertEqual(self.selected(), ["Beta"])

    def test_crate_change_selects_that_crate(self):
        self.change("Alpha/Proofs.lean", "import Alpha.Spec\n\n")
        self.assertEqual(self.selected(), ["Alpha"])

    def test_direct_leaves_out_crates_importing_a_changed_standard(self):
        self.change("Standards/Field.lean", "def field := 1\n")
        self.assertEqual(changed_crates(self.root, self.base, "comparator", ["Alpha", "Beta"], direct=True), [])

    def test_direct_leaves_out_crates_importing_a_changed_crate(self):
        self.change("Beta/Spec.lean", "import Standards.Curve\nimport Alpha.Spec\n")
        self.base = self.git("rev-parse", "HEAD")
        self.change("Alpha/Spec.lean", "import Standards.Hash\n\n")
        self.assertEqual(self.selected(), ["Alpha", "Beta"])
        self.assertEqual(changed_crates(self.root, self.base, "comparator", ["Alpha", "Beta"], direct=True), ["Alpha"])

    def test_direct_keeps_own_files_pins_and_tooling(self):
        direct = lambda: changed_crates(self.root, self.base, "comparator", ["Alpha", "Beta"], direct=True)
        self.change("ci/comparator.py", "# changed\n")
        self.assertEqual(direct(), ["Alpha"])
        self.change("Beta/Proofs.lean", "import Beta.Spec\n")
        self.assertEqual(direct(), ["Beta"])
        self.change("lean-toolchain", "leanprover/lean4:v4.1.0\n")
        self.assertEqual(direct(), ["Alpha", "Beta"])

    def test_direct_keeps_lakefile_blocks_and_manifest(self):
        direct = lambda: changed_crates(self.root, self.base, "comparator", ["Alpha", "Beta"], direct=True)
        self.change("lakefile.lean", LAKEFILE.replace("`Beta.Tests]", "`Beta.Tests]\n  needs := #[]"))
        self.assertEqual(direct(), ["Beta"])
        self.change("lake-manifest.json", "{}\n")
        self.assertEqual(direct(), ["Alpha", "Beta"])

    def test_direct_with_standard_and_own_change_selects_only_the_owner(self):
        self.change("Standards/Hash.lean", "def hash := 1\n")
        self.change("Beta/Statements.lean", "import Beta.Spec\n\n")
        self.assertEqual(self.selected(), ["Alpha", "Beta"])
        self.assertEqual(changed_crates(self.root, self.base, "comparator", ["Alpha", "Beta"], direct=True), ["Beta"])

    def test_trusted_code_without_escapes_passes(self):
        self.write("Standards/Field.lean", "/- an axiom, by sorry -/\n-- native_decide\ndef field := \"sorry\"\n")
        self.write("Alpha/Spec/Char.lean", "def quote := '\"'\ndef q' := 0\n")
        self.write("Standards/Hash/Tests.lean", "example : 1 = 1 := by native_decide\n")
        self.assertEqual(trust_escapes(self.root), [])

    def test_trusted_code_with_escapes_fails(self):
        self.write("Standards/Field.lean", "axiom field_ok : True\n")
        self.write("Beta/Spec.lean", "import Standards.Curve\ntheorem t : True := by sorry\n")
        self.write("Alpha/Spec/Fast.lean", "example : 2 + 2 = 4 := by decide +native\n")
        errors = trust_escapes(self.root)
        self.assertEqual([error.split(" uses ")[0] for error in errors],
                         ["Alpha/Spec/Fast.lean", "Beta/Spec.lean", "Standards/Field.lean"])

    def test_modules_importing_their_crate_and_standards_pass(self):
        self.write("Alpha/Spec/Core.lean", "import Alpha.Spec.Util\nimport Standards.Hash\nimport Mathlib.Data\n")
        self.write("Alpha/Statements/Main.lean", "import Alpha.Spec\nimport Standards.Field\n")
        self.write("Alpha/Proofs/Main.lean", "import Alpha.Spec\nimport Alpha.Proofs.Lemmas\nimport X86Proofs\n")
        self.write("Alpha/Tests/Main.lean", "import Alpha.Spec\nimport Standards.Hash.Tests\n")
        self.assertEqual(foreign_imports(self.root), [])

    def test_modules_importing_another_crate_fail(self):
        self.write("Alpha/Spec/Core.lean", "import Beta.Spec\n")
        self.write("Alpha/Statements.lean", "import Alpha.Spec\nimport Beta.Spec.Curve\n")
        self.write("Alpha/Tests/Main.lean", "import Alpha.Spec\nimport Beta.Tests\n")
        self.write("Alpha/Proofs/Main.lean", "import Alpha.Spec\nimport Beta.Proofs.Lemmas\n")
        self.write("Beta/Proofs.lean", "import Beta.Spec\nimport Alpha.Spec\n")
        self.write("Beta/TestDriver.lean", "import Beta.Tests\nimport Alpha.Tests\n")
        errors = foreign_imports(self.root)
        self.assertEqual([error.split(";")[0] for error in errors],
                         ["Alpha: Alpha/Proofs/Main.lean imports Beta.Proofs.Lemmas",
                          "Alpha: Alpha/Spec/Core.lean imports Beta.Spec",
                          "Alpha: Alpha/Statements.lean imports Beta.Spec.Curve",
                          "Alpha: Alpha/Tests/Main.lean imports Beta.Tests",
                          "Beta: Beta/Proofs.lean imports Alpha.Spec",
                          "Beta: Beta/TestDriver.lean imports Alpha.Tests"])

    def test_package_directories_are_ignored(self):
        self.write("Alpha/.lake/packages/beta/Beta/Spec.lean", "import Alpha.Spec\n")
        self.write("Alpha/.lake/packages/beta/Alpha/Spec.lean", "import Beta.Spec\n")
        self.assertEqual(foreign_imports(self.root), [])

    def test_standards_importing_a_crate_fail(self):
        self.write("Standards.lean", "import Standards.Hash\nimport Standards.Curve\nimport Alpha.Spec\n")
        self.write("Standards/Field.lean", "import Beta.Spec.Curve\n")
        errors = foreign_imports(self.root)
        self.assertEqual([error.split(";")[0] for error in errors],
                         ["Standards: Standards/Field.lean imports Beta.Spec.Curve",
                          "Standards: Standards.lean imports Alpha.Spec"])

    def test_selection_keeps_only_eligible_crates(self):
        self.change("lean-toolchain", "leanprover/lean4:v4.1.0\n")
        self.assertEqual(self.selected(eligible=("Beta",)), ["Beta"])


    def suites(self):
        return test_suites(self.root, self.base)

    def test_standard_selects_its_subject_and_crates_testing_it(self):
        self.change("Standards/Field.lean", "def field := 1\n")
        self.assertEqual(self.suites(), ["Beta", "Standards.Curve"])

    def test_vectors_select_the_suites_that_read_them(self):
        self.change("Standards/Hash/Vectors/vectors.txt", "01\n")
        self.assertEqual(self.suites(), ["Standards.Hash"])
        self.base = self.git("rev-parse", "HEAD")
        self.change("Alpha/Tests/Vectors/kat.txt", "01\n")
        self.assertEqual(self.suites(), ["Alpha"])
        self.assertEqual(changed_crates(self.root, self.base, "tests", ["Alpha", "Beta"]), ["Alpha"])

    def test_vectors_named_by_no_suite_select_their_owner(self):
        self.change("Standards/Curve/Vectors/new.txt", "00\n")
        self.assertEqual(self.suites(), ["Standards.Curve"])

    def test_vectors_with_no_reader_or_owner_select_every_suite(self):
        self.change("Standards/Orphan/Vectors/x.txt", "00\n")
        self.assertEqual(self.suites(), ["Alpha", "Beta", "Standards"])

    def test_new_standards_registration_selects_only_that_subject(self):
        self.write("Standards/Field/Tests.lean", "import Standards.Field\n")
        self.change("Standards/Tests.lean", FILES["Standards/Tests.lean"] + "import Standards.Field.Tests\n")
        self.assertEqual(self.suites(), ["Standards.Field"])
        self.assertEqual(changed_crates(self.root, self.base, "tests", ["Alpha", "Beta"]), [])

    def test_subject_test_module_selects_only_that_subject(self):
        self.change("Standards/Curve/Tests.lean", "import Standards.Curve\n\n")
        self.assertEqual(self.suites(), ["Standards.Curve"])

    def test_crate_tests_select_only_that_crate(self):
        self.change("Alpha/Tests.lean", "import Alpha.Spec\n\n")
        self.assertEqual(self.suites(), ["Alpha"])

    def test_standards_registration_entries_count_as_registration(self):
        self.write("Standards/Field/Tests.lean", "import Standards.Field\n")
        self.change("Standards/Tests.lean", FILES["Standards/Tests.lean"] + "import Standards.Field.Tests\n"
                    + '  ("Standards.Field", Field.Tests.run),\n')
        self.assertEqual(self.suites(), ["Standards.Field"])

    def test_standards_driver_code_selects_all_standards_only(self):
        self.change("Standards/Tests.lean", FILES["Standards/Tests.lean"] + "def extra := 0\n")
        self.assertEqual(self.suites(), ["Standards"])

    def test_pins_select_every_suite(self):
        everything = ["Alpha", "Beta", "Standards"]
        self.change("lean-toolchain", "leanprover/lean4:v4.1.0\n")
        self.assertEqual(self.suites(), everything)

    def test_new_crate_registration_selects_only_that_crate(self):
        self.write("Gamma/comparator.config.json", json.dumps({"theorem_names": []}))
        self.write("Gamma/Tests.lean", "def run := 0\n")
        self.change("Tests.lean", DRIVER.replace("import Beta.Tests\n", "import Beta.Tests\nimport Gamma.Tests\n")
                    .replace("  -- END CRATE SUITES", "  (\"Gamma\", Gamma.Tests.run),\n  -- END CRATE SUITES"))
        self.assertEqual(self.suites(), ["Gamma"])

    def test_other_test_driver_change_selects_every_suite(self):
        self.change("Tests.lean", DRIVER + "\ndef main := 0\n")
        self.assertEqual(self.suites(), ["Alpha", "Beta", "Standards"])

    def test_unrelated_change_selects_no_suite(self):
        self.change("ci/crates.py", "# changed\n")
        self.assertEqual(self.suites(), [])

    def test_no_base_selects_every_suite(self):
        self.assertEqual(test_suites(self.root), ["Alpha", "Beta", "Standards"])


    def standalone_gamma(self):
        """Adds Gamma as a standalone crate, its own Lake package, and makes that the base."""
        self.write("Gamma/lakefile.lean", "import Lake\nopen Lake DSL\npackage gamma where\n"
                   "@[default_target, test_driver]\nlean_exe tests where\n  root := `TestDriver\n"
                   "lean_lib Gamma where\n  srcDir := (__dir__).parent.get!\n")
        self.write("Gamma/lake-manifest.json", "{}\n")
        self.write("Gamma/lean-toolchain", "leanprover/lean4:v4.0.0\n")
        self.write("Gamma/TestDriver.lean", "import Gamma.Tests\ndef main : IO Unit := Gamma.Tests.run\n")
        self.write("Gamma/comparator.config.json", json.dumps({
            "challenge_module": "Gamma.Statements", "solution_module": "Gamma.Proofs", "theorem_names": [],
            "permitted_axioms": ["propext"]}))
        self.write("Gamma/Spec.lean", "import Standards.Hash\n")
        self.write("Gamma/Statements.lean", "import Gamma.Spec\n")
        self.write("Gamma/Proofs.lean", "import Gamma.Spec\n")
        self.write("Gamma/Tests.lean", "import Gamma.Spec\n")
        self.write("report/crates/gamma/page.mjs", "export default {\n  lean: 'Gamma',\n};\n")
        self.commit()
        self.base = self.git("rev-parse", "HEAD")

    def test_repository_pins_do_not_select_a_standalone_crate(self):
        self.standalone_gamma()
        everything = ("Alpha", "Beta", "Gamma")
        self.change("lean-toolchain", "leanprover/lean4:v4.1.0\n")
        self.change("lake-manifest.json", "{}\n")
        self.change("lakefile.lean", LAKEFILE.replace("package rustcrypto where", "package rustcrypto where\n  x := 1"))
        self.change("Tests.lean", DRIVER + "\ndef main := 0\n")
        for kind in ("build", "tests", "comparator"):
            self.assertEqual(self.selected(kind, everything), ["Alpha", "Beta"])
        self.assertEqual(self.suites(), ["Alpha", "Beta", "Standards"])

    def test_standalone_package_files_select_that_crate(self):
        self.standalone_gamma()
        everything = ("Alpha", "Beta", "Gamma")
        self.change("Gamma/lake-manifest.json", "{\"packages\": []}\n")
        for kind in ("build", "tests", "comparator"):
            self.assertEqual(self.selected(kind, everything), ["Gamma"])
        self.assertEqual(self.selected("extraction", everything), [])
        self.base = self.git("rev-parse", "HEAD")
        self.change("Gamma/TestDriver.lean", "import Gamma.Tests\n")
        self.assertEqual(self.suites(), ["Gamma"])

    def test_standards_still_select_a_standalone_crate(self):
        self.standalone_gamma()
        self.change("Standards/Hash.lean", "def hash := 1\n")
        self.assertEqual(self.selected("build", ("Alpha", "Beta", "Gamma")), ["Alpha", "Gamma"])
        self.assertIn("Gamma", self.suites())

    def test_standalone_crate_runs_lake_in_its_directory(self):
        self.standalone_gamma()
        self.assertEqual({entry["crate"]: entry["project"] for entry in matrix(self.root, ["Alpha", "Gamma"])},
                         {"Alpha": ".", "Gamma": "Gamma"})
        self.assertEqual(test_suites(self.root), ["Alpha", "Beta", "Gamma", "Standards"])

    def gamma_errors(self):
        return [error for error in check(self.root) if error.startswith("Gamma:")]

    def test_standalone_crate_follows_the_conventions(self):
        self.standalone_gamma()
        self.assertEqual(self.gamma_errors(), [])

    def test_standalone_crate_must_not_be_registered_in_the_repository(self):
        self.standalone_gamma()
        self.write("lakefile.lean", LAKEFILE.replace("-- END CRATES", "-- gamma\nlean_lib Gamma where\n-- END CRATES"))
        self.write("Tests.lean", DRIVER.replace("import Beta.Tests\n", "import Beta.Tests\nimport Gamma.Tests\n"))
        errors = self.gamma_errors()
        self.assertTrue(any("must not declare lean_lib Gamma" in error for error in errors), errors)
        self.assertTrue(any("Tests.lean must not register" in error for error in errors), errors)

    def test_standalone_crate_needs_its_package_files_and_test_driver(self):
        self.standalone_gamma()
        (self.root / "Gamma/lean-toolchain").unlink()
        self.write("Gamma/TestDriver.lean", "def main : IO Unit := pure ()\n")
        self.write("Gamma/lakefile.lean", "import Lake\nopen Lake DSL\npackage gamma where\n")
        errors = self.gamma_errors()
        for expected in ("must declare `lean_lib Gamma`", "must declare a `test_driver` executable",
                         "needs its own lean-toolchain", "must run Gamma.Tests.run"):
            self.assertTrue(any(expected in error for error in errors), (expected, errors))


if __name__ == "__main__":
    unittest.main()
