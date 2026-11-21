"""Exercise the dependency check against real Lean builds, including indirect imports."""

from pathlib import Path
import json
import subprocess
import tempfile
import unittest

from check_spec_dependencies import audit, check, specification_modules
from comparator import spec_inputs, stage


class SpecDependenciesTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="spec-dependencies-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        repository = Path(__file__).resolve().parent.parent
        self.write("Demo/comparator.config.json", json.dumps({"challenge_module": "Demo.Statements"}))
        self.write("lean-toolchain", (repository / "lean-toolchain").read_text())
        self.write("lakefile.toml", '''name = "spec_check_fixture"
[[require]]
name = "x86proofs"
path = "vendor/x86proofs"
[[lean_lib]]
name = "Demo"
''')
        # A differently named module tests package ownership, not just namespace matching.
        self.write("vendor/x86proofs/lakefile.toml", '''name = "x86proofs"
[[lean_lib]]
name = "Hidden"
''')
        self.write("vendor/x86proofs/lake-manifest.json", json.dumps({
            "version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
            "name": "x86proofs", "lakeDir": ".lake", "fixedToolchain": False,
        }))
        self.write("vendor/x86proofs/Hidden.lean", "def proofLibraryValue : Nat := 1\n")
        self.write("Demo/Spec/Base.lean", "-- import Hidden is only a comment.\ndef specValue : Nat := 0\n")
        self.write("Demo/Statements.lean", "import Demo.Spec.Base\nexample : specValue = 0 := rfl\n")
        self.write("Demo/Proofs/Implementation.lean", "import Hidden\n")

    def write(self, name, contents):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)

    def test_accepts_independent_spec_and_rebuilds_changed_imports(self):
        check(self.root)
        self.write("Demo/Statements.lean", "import Demo.Spec.Base\nimport Hidden\n")
        with self.assertRaisesRegex(ValueError, "Demo.Statements -> Hidden"):
            check(self.root)
        self.write("Demo/Statements.lean", "import Demo.Spec.Base\n")
        check(self.root)

    def test_rejects_transitive_import(self):
        self.write("Demo/Bridge.lean", "import Hidden\n")
        self.write("Demo/Spec/Base.lean", "import Demo.Bridge\ndef specValue : Nat := 0\n")
        with self.assertRaisesRegex(ValueError, "Demo.Statements -> Hidden"):
            check(self.root)

    def test_checks_spec_modules_not_imported_by_statement(self):
        self.write("Demo/Spec/Unused.lean", "import Hidden\n")
        with self.assertRaisesRegex(ValueError, "Demo.Spec.Unused -> Hidden"):
            check(self.root)

    def test_checks_statement_submodules(self):
        self.write("Demo/Statements/Unused.lean", "import Hidden\n")
        with self.assertRaisesRegex(ValueError, "Demo.Statements.Unused -> Hidden"):
            check(self.root)

    def test_missing_metadata_fails(self):
        check(self.root)
        (self.root / ".lake/build/ir/Demo/Statements.setup.json").unlink()
        with self.assertRaises(FileNotFoundError):
            audit(self.root, specification_modules(self.root))

    def test_checks_modules_restored_without_metadata(self):
        # Lake writes no .setup.json for a module it restores from the artifact cache
        self.write("Demo/Spec/Unused.lean", "import Hidden\n")
        subprocess.run(["lake", "build", "Demo.Spec.Unused"], cwd=self.root, check=True)
        for path in (self.root / ".lake/build/ir").rglob("*.setup.json"):
            path.unlink()
        with self.assertRaisesRegex(ValueError, "Demo.Spec.Unused -> Hidden"):
            check(self.root)
        self.write("Demo/Spec/Unused.lean", "def unused := 0\n")
        subprocess.run(["lake", "build", "Demo.Spec.Unused"], cwd=self.root, check=True)
        for path in (self.root / ".lake/build/ir").rglob("*.setup.json"):
            path.unlink()
        check(self.root)

    def test_proofs_may_use_the_library(self):
        subprocess.run(["lake", "build", "Demo.Proofs.Implementation"], cwd=self.root, check=True)
        check(self.root)

    def test_rejects_proof_library_plugins_and_dynamic_libraries(self):
        check(self.root)
        path = self.root / ".lake/build/ir/Demo/Statements.setup.json"
        original = json.loads(path.read_text())
        for field, value in (("plugins", [{"path": "vendor/x86proofs/plugin.so"}]),
                             ("dynlibs", ["vendor/x86proofs/library.so"])):
            with self.subTest(field=field):
                setup = dict(original)
                setup[field] = value
                path.write_text(json.dumps(setup))
                with self.assertRaisesRegex(ValueError, "Specification/statement depends"):
                    audit(self.root, specification_modules(self.root))

    def test_all_crates_are_checked(self):
        self.write("Other/comparator.config.json", "{}\n")
        self.write("Other/Spec.lean", "import Hidden\n")
        with (self.root / "lakefile.toml").open("a") as out:
            out.write('[[lean_lib]]\nname = "Other"\n')
        with self.assertRaisesRegex(ValueError, "Other.Spec -> Hidden"):
            check(self.root)
        check(self.root, ["Demo"])

    def test_staging_keeps_unused_claim_modules_and_package_checker(self):
        check(self.root)
        self.write("lakefile.lean", "import Lake\n")
        self.write("Demo/Statements/Unused.lean", "def unusedStatement := True\n")
        self.write("Demo/Spec/Unused.lean", "def unusedSpec := True\n")
        temporary = self.root / "staging"
        temporary.mkdir()
        stage(self.root, temporary, "Demo")
        workspace = temporary / "challenge/workspace"
        self.assertTrue((workspace / "Demo/Statements/Unused.lean").is_file())
        self.assertTrue((workspace / "Demo/Spec/Unused.lean").is_file())
        self.assertTrue((temporary / "challenge/check_spec_dependencies.py").is_file())

    def test_staging_rejects_unused_claim_importing_proof_namespace(self):
        self.write("Demo/Statements/Unused.lean", "import X86Proofs\n")
        with self.assertRaisesRegex(RuntimeError, "Statement reaches the proof library"):
            spec_inputs(self.root, "Demo")

    def standalone(self):
        """Makes Demo a standalone crate: its own Lake package, reading its sources from the root."""
        self.write("Demo/lean-toolchain", (self.root / "lean-toolchain").read_text())
        self.write("Demo/lakefile.lean", 'import Lake\nopen Lake DSL\npackage demo\n'
                   'require x86proofs from "../vendor/x86proofs"\nlean_lib Demo where\n  srcDir := (__dir__).parent.get!\n')

    def test_standalone_crate_is_checked_in_its_own_project(self):
        self.standalone()
        check(self.root)
        self.assertTrue((self.root / "Demo/.lake/build/lib/lean/Demo/Statements.olean").is_file())
        self.assertFalse((self.root / ".lake/build").exists())
        self.write("Demo/Statements.lean", "import Demo.Spec.Base\nimport Hidden\n")
        with self.assertRaisesRegex(ValueError, "Demo.Statements -> Hidden"):
            check(self.root)

    def test_staging_standalone_crate_copies_its_own_package(self):
        self.standalone()
        check(self.root)
        temporary = self.root / "staging"
        temporary.mkdir()
        stage(self.root, temporary, "Demo")
        workspace = temporary / "challenge/workspace"
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            self.assertTrue((workspace / "Demo" / name).is_file(), name)
        self.assertTrue((workspace / "Demo/.lake/packages").is_symlink())
        self.assertFalse((workspace / "lakefile.toml").exists())
        self.assertFalse((workspace / ".lake").exists())


if __name__ == "__main__":
    unittest.main()
