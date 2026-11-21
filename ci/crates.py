#!/usr/bin/env python3

"""Crate discovery and repository checks

A crate is a top-level directory with a `comparator.config.json`, named like its Lean library
(`Sha2/` for the `sha2` crate). A crate is either a library of the repository's Lake package or,
like every crate in this repository, a standalone crate: its own Lake package, with a
`lakefile.lean`, `lake-manifest.json` and `lean-toolchain` in its directory, so that it can pin its
own dependencies. Its libraries read their sources from the repository root (an absolute
`srcDir`, the parent of `__dir__`), its `TestDriver.lean` runs its suite, and every Lake command
for it runs in its directory. The repository's pins and registrations do not apply to it.
Commands:

list:   Prints crate directories, one per line, or `--json` for a GitHub Actions matrix whose
        `project` is the directory to run Lake in.
        `--changed-since REF --kind KIND` keeps only crates that the changes since the merge
        base with REF affect for that kind of check (see CHECKS and changed_crates): crates
        whose relevant files or lakefile.lean blocks changed, crates importing them, crates
        importing a changed shared standard module, one crate when the check's tooling changed,
        and every crate when relevant shared files changed. `--direct` leaves out the crates
        selected only because they import a changed crate or shared standard module.
        `--require program` keeps crates with an extraction program, and `--require theorems`
        crates with comparator theorems.
paths:  Prints the path filters of a kind of check, as each workflow's `paths:` lists them.
tests:  Prints the `lake test` suites to run, one per line: the crates' suites and the `Standards`
        subjects that the changes since the merge base with `--changed-since REF` affect
        (test_suites), or every crate and `Standards` without it. A standalone crate's suite runs
        with `lake test` in its directory, the others with the repository's test driver.
check:  Checks that each crate is registered and follows the repository conventions, and that
        workflow path filters match CHECKS.
scope:  `--changed-since REF` checks that the changes since the merge base with REF keep
        specification and proofs in separate pull requests: a pull request that changes a
        crate's proofs (or the theorems it claims) changes nothing but proofs, claimed
        theorems, and report files.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parent))
from comparator import (  # noqa: E402
    PROOF_LIBRARIES, imports, is_trusted_module, local_closure, module_path, proof_library_imports,
)

ROOT = Path(__file__).resolve().parent.parent
CRATE_NAME = re.compile(r"[A-Z][A-Za-z0-9]*")
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
SKILLS = (".claude/skills", ".agents/skills")

# Files every expensive check depends on: the Lake package, its pins, and crate selection
COMMON = ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "ci/crates.py", "ci/comparator.py",
          ".github/workflows/crates.yml")
# Of COMMON, the toolchain and dependency pins select every crate, and lakefile.lean the crates
# whose block changed (lakefile_crates). The others select crates without changing any crate's
# result, so they select none, though each workflow still runs them in its selection job.
PACKAGE = ("lean-toolchain", "lake-manifest.json")
LAKEFILE = "lakefile.lean"
# The test driver, whose crate registrations between its CRATE markers select those crates
TEST_DRIVER = "Tests.lean"
# A standalone crate's Lake package files, which select it as the repository's PACKAGE files select
# the other crates, and its test driver
STANDALONE = ("lakefile.lean", "lake-manifest.json", "lean-toolchain")
STANDALONE_TEST_DRIVER = "TestDriver.lean"
SPEC = ("Spec.lean", "Spec/**", "Statements.lean", "Statements/**")
PROOFS = ("Proofs.lean", "Proofs/**")
STANDARDS = ("Standards.lean", "Standards/**/*.lean")
# For each kind of check: the shared files and the crate-relative files it depends on, as GitHub
# path filter globs. A change to a shared file selects every crate; a change to a `tooling` file
# selects only the smallest crate, which exercises the tooling; a change to a shared standard
# module selects the crates whose `roots` import it, directly or not; and a change to a
# crate's file selects that crate and (`dependents`) the crates importing it. Each workflow's
# `paths:` filters are COMMON, the shared and tooling files, STANDARDS for kinds with
# `roots`, and `*/` before each crate glob; `check` keeps them in sync.
CHECKS = {
    "build": {
        "shared": ("ci/ClaimImports.lean", "ci/check_spec_dependencies.py", "ci/test_spec_dependencies.py",
                   ".github/workflows/build.yml"),
        "roots": ("Spec", "Statements", "Proofs", "Tests"),
        "crate": ("**/*.lean", "**/*.bin", *STANDALONE),
        "dependents": True,
    },
    "tests": {
        "shared": (".github/workflows/tests.yml",),
        # The Standards test driver: its imports register subjects, and a change selects the
        # subjects it adds or whose import line changed, never a crate (`registered_subjects`)
        "standards_registry": "Standards/Tests.lean",
        # Tests read vectors at run time, by paths imports do not show: a changed vector file selects
        # the suites whose test sources name its `Vectors` directory (`vector_readers`)
        "vectors": ("Standards/**/Vectors/**", "*/Tests/Vectors/**"),
        "registry": TEST_DRIVER,
        "roots": ("Tests",),
        "crate": ("Spec.lean", "Spec/**", "Tests.lean", "Tests/**", *STANDALONE, STANDALONE_TEST_DRIVER),
        "dependents": True,
    },
    "extraction": {
        "shared": ("scripts/extract.py", "scripts/layout.ld", "ci/check-extraction.sh",
                   ".github/workflows/extraction.yml"),
        "crate": ("program/**", "**/Extracted/**"),
        "dependents": False,
    },
    "comparator": {
        "shared": (),
        "tooling": ("ci/comparator.py", "ci/setup-comparator.sh", "ci/landrun.sh", "ci/ClaimImports.lean",
                    "ci/check_spec_dependencies.py", "ci/test_spec_dependencies.py",
                    ".github/workflows/comparator.yml"),
        "roots": ("Statements", "Proofs"),
        "crate": (*SPEC, *PROOFS, "comparator.config.json", *STANDALONE),
        "dependents": True,
    },
}
# Rust target required of every extracted program (lean-x86 formalizes x86-64-v1 in 64-bit mode)
RUST_TARGET = "x86_64-unknown-none"
RUST_CPU = "target-cpu=x86-64"


def glob_regex(pattern):
    """Translates a GitHub path filter glob: `*` stays within a directory, `**` crosses them."""
    regex = re.escape(pattern).replace(r"\*\*/", "(?:.*/)?").replace(r"\*\*", ".*").replace(r"\*", "[^/]*")
    return re.compile(regex.replace(r"\?", "[^/]") + r"\Z")


def matches(path, patterns):
    return any(glob_regex(pattern).match(path) for pattern in patterns)


def workflow_paths(kind):
    """The `paths:` filters of the workflow running one kind of check."""
    check = CHECKS[kind]
    shared = (*((check["standards_registry"],) if "standards_registry" in check else ()),
              *check.get("vectors", ()), *check["shared"],
              *((check["registry"],) if "registry" in check else ()),
              *check.get("tooling", ()),
              *(STANDARDS if "roots" in check else ()))
    shared = (*COMMON, *shared)
    return list(dict.fromkeys([*shared, *(f"*/{pattern}" for pattern in check["crate"])]))


def crates(root=ROOT):
    """Returns the crate directory names, sorted."""
    return sorted(path.name for path in root.iterdir()
                  if path.is_dir() and not path.name.startswith(".")
                  and (path / "comparator.config.json").is_file())


def standalone(root, crate):
    """Whether a crate is its own Lake package rather than a library of the repository's."""
    return (root / crate / LAKEFILE).is_file()


def crate_modules(root, crate):
    """Returns every Lean module in a crate directory."""
    return sorted(".".join(path.relative_to(root).with_suffix("").parts)
                  for path in (root / crate).rglob("*.lean") if ".lake" not in path.parts)


def config(root, crate):
    return json.loads((root / crate / "comparator.config.json").read_text())


def has_program(root, crate):
    return (root / crate / "program/extraction.toml").is_file()


def dependents(root, names):
    """Returns the crates importing modules of the given crates, transitively, including them."""
    all_crates = crates(root)
    uses = {crate: {module.split(".")[0] for module_name in crate_modules(root, crate)
                    for module in imports(root / module_path(module_name))} for crate in all_crates}
    affected = set(names) & set(all_crates)
    while True:
        more = {crate for crate in all_crates if uses[crate] & affected} - affected
        if not more:
            return sorted(affected)
        affected |= more


def imported_modules(root, modules):
    """Returns the modules reachable from `modules` by imports, including them. Unlike
    `local_closure`, it keeps imported modules without a source file, such as deleted ones."""
    seen, pending = set(), list(modules)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        if (root / module_path(module)).is_file():
            pending += imports(root / module_path(module))
    return seen


def lakefile_blocks(text):
    """Splits lakefile.lean into each crate's block between the CRATES markers, by the library it
    declares, and the rest of the file, or returns None if the markers are missing."""
    head, begin, rest = text.partition("-- BEGIN CRATES\n")
    body, end, tail = rest.partition("-- END CRATES")
    if not begin or not end:
        return None
    blocks, other = {}, [head, tail]
    for block in re.split(r"^(?=-- )", body, flags=re.M):
        library = re.search(r"^lean_lib (\w+) where$", block, re.M)
        if library:
            blocks[library.group(1)] = block.strip()
        else:
            other.append(block.strip())
    return other, blocks


def lakefile_crates(root, merge_base):
    """Returns the crates whose lakefile.lean block changed since `merge_base`, or None if anything
    outside the blocks changed, which may affect every crate."""
    before, after = (lakefile_blocks(show(root, revision, LAKEFILE) or "") for revision in (merge_base, "HEAD"))
    if before is None or after is None or before[0] != after[0]:
        return None
    return {name for name in before[1].keys() | after[1].keys() if before[1].get(name) != after[1].get(name)}


def registered_crates(root, merge_base):
    """Returns the crates whose registration lines between the test driver's CRATE markers changed
    since `merge_base`, or None if anything else in it changed, which may affect every suite."""
    def split(text):
        registrations, other, inside = set(), [], False
        for line in (text or "").splitlines():
            if re.fullmatch(r"\s*-- (BEGIN|END) CRATE \w+", line):
                inside = "BEGIN" in line
                other.append(line)
            elif inside:
                registrations.add(line.strip())
            else:
                other.append(line)
        return other, registrations
    (other_before, before), (other_after, after) = (split(show(root, revision, TEST_DRIVER))
                                                    for revision in (merge_base, "HEAD"))
    if other_before != other_after:
        return None
    return {match.group(1) for line in before ^ after
            for match in [re.search(r"\b([A-Z]\w*)\.Tests\b", line)] if match}


def smallest(root, names):
    """Returns the crate with the least Lean source, the cheapest to check, among `names`."""
    def size(crate):
        return sum(path.stat().st_size for path in (root / crate).rglob("*.lean") if ".lake" not in path.parts)
    return min(names, key=lambda crate: (size(crate), crate))


def merge_base_changes(root, base):
    """Returns the merge base with `base` and the paths changed between it and HEAD."""
    merge_base = subprocess.check_output(["git", "merge-base", base, "HEAD"], cwd=root, text=True).strip()
    changed = subprocess.check_output(["git", "diff", "--name-only", "--no-renames", merge_base, "HEAD"],
                                      cwd=root, text=True).splitlines()
    return merge_base, changed


def test_sources(root):
    """Each test suite's Lean sources: a crate's `Tests.lean` and `Tests/`, a `Standards` subject's
    `Tests.lean` and the modules beside it."""
    sources = {crate: [root / crate / "Tests.lean", *(root / crate / "Tests").rglob("*.lean")]
               for crate in crates(root)}
    for subject in standards_subjects(root):
        directory = root / Path(*subject.split("."))
        sources[subject] = [*directory.rglob("*.lean")] if directory.is_dir() else \
            [root / Path(*subject.split(".")).with_suffix(".lean")]
    return sources


def registered_subjects(root, merge_base):
    """The `Standards` subjects `Standards/Tests.lean` registers now and did not at `merge_base`."""
    before = show(root, merge_base, "Standards/Tests.lean") or ""
    old = set(re.findall(r"^import (Standards\.\S+)\.Tests$", before, re.M))
    return set(standards_subjects(root)) - old


def registry_imports_only(root, merge_base):
    """Whether `Standards/Tests.lean` changed only in its subject registrations (an import line and
    a `("Standards.…", ….Tests.run),` entry) since `merge_base`."""
    strip = lambda text: re.sub(r'^(import .*|\s*\("Standards\.[\w.]+", [\w.]+\.Tests\.run\),)\n', "",
                                text or "", flags=re.M).strip()
    return strip(show(root, merge_base, "Standards/Tests.lean")) == strip(show(root, "HEAD", "Standards/Tests.lean"))


def vector_readers(root, path):
    """The suites whose test sources name the `Vectors` directory holding `path`, and the suite
    whose directory holds it, or None if there are none, so that the caller runs every suite."""
    directory = path[:path.index("/Vectors/") + len("/Vectors")]
    readers = {suite for suite, files in test_sources(root).items()
               if any(directory in file.read_text(errors="ignore") for file in files if file.is_file())}
    # A test may build the path from parts; the suite owning the directory reads it then
    top = path.split("/")[0]
    owners = [subject for subject in standards_subjects(root)
              if path.startswith("/".join(subject.split(".")) + "/")] if top == "Standards" else \
        ([top] if top in crates(root) else [])
    if owners:
        readers.add(max(owners, key=len))
    return readers or None


def changed_crates(root, base, kind, eligible, direct=False):
    """Returns the crates among `eligible` whose `kind` check the changes since the merge base with
    `base` affect. With `direct`, a crate is selected only by changes to its own files or
    lakefile.lean block, the package pins, or the check's tooling, not because it imports a
    changed crate or shared standard module. The repository's package pins, and changes to its
    lakefile.lean or test driver outside the crate entries, select every crate but the standalone
    ones, which do not use them."""
    check = CHECKS[kind]
    all_crates = crates(root)
    merge_base, changed = merge_base_changes(root, base)
    touched, standards, tooling, readers, package = set(), set(), False, set(), False
    for path in changed:
        top, _, rest = path.partition("/")
        if matches(path, check["shared"]):
            return eligible
        if matches(path, PACKAGE):
            package = True
            continue
        if matches(path, check.get("vectors", ())):
            found = vector_readers(root, path)
            if found is None:
                return eligible
            readers |= found & set(all_crates)
            continue
        if path == check.get("standards_registry"):
            continue
        if path == LAKEFILE:
            blocks = lakefile_crates(root, merge_base)
            if blocks is None:
                package = True
            else:
                touched |= blocks & set(all_crates)
        elif path == check.get("registry"):
            registered = registered_crates(root, merge_base)
            if registered is None:
                package = True
            else:
                touched |= registered & set(all_crates)
        elif matches(path, check.get("tooling", ())):
            tooling = True
        elif "roots" in check and matches(path, STANDARDS):
            standards.add(".".join(Path(path).with_suffix("").parts))
        elif top in all_crates and matches(rest, check["crate"]):
            touched.add(top)
    if standards and not direct:
        touched |= {crate for crate in all_crates
                    if standards & imported_modules(root, [f"{crate}.{name}" for name in check["roots"]])}
    expand = check["dependents"] and not direct
    selected = (set(dependents(root, touched) if expand else touched) | readers) & set(eligible)
    if package:
        selected |= {crate for crate in eligible if not standalone(root, crate)}
    if tooling and eligible and not selected:
        selected.add(smallest(root, eligible))
    return sorted(selected)


def standards_subjects(root):
    """The `Standards` test subjects, by the name `Standards.Tests.subjects` gives each: every test
    module `Standards/Tests.lean` imports, without `.Tests`."""
    return sorted(module.removesuffix(".Tests") for module in imports(root / "Standards/Tests.lean")
                  if module.endswith(".Tests") and module.startswith("Standards."))


def test_suites(root, base=None):
    """Returns the `lake test` suites to run for the changes since the merge base with `base`:
    the crates `changed_crates` selects for tests, and each `Standards` subject whose test module
    imports a changed `Standards` module, directly or not. A change
    that selects every crate selects all of `Standards` too, as does no `base`, and a change to the
    repository's package selects every crate `changed_crates` selects for it and all of
    `Standards`."""
    everything = [*crates(root), "Standards"]
    if base is None:
        return everything
    names = crates(root)
    selected = changed_crates(root, base, "tests", names)
    merge_base, changed = merge_base_changes(root, base)
    check = CHECKS["tests"]
    vector_paths = [path for path in changed if matches(path, check["vectors"])]
    vector_suites = [vector_readers(root, path) for path in vector_paths]
    if any(found is None for found in vector_suites) or \
            any(matches(path, check["shared"]) for path in changed):
        return everything
    if any(matches(path, PACKAGE) for path in changed) or \
            (LAKEFILE in changed and lakefile_crates(root, merge_base) is None) or \
            (TEST_DRIVER in changed and registered_crates(root, merge_base) is None):
        return [*selected, "Standards"]
    modules = {".".join(Path(path).with_suffix("").parts) for path in changed if matches(path, STANDARDS)}
    subjects = [subject for subject in standards_subjects(root)
                if modules & imported_modules(root, [f"{subject}.Tests"])]
    subjects = sorted(set(subjects) | {suite for found in vector_suites for suite in found
                                       if suite.startswith("Standards.")}
                      | (registered_subjects(root, merge_base) if check["standards_registry"] in changed else set()))
    if check["standards_registry"] in changed and not registry_imports_only(root, merge_base):
        return [*selected, "Standards"]
    return [*selected, *subjects]


def show(root, revision, path):
    """Returns a file's contents at a revision, or None if it does not exist there."""
    result = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=root, capture_output=True, text=True)
    return result.stdout if result.returncode == 0 else None


def classify(root, base):
    """Splits the changes since the merge base with `base` into proof changes and the others."""
    merge_base, changed = merge_base_changes(root, base)
    all_crates = set(crates(root)) | {path.split("/")[0] for path in changed
                                      if show(root, merge_base, f"{path.split('/')[0]}/comparator.config.json")}
    proof_files, other_files = [], []
    for path in changed:
        top, _, rest = path.partition("/")
        if top in all_crates and rest == "comparator.config.json":
            before, after = show(root, merge_base, path), show(root, "HEAD", path)
            before, after = (json.loads(text) if text else {} for text in (before, after))
            claims = before.get("theorem_names") != after.get("theorem_names")
            rest_changed = {k: v for k, v in before.items() if k != "theorem_names"} != \
                {k: v for k, v in after.items() if k != "theorem_names"}
            if claims and before:
                proof_files.append(f"{path} (theorem_names)")
            if rest_changed or (claims and not before):
                other_files.append(path)
        elif top in all_crates and matches(rest, PROOFS):
            # The scaffold's empty Proofs.lean belongs to the specification pull request
            if rest == "Proofs.lean" and not (show(root, "HEAD", path) or "").strip():
                other_files.append(path)
            else:
                proof_files.append(path)
        elif not (path.startswith("report/") or path in {
            f"dashboard/charts/{chart}.{extension}"
            for chart in ("completed-over-time", "lines-of-code-over-time", "lines-of-code", "x86-instructions", "lines-per-statement")
            for extension in ("png", "svg")
        }):
            other_files.append(path)
    return proof_files, other_files


def scope(root, base):
    """Returns violations of the separation of specification and proof pull requests."""
    proof_files, other_files = classify(root, base)
    if not proof_files:
        return []
    errors = ["this pull request changes proofs or claimed theorems, so it may change only "
              "<Crate>/Proofs.lean, <Crate>/Proofs/, theorem_names in comparator.config.json, report/, and dashboard/charts/. "
              "Open a separate specification pull request for:"]
    errors += [f"  {path}" for path in other_files if not path.startswith("report/")]
    errors.append("Proof changes in this pull request:")
    errors += [f"  {path}" for path in proof_files]
    return errors if any(not path.startswith("report/") for path in other_files) else []


def matrix(root, names):
    """One matrix entry per crate, with the facts workflows use to skip inapplicable jobs."""
    return [{
        "crate": crate,
        "project": crate if standalone(root, crate) else ".",
        "program": has_program(root, crate),
        "theorems": len(config(root, crate).get("theorem_names", [])),
    } for crate in names]


# Lean code that adds an axiom, an unproved result or an unchecked one. The shared trusted code
# (`Standards` and each crate's `Spec/`) must not contain it: on pull requests, comparator checks
# only the crates whose own files changed, so it would not see a crate's proofs start to depend on
# a changed module they import.
TRUST_ESCAPES = re.compile(r"(?<![\w'])(?:axiom|sorry|admit|native_decide|ofReduceBool|ofReduceNat|"
                           r"skipKernelTC)(?![\w'])|(?<!\w)\+native\b")
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")


def lean_code(text):
    """Lean source without comments (nested block comments included) and string literals."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            i = text.find("\n", i) if "\n" in text[i:] else len(text)
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append(' "" ')
        elif CHAR_LITERAL.match(text, i) and not (out and re.match(r"[\w.']", out[-1])):
            i = CHAR_LITERAL.match(text, i).end()
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def trust_escapes(root):
    """Returns `Standards` and `Spec` modules (not tests) that use an axiom, `sorry` or the like."""
    paths = [root / "Standards.lean", *(root / "Standards").rglob("*.lean"),
             *(path for crate in crates(root) for path in (root / crate / "Spec").rglob("*.lean")),
             *(root / crate / "Spec.lean" for crate in crates(root))]
    errors = []
    for path in sorted(paths):
        relative = path.relative_to(root)
        if not path.is_file() or ".lake" in relative.parts or "Tests" in relative.with_suffix("").parts:
            continue
        found = sorted(set(TRUST_ESCAPES.findall(lean_code(path.read_text()))))
        if found:
            errors.append(f"{relative} uses {', '.join(f'`{word}`' for word in found)}; shared specification "
                          "modules must not add axioms or unproved results, since comparator does not check "
                          "the crates importing them on pull requests")
    return errors


def foreign_imports(root):
    """Returns crate modules that import another crate's modules, and `Standards` modules that
    import any crate's. Every Lean file in a crate directory counts, outside hidden directories such
    as a standalone crate's `.lake/`, so a crate's import closure holds only its own modules,
    `Standards` and external packages."""
    names = set(crates(root))
    owners = [(crate, [*(root / crate).rglob("*.lean")], names - {crate}) for crate in sorted(names)]
    owners.append(("Standards", [root / "Standards.lean", *(root / "Standards").rglob("*.lean")], names))
    errors = []
    for owner, paths, banned in owners:
        for path in sorted(paths):
            relative = path.relative_to(root)
            if not path.is_file() or any(part.startswith(".") for part in relative.parts):
                continue
            foreign = sorted({module for module in imports(path) if module.split(".")[0] in banned})
            if not foreign:
                continue
            if owner == "Standards":
                errors.append(f"Standards: {relative} imports {', '.join(foreign)}; "
                              "standard definitions import no crate's modules")
            else:
                errors.append(f"{owner}: {relative} imports {', '.join(foreign)}; no module of a crate "
                              "imports another crate's modules, so that each crate builds on its own")
    return errors


def check(root):
    """Returns a list of convention violations."""
    errors = []
    lakefile = (root / "lakefile.lean").read_text()
    tests = (root / "Tests.lean").read_text()
    for crate in crates(root):
        def error(message):
            errors.append(f"{crate}: {message}")
        if not CRATE_NAME.fullmatch(crate):
            error("directory name must be an UpperCamelCase Lean library name")
            continue
        registered = bool(re.search(rf"^lean_lib {crate} where$", lakefile, re.M))
        if standalone(root, crate):
            own = (root / crate / LAKEFILE).read_text()
            if registered:
                error(f"is standalone ({crate}/{LAKEFILE}), so lakefile.lean must not declare lean_lib {crate}")
            if not re.search(rf"^lean_lib {crate} where$", own, re.M):
                error(f"{crate}/{LAKEFILE} must declare `lean_lib {crate}`")
            if not re.search(rf"^@\[[^\]]*\btest_driver\b[^\]]*\]\s*lean_exe \w+ where$", own, re.M):
                error(f"{crate}/{LAKEFILE} must declare a `test_driver` executable")
            for name in STANDALONE[1:]:
                if not (root / crate / name).is_file():
                    error(f"is standalone ({crate}/{LAKEFILE}), so it needs its own {name}")
            driver = root / crate / STANDALONE_TEST_DRIVER
            if not driver.is_file() or f"{crate}.Tests.run" not in driver.read_text():
                error(f"{crate}/{STANDALONE_TEST_DRIVER} must run {crate}.Tests.run")
        elif not registered:
            error(f"missing `lean_lib {crate}` block in lakefile.lean")
        cfg = config(root, crate)
        for key, expected in (("challenge_module", f"{crate}.Statements"), ("solution_module", f"{crate}.Proofs")):
            if cfg.get(key) != expected:
                error(f"comparator {key} must be {expected}")
        theorems = cfg.get("theorem_names")
        if not isinstance(theorems, list) or len(set(theorems)) != len(theorems):
            error("comparator theorem_names must be a list of distinct names")
            theorems = []
        statements = "\n".join(path.read_text() for path in
                               [root / crate / "Statements.lean", *(root / crate / "Statements").rglob("*.lean")]
                               if path.is_file())
        for theorem in theorems:
            if not theorem.startswith(f"{crate}.Statements."):
                error(f"theorem {theorem} must be in namespace {crate}.Statements")
            if not re.search(rf"^theorem\s+{re.escape(theorem.split('.')[-1])}\b", statements, re.M):
                error(f"theorem {theorem} is not stated in {crate}/Statements.lean")
        extra = set(cfg.get("permitted_axioms", [])) - PERMITTED_AXIOMS
        if extra:
            error(f"permitted_axioms beyond {sorted(PERMITTED_AXIOMS)}: {sorted(extra)}")
        if cfg.get("enable_nanoda", False) not in (False, True):
            error("enable_nanoda must be a boolean")
        for module in (f"{crate}.Spec", f"{crate}.Statements", f"{crate}.Proofs", f"{crate}.Tests"):
            if not (root / module_path(module)).is_file():
                error(f"missing {module_path(module)}")
                continue
            reached = set(local_closure(root, module))
            directory = root / module_path(module).with_suffix("")
            for path in sorted(directory.rglob("*.lean")):
                submodule = ".".join(path.relative_to(root).with_suffix("").parts)
                if submodule not in reached:
                    error(f"{module_path(module)} does not import {submodule}, so `lake build {crate}` skips it")
        if (root / module_path(f"{crate}.Statements")).is_file():
            untrusted = [module for module in local_closure(root, f"{crate}.Statements")
                         if not is_trusted_module(module, crate)]
            if untrusted:
                error(f"statement imports non-specification modules: {', '.join(untrusted)}")
        claim = sorted({module for root_module in (f"{crate}.Spec", f"{crate}.Statements")
                        for module in local_closure(root, root_module)})
        for found in proof_library_imports(root, claim):
            error(f"{found}; the specification and statement must not import the proof library "
                  f"({', '.join(PROOF_LIBRARIES)}), which only proofs may use")
        if (root / module_path(f"{crate}.Proofs")).is_file():
            if any(module.split(".")[1:2] == ["Statements"] for module in local_closure(root, f"{crate}.Proofs")):
                error("proofs must not import the statement; restate each theorem under the same name")
        proofs = sorted((root / crate / "Proofs").rglob("*.lean"))
        for proof in proofs:
            text = proof.read_text()
            if re.search(r"--|/-", text):
                error(f"{proof.relative_to(root)} contains a comment; proof files contain no comments")
            for word in ("sorry", "admit", "native_decide"):
                if re.search(rf"\b{word}\b", text):
                    error(f"{proof.relative_to(root)} uses `{word}`; merged proofs are complete")
        if proofs and not theorems:
            error("Proofs/ is not empty but theorem_names is, so comparator would not check it")
        manifest = root / crate / "program/Cargo.toml"
        if manifest.is_file():
            profile = tomllib.loads(manifest.read_text()).get("profile", {})
            if profile != {"release": {"panic": "abort"}}:
                error(f"{manifest.relative_to(root)} must use Cargo's default release profile with only "
                      f'[profile.release] panic = "abort"')
        cargo = root / crate / "program/.cargo/config.toml"
        if has_program(root, crate):
            build = tomllib.loads(cargo.read_text()).get("build", {}) if cargo.is_file() else {}
            flags = " ".join(build.get("rustflags", []))
            if build.get("target") != RUST_TARGET or not re.search(rf"(?:^|\s|-C\s*){re.escape(RUST_CPU)}\b", flags):
                error(f"{cargo.relative_to(root)} must set [build] target = \"{RUST_TARGET}\" and "
                      f"rustflags -C {RUST_CPU} (x86-64-v1), as lean-x86 formalizes")
        registered = f"import {crate}.Tests" in tests or f'("{crate}", {crate}.Tests.run)' in tests
        if standalone(root, crate):
            if registered:
                error(f"is standalone, so Tests.lean must not register {crate}.Tests.run; "
                      f"{crate}/{STANDALONE_TEST_DRIVER} runs it")
        elif f"import {crate}.Tests" not in tests or f'("{crate}", {crate}.Tests.run)' not in tests:
            error(f"{crate}.Tests.run is not registered in Tests.lean")
        if (root / crate / "program").is_dir() and not has_program(root, crate):
            error("program/ has no extraction.toml")
    for name in re.findall(r"^lean_lib (\w+) where$", lakefile, re.M):
        if name == "Standards":
            reached = set(local_closure(root, name))
            tested = set(local_closure(root, "Standards.Tests"))
            for path in [root / "Standards.lean", *(root / name).rglob("*.lean")]:
                module = ".".join(path.relative_to(root).with_suffix("").parts)
                if "Tests" in module.split("."):
                    if module not in tested and module != "Standards.Tests":
                        errors.append(f"Standards/Tests.lean does not import {module}")
                elif module not in reached:
                    errors.append(f"Standards.lean does not import {module}")
            for module in reached | tested:
                if not module.startswith("Standards.") and module != "Standards":
                    errors.append(f"Standards imports crate-specific module {module}")
            listed = re.findall(r'^  \("([\w.]+)", [\w.]+\.Tests\.run\),$',
                                (root / "Standards/Tests.lean").read_text(), re.M)
            if sorted(listed) != standards_subjects(root):
                errors.append("Standards.Tests.subjects must list each test module Standards/Tests.lean imports, "
                              "by its name without `.Tests`, as `ci/crates.py tests` selects them")
        elif name not in crates(root):
            errors.append(f"lakefile.lean declares lean_lib {name}, but {name}/comparator.config.json does not exist")
    for name in re.findall(r"^import (\w+)\.Tests$", tests, re.M):
        if name not in crates(root) and name != "Standards":
            errors.append(f"Tests.lean registers {name}, which is not a crate")
    errors += trust_escapes(root)
    errors += foreign_imports(root)
    for kind in CHECKS:
        workflow = root / ".github/workflows" / f"{kind}.yml"
        expected = sorted(workflow_paths(kind))
        blocks = re.findall(r"^ +paths:\n((?: +- .+\n)+)", workflow.read_text(), re.M) if workflow.is_file() else []
        found = [sorted(item.strip().removeprefix("- ").strip("'\"") for item in block.splitlines()) for block in blocks]
        if len(found) != 2 or any(paths != expected for paths in found):
            errors.append(f"{workflow.relative_to(root)}: pull_request and push paths must be "
                          f"`python3 ci/crates.py paths {kind}`")
    skills = [{path.relative_to(root / base): path.read_bytes()
               for path in (root / base).rglob("*") if path.is_file()} for base in SKILLS]
    if skills[0] != skills[1]:
        errors.append(f"{SKILLS[0]} and {SKILLS[1]} must contain identical skills")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    listing = commands.add_parser("list")
    listing.add_argument("--json", action="store_true", help="print a GitHub Actions matrix include list")
    listing.add_argument("--changed-since", metavar="REF", help="only crates affected since REF")
    listing.add_argument("--kind", choices=sorted(CHECKS), default="build", help="kind of check (default: build)")
    listing.add_argument("--direct", action="store_true",
                         help="with --changed-since, leave out crates selected only by their imports")
    listing.add_argument("--require", choices=("program", "theorems"),
                         help="only crates with an extraction program, or with comparator theorems")
    commands.add_parser("paths").add_argument("kind", choices=sorted(CHECKS))
    commands.add_parser("tests").add_argument("--changed-since", metavar="REF",
                                              help="only suites affected since REF")
    commands.add_parser("check")
    commands.add_parser("scope").add_argument("--changed-since", metavar="REF", required=True)
    args = parser.parse_args()
    if args.command in ("check", "scope"):
        errors = check(ROOT) if args.command == "check" else scope(ROOT, args.changed_since)
        for message in errors:
            print(f"error: {message}" if not message.startswith("  ") else message, file=sys.stderr)
        if errors:
            sys.exit(1)
        print(f"{len(crates(ROOT))} crate(s) follow the repository conventions" if args.command == "check"
              else "Specification and proof changes are in separate pull requests")
        return
    if args.command == "paths":
        print("\n".join(workflow_paths(args.kind)))
        return
    if args.command == "tests":
        print("\n".join(test_suites(ROOT, args.changed_since)))
        return
    # Workflows interpolate crate names into runner labels and paths; `check` reports the others.
    names = [name for name in crates(ROOT) if CRATE_NAME.fullmatch(name)]
    if args.require:
        names = [entry["crate"] for entry in matrix(ROOT, names) if entry[args.require]]
    if args.changed_since:
        names = changed_crates(ROOT, args.changed_since, args.kind, names, direct=args.direct)
    if args.json:
        print(json.dumps(matrix(ROOT, names)))
    else:
        print("\n".join(names))


if __name__ == "__main__":
    main()
