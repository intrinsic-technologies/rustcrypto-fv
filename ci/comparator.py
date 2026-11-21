#!/usr/bin/env python3

"""Comparator CI

Four commands, each for one crate directory; the first three support the two comparator CI jobs:

stage:  Copies the crate's statement, the specification modules it imports, their binary
        data, and the configuration into a temporary workspace without proof sources or Git
        history.
build:  Compiles the staged statement in a new sandboxed process to produce independent
        reference artifacts, and checks that its compiled imports do not reach the proof
        library (lean-x86-proofs).
verify: Rebuilds the statement in a new sandboxed process, compares its artifacts with the
        reference, and repeats the import check. Then it runs the comparator to build the proof
        and check that it proves the same statements, uses only permitted axioms, and passes
        kernel verification.
inputs: Prints the files `stage` copies, relative to the repository root. Run it from the root
        to check them locally.

Shared setup supplies pinned tools and read-only dependencies under RUNNER_TEMP.

A standalone crate (one whose directory holds a lakefile.lean) is its own Lake project: its
package files, `.lake` directory, and dependencies are in the crate directory, every Lake command
runs there, and its sources stay at their paths from the repository root.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

from check_spec_dependencies import audit, project_directory, specification_modules

# Files every staged workspace needs to load the Lake package, relative to its project directory
PACKAGE_FILES = ("lean-toolchain", "lakefile.lean", "lake-manifest.json")

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+?)\s*(?:--.*)?$")

# Root modules of lean-x86-proofs' libraries, which proofs may import but the trusted claim may not
PROOF_LIBRARIES = ("X86Proofs", "X86ProofsExamples")
# Lean script checking the same rule on compiled import graphs (it keeps its own copy of the list)
CLAIM_IMPORTS = Path(__file__).resolve().parent / "ClaimImports.lean"
SPEC_DEPENDENCIES = Path(__file__).resolve().parent / "check_spec_dependencies.py"


def module_path(module):
    """Returns the source path of a module relative to the package root."""
    return Path(*module.split(".")).with_suffix(".lean")


def imports(source):
    """Returns the modules imported by a Lean source file."""
    modules = []
    for line in source.read_text().splitlines():
        match = IMPORT.match(line)
        if match:
            modules += match.group(1).split()
    return modules


def local_closure(checkout, module):
    """Returns the modules in the checkout reachable from `module` by imports, in a fixed order.

    Modules without a source file in the checkout come from dependencies or the toolchain.
    """
    seen, pending = [], [module]
    while pending:
        current = pending.pop()
        if current in seen or not (checkout / module_path(current)).is_file():
            continue
        seen.append(current)
        pending += imports(checkout / module_path(current))
    return sorted(seen)


def proof_library_imports(checkout, modules):
    """Returns `module imports library-module` for each import of a proof library by `modules`."""
    return [f"{module} imports {imported}" for module in modules
            for imported in imports(checkout / module_path(module))
            if imported.split(".")[0] in PROOF_LIBRARIES]


def is_trusted_module(module, crate):
    """Shared standards, specification modules, and this crate's statements are trusted inputs."""
    parts = module.split(".")
    statement = parts[:2] == [crate, "Statements"]
    return "Proofs" not in parts and "Tests" not in parts and (
        statement or "Spec" in parts or parts[0] == "Standards")


def load_config(workspace, crate):
    return json.loads((workspace / crate / "comparator.config.json").read_text())


def run(command, cwd):
    """Runs a command in the given directory, raising an error if it fails."""
    subprocess.run(command, cwd=cwd, check=True)


def restricted(command, cwd):
    """Blocks Unix sockets in addition to the child command's Landrun restrictions."""
    run([
        "systemd-run", "--user", "--wait", "--pipe", "--collect",
        "--property=RestrictAddressFamilies=~AF_UNIX", f"--working-directory={cwd}",
        f"--setenv=PATH={os.environ['PATH']}", f"--setenv=HOME={os.environ['HOME']}",
        "--", *command,
    ], cwd)


def build_statement(workspace, temporary, crate):
    """Builds the configured challenge module under Landrun, with only .lake writable."""
    project = project_directory(workspace, crate)
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=project, text=True).strip()
    git = shutil.which("git")
    if git is None:
        raise RuntimeError("git executable not found")
    restricted([
        str(temporary / "bin/landrun"), "--best-effort", "--ro", "/", "--rw", "/dev",
        "-ldd", "-add-exec", "--env", "PATH", "--env", "HOME",
        "--rwx", str(project / ".lake"), "--rox", prefix, "--rox", git,
        "--", "lake", "build", *specification_modules(workspace, [crate]),
    ], project)


def spec_inputs(checkout, crate):
    """Returns the files needed to build the crate's statement, relative to the checkout.

    These are the statement's local import closure, the data files beside each of those modules
    (such as extracted `.bin` files read by `include_bytes`), and the crate's whole `Spec/` tree,
    which Lake tracks as an input directory. Fails if a proof or test module is reachable.
    """
    config = load_config(checkout, crate)
    modules = sorted({module for root in specification_modules(checkout, [crate])
                      for module in local_closure(checkout, root)})
    if config["challenge_module"] not in modules:
        raise RuntimeError(f"Missing challenge module source: {config['challenge_module']}")
    untrusted = [module for module in modules if not is_trusted_module(module, crate)]
    if untrusted:
        raise RuntimeError(f"Statement imports non-specification modules: {', '.join(untrusted)}")
    library = proof_library_imports(checkout, modules)
    if library:
        raise RuntimeError(f"Statement reaches the proof library: {', '.join(library)}")
    files = set()
    for module in modules:
        source = checkout / module_path(module)
        files |= {path for path in source.parent.iterdir() if path.is_file() and path.suffix != ".lean"}
        files.add(source)
    spec = checkout / crate / "Spec"
    if spec.is_dir():
        files |= {path for path in spec.rglob("*") if path.is_file()}
    files |= {project_directory(checkout, crate) / name for name in PACKAGE_FILES}
    files.add(checkout / crate / "comparator.config.json")
    return sorted(path.relative_to(checkout) for path in files)


def stage(checkout, temporary, crate):
    """Prepares a temporary spec-only workspace and copies this script for the build step.

    Copies the statement, specification, binary data, and configuration, and creates a symlink to
    the external dependency directory. These inputs remain available when the original checkout
    is deleted.
    """
    staging = temporary / "challenge"
    staging.mkdir()
    workspace = staging / "workspace"
    for relative in spec_inputs(checkout, crate):
        source = checkout / relative
        if source.resolve() != source:
            raise RuntimeError(f"Spec-only input must not be a symlink: {source}")
        destination = workspace / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        print(f"  {relative}", flush=True)
    project = project_directory(workspace, crate)
    (project / ".lake").mkdir()
    # Reuse the artifact cache of the dependency-only setup build; otherwise Lake tries to write
    # hash files beside the read-only dependency artifacts
    cache = project_directory(checkout, crate) / ".lake/cache"
    if cache.is_dir():
        shutil.copytree(cache, project / ".lake/cache")
    (project / ".lake/packages").symlink_to(temporary / "dependencies", target_is_directory=True)
    shutil.copyfile(__file__, staging / "comparator.py")
    shutil.copyfile(CLAIM_IMPORTS, staging / CLAIM_IMPORTS.name)
    shutil.copyfile(SPEC_DEPENDENCIES, staging / SPEC_DEPENDENCIES.name)
    print(f"Staged spec-only inputs for {crate} at {workspace}", flush=True)


def check_claim_imports(workspace, checker, crate):
    """Fails if the built statement reaches the proof library, by its compiled import graph."""
    project = project_directory(workspace, crate)
    modules = specification_modules(workspace, [crate])
    audit(project, modules)
    run(["lake", "env", "lean", "--run", str(checker), *modules], project)


def build(checkout, temporary, crate):
    """Compiles the staged statement in a new sandboxed process to produce reference artifacts."""
    if checkout.exists():
        raise RuntimeError("Delete the original checkout before building the isolated statement")
    workspace = temporary / "challenge/workspace"
    build_statement(workspace, temporary, crate)
    # This copy of the script runs from the staging directory, beside its copy of the checker
    check_claim_imports(workspace, CLAIM_IMPORTS, crate)


def compare_artifacts(build_dir, reference):
    """Checks each compiled artifact against the reference, ignoring path metadata; symlinks and
    artifacts whose references are missing or differ in content are rejected.
    """
    for path in sorted(build_dir.rglob("*")):
        relative = path.relative_to(build_dir)
        if path.is_symlink():
            raise RuntimeError(f"Unexpected artifact symlink: {relative}")
        if not path.is_file() or path.name.endswith((".trace", ".setup.json")):
            continue
        expected = reference / relative
        if expected.is_symlink() or not expected.is_file() or path.read_bytes() != expected.read_bytes():
            raise RuntimeError(f"Artifact differs from spec-only reference: {relative}")


def verify(checkout, temporary, crate):
    """Rebuilds the statement, compares reference artifacts, and checks the proof.

    Creates a sandboxed process to compile the statement, then compares its artifacts with the
    independent reference. Runs the comparator to build the proof and checks that it proves the
    same statements, uses only permitted axioms, and passes kernel verification.
    """
    project = project_directory(checkout, crate)
    build_dir = project / ".lake/build"
    if build_dir.exists():
        raise RuntimeError("Comparator must start without project build outputs")
    print(f"Building {crate} statement before loading proofs", flush=True)
    build_statement(checkout, temporary, crate)
    config = load_config(checkout, crate)
    statement = build_dir / "lib/lean" / (config["challenge_module"].replace(".", "/") + ".olean")
    if not statement.is_file():
        raise RuntimeError(f"Missing statement artifact: {statement}")
    compare_artifacts(build_dir, temporary / "reference")
    print("Statement and imported spec artifacts match the isolated reference", flush=True)
    check_claim_imports(checkout, CLAIM_IMPORTS, crate)
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True,
    ).strip()
    comparator = temporary / "comparator"
    restricted([
        "env", "-i", f"PATH={os.environ['PATH']}", f"HOME={os.environ['HOME']}",
        f"LEAN_PATH={lean_path}", f"COMPARATOR_LANDRUN={temporary / 'bin/landrun'}",
        f"COMPARATOR_LEAN4EXPORT={comparator / '.lake/packages/lean4export/.lake/build/bin/lean4export'}",
        "stdbuf", "-oL", "-eL", str(comparator / ".lake/build/bin/comparator"),
        os.path.relpath(checkout / crate / "comparator.config.json", project),
    ], project)


def main():
    """Runs the selected CI command using runner paths and reports command failures."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("stage", "build", "verify", "inputs"))
    parser.add_argument("crate", help="crate directory, such as Sha2")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.crate):
        parser.error(f"invalid crate directory: {args.crate}")
    try:
        if args.command == "inputs":
            # Local check of what `stage` copies, runnable outside CI from the repository root
            for path in spec_inputs(Path.cwd().resolve(), args.crate):
                print(path)
            return
        checkout = Path(os.environ["GITHUB_WORKSPACE"]).resolve()
        temporary = Path(os.environ["RUNNER_TEMP"]).resolve()
        {"stage": stage, "build": build, "verify": verify}[args.command](checkout, temporary, args.crate)
    except (OSError, RuntimeError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"comparator: {error}\n")


if __name__ == "__main__":
    main()
