#!/usr/bin/env python3

"""Reject proof-library dependencies in every specification and statement module.

A module's setup records resolved artifacts for its complete transitive import closure,
including imports through other packages. Build the targets before inspecting this metadata
so the check cannot use stale import information. Lake writes a module's .setup.json only
when it compiles the module, not when it restores it from the artifact cache, so `check`
asks Lake for each setup instead; Comparator, which compiles every module, reads the files.
"""

import json
import os
from pathlib import Path
import subprocess
import sys


def project_directory(root, crate):
    """The Lake project that builds a crate: the crate's own directory if it holds a lakefile.lean
    (a standalone crate, which pins its own dependencies and reads its sources from the repository
    root), otherwise the repository root."""
    return root / crate if (root / crate / "lakefile.lean").is_file() else root


def specification_modules(root, crates=None):
    sources = []
    if crates is None:
        crates = sorted(path.parent.name for path in root.glob("*/comparator.config.json"))
    for crate in crates:
        for name in ("Spec", "Statements"):
            entry = root / crate / f"{name}.lean"
            if entry.is_file():
                sources.append(entry)
            sources += sorted((root / crate / name).rglob("*.lean"))
    return sorted({".".join(path.relative_to(root).with_suffix("").parts) for path in sources})


def proof_library_directory(root):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["name"] == "x86proofs":
            if package["type"] == "path":
                return (root / package["dir"]).resolve()
            return (root / manifest["packagesDir"] / package["name"]).resolve()
    return None


def compiled_setup(root, module):
    """The setup Lake wrote when it compiled `module`."""
    return json.loads((root / ".lake/build/ir" / (module.replace(".", "/") + ".setup.json")).read_text())


def resolved_setup(root, module, sources=None):
    """The setup Lake resolves for `module`, whether it was compiled or restored from the cache.
    `root` is the Lake project, and `sources` the directory holding module sources when it differs
    (a standalone crate's project reads them from the repository root)."""
    path = Path(os.path.relpath((sources or root) / Path(*module.split(".")).with_suffix(".lean"), root))
    return json.loads(subprocess.run(["lake", "setup-file", str(path)], cwd=root, check=True,
                                     capture_output=True, text=True).stdout)


def audit(root, modules, setup_of=compiled_setup):
    proof_library = proof_library_directory(root)
    failures = []

    def belongs_to_proof_library(path):
        return proof_library is not None and (root / path).resolve().is_relative_to(proof_library)

    for module in modules:
        setup = setup_of(root, module)
        if setup.get("name") != module or not isinstance(setup.get("importArts"), dict):
            raise ValueError(f"Missing or invalid import metadata for {module}")
        for imported, groups in setup["importArts"].items():
            namespace = imported.split(".")[0]
            if namespace in ("X86Proofs", "X86ProofsExamples") or any(
                belongs_to_proof_library(artifact) for group in groups for artifact in group
            ):
                failures.append(f"{module} -> {imported}")
        for plugin in setup.get("plugins", []):
            if belongs_to_proof_library(plugin["path"]):
                failures.append(f"{module} -> plugin {plugin['path']}")
        for library in setup.get("dynlibs", []):
            if belongs_to_proof_library(library):
                failures.append(f"{module} -> dynamic library {library}")
    if failures:
        details = "\n".join(f"  {failure}" for failure in failures[:20])
        if len(failures) > 20:
            details += f"\n  ... and {len(failures) - 20} more"
        raise ValueError(f"Specification/statement depends on lean-x86-proofs:\n{details}")


def check(root, crates=None):
    root = root.resolve()
    if crates is None:
        crates = sorted(path.parent.name for path in root.glob("*/comparator.config.json"))
    projects = {}
    for crate in crates:
        projects.setdefault(project_directory(root, crate), []).append(crate)
    count = 0
    for project, members in sorted(projects.items()):
        modules = specification_modules(root, members)
        if modules:
            subprocess.run(["lake", "build", *modules], cwd=project, check=True)
        audit(project, modules, lambda directory, module: resolved_setup(directory, module, root))
        count += len(modules)
    print(f"Checked {count} specification/statement modules: no lean-x86-proofs dependencies.")


if __name__ == "__main__":
    try:
        check(Path(__file__).resolve().parent.parent, sys.argv[1:] or None)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        sys.exit(f"spec dependencies: {error}")
