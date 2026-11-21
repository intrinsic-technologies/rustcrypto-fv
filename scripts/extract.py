#!/usr/bin/env python3

"""Extraction

Compiles a crate's Rust wrapper in `<Crate>/program/` for bare-metal x86-64, links a fixed image,
and generates the checked-in Lean definitions and binary data with the pinned lean-x86 extractor,
`x86-extract`.

Usage, from anywhere: scripts/extract.py <Crate>

The crate's `program/` directory provides:

* `Cargo.toml`, `Cargo.lock`: a `staticlib` package depending on the pinned RustCrypto crate;
* `rust-toolchain.toml`: the pinned compiler, with the `x86_64-unknown-none` target;
* `.cargo/config.toml`: the target and code generation flags;
* `extraction.toml`: the `x86-extract` configuration, without `elf` and `output`, which this
  script supplies. Its `namespace` selects the output directory, such as
  `Sha2.Spec.Program.Extracted` for `Sha2/Spec/Program/Extracted/`;
* `layout.ld` (optional): a linker script replacing `scripts/layout.ld`.

Intermediate outputs, including Cargo's target directory, stay in `.cache/extract/<Crate>/`.
Requires Rust/rustup, Python 3, binutils, Make, and a C compiler alongside Lean and Git.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
EXTRACTOR_TARGET = ROOT / ".cache/x86-extract"


def run(command, cwd=ROOT, env=None, capture=False):
    print("+", " ".join(str(part) for part in command), flush=True)
    result = subprocess.run(command, cwd=cwd, env=env, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None)
    return result.stdout


def build_extractor():
    """Builds the XED decoder and `x86-extract` from the pinned lean-x86 checkout."""
    run(["lake", "env", "true"])
    x86 = ROOT / ".lake/packages/x86"
    run(["git", "-C", x86, "submodule", "update", "--init", "vendor/xed", "vendor/mbuild"])
    run(["make", "-C", x86 / "extraction"])
    env = {key: value for key, value in os.environ.items() if key not in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS")}
    run(["cargo", "build", "--locked", "--release", "--manifest-path", x86 / "extraction/Cargo.toml",
         "--target-dir", EXTRACTOR_TARGET], env=env)
    return EXTRACTOR_TARGET / "release/x86-extract", x86 / "extraction/.cache/decode-instructions"


def toml_value(value):
    """Formats the TOML values that `x86-extract` configurations use."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ", ".join(toml_value(item) for item in value) + "]"
    raise ValueError(f"Unsupported extraction setting: {value!r}")


def write_config(settings, path):
    tables = {key: value for key, value in settings.items() if isinstance(value, dict)}
    lines = [f"{key} = {toml_value(value)}" for key, value in settings.items() if key not in tables]
    for name, table in tables.items():
        lines += ["", f"[{name}]", *(f"{json.dumps(key)} = {toml_value(value)}" for key, value in table.items())]
    path.write_text("\n".join(lines) + "\n")


def section_stem(section):
    """The `.bin` file stem `x86-extract` uses for a section, such as `data_rel_ro`."""
    stem = "".join(c.lower() if c.isascii() and c.isalnum() else "_" for c in section.lstrip("."))
    return stem if stem[:1].isalpha() else "section_" + stem


def build_program(program, cache, entries):
    """Builds the wrapper's static library and links the ELF that the extractor reads."""
    cargo_config = program / ".cargo/config.toml"
    if cargo_config.is_file() and any("rustflags" in table for table in
                                      tomllib.loads(cargo_config.read_text()).get("target", {}).values()):
        raise RuntimeError(f"{cargo_config.relative_to(ROOT)}: set flags in [build] rustflags, not [target.*]")
    cargo_home = ROOT / ".cache/cargo"
    env = {key: value for key, value in os.environ.items() if key not in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS")}
    env["CARGO_HOME"] = str(cargo_home)
    # Panic locations embed source paths in read-only data; remap them so that extraction does
    # not depend on the checkout or Cargo home location. Cargo appends these to the crate's flags.
    # With the `rust-src` component installed, rustc resolves standard library paths to the local
    # sysroot instead of `/rustc/<commit>`; map them back so the component makes no difference.
    target = cache / "target"
    sysroot = run(["rustc", "--print", "sysroot"], cwd=program, env=env, capture=True).strip()
    commit = next(line.split(": ", 1)[1] for line in
                  run(["rustc", "-vV"], cwd=program, env=env, capture=True).splitlines()
                  if line.startswith("commit-hash: "))
    remap = [f"--remap-path-prefix={cargo_home}=/cargo", f"--remap-path-prefix={target}=/target",
             f"--remap-path-prefix={program}=/program",
             f"--remap-path-prefix={sysroot}/lib/rustlib/src/rust=/rustc/{commit}"]
    messages = run(["cargo", "build", "--locked", "--release", "--message-format=json-render-diagnostics",
                    "--target-dir", str(target),
                    "--config", f"build.rustflags = {json.dumps(remap)}"], cwd=program, env=env, capture=True)
    libraries = [path for line in messages.splitlines() if line.startswith("{")
                 for message in [json.loads(line)] if message.get("reason") == "compiler-artifact"
                 and "staticlib" in message["target"]["crate_types"]
                 for path in message["filenames"] if path.endswith(".a")]
    if len(libraries) != 1:
        raise RuntimeError(f"Expected one static library from {program}, found {libraries}")
    layout = program / "layout.ld"
    if not layout.is_file():
        layout = SCRIPTS / "layout.ld"
    elf = cache / "program.elf"
    symbols = [argument for symbol in entries for argument in ("--undefined", symbol)]
    run(["ld", "--gc-sections", "--no-undefined", "--fatal-warnings", "-T", layout,
         "--entry", entries[0], *symbols, libraries[0], "-o", elf])
    return elf


def extract(crate):
    program = ROOT / crate / "program"
    settings = tomllib.loads((program / "extraction.toml").read_text())
    for key in ("elf", "output"):
        if key in settings:
            raise RuntimeError(f"{crate}/program/extraction.toml must not set `{key}`; scripts/extract.py supplies it")
    namespace = settings["namespace"]
    if namespace.split(".")[:2] != [crate, "Spec"] or namespace.split(".")[-1] != "Extracted":
        raise RuntimeError(f"Extraction namespace must be {crate}.Spec.<Name>.Extracted, not {namespace}")
    entries = list(settings.get("entries", {}).values())
    if not entries:
        raise RuntimeError(f"{crate}/program/extraction.toml has no [entries]")

    cache = ROOT / ".cache/extract" / crate
    shutil.rmtree(cache / "generated", ignore_errors=True)
    cache.mkdir(parents=True, exist_ok=True)
    elf = build_program(program, cache, entries)
    extractor, decoder = build_extractor()

    relative = Path(*namespace.split("."))
    generated = cache / "generated" / relative
    config = cache / "extraction.toml"
    write_config({"elf": str(elf), "output": str(generated), **settings}, config)
    run([extractor, "--decoder", decoder, config])

    # Compare extracted bytes with the ELF sections before installing generated files.
    for section in [*settings["code_sections"], *settings.get("data_sections", [])]:
        name = section_stem(section) + ".bin"
        if (generated / name).is_file():
            dump = cache / f"objcopy-{name}"
            run(["objcopy", "--dump-section", f"{section}={dump}", elf, "/dev/null"])
            if dump.read_bytes() != (generated / name).read_bytes():
                raise RuntimeError(f"Extracted {name} differs from the ELF's {section} section")
            print(f"Checked {name} against the ELF's {section} section", flush=True)

    destination = ROOT / relative
    shutil.rmtree(destination, ignore_errors=True)
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(generated, destination)
    print(f"Installed {destination.relative_to(ROOT)}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("crate", help="crate directory, such as Sha2")
    args = parser.parse_args()
    if not (ROOT / args.crate / "program/extraction.toml").is_file():
        parser.error(f"{args.crate}/program/extraction.toml not found")
    try:
        extract(args.crate)
    except (OSError, RuntimeError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"extract: {error}")


if __name__ == "__main__":
    main()
