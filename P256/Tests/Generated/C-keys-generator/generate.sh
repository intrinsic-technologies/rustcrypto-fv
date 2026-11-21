#!/bin/sh
# Regenerate P256/Tests/Generated/C-keys-cases.txt byte for byte from cases.txt: copy P256/program
# to a scratch directory, add generator.rs as a test module, and run it natively
# (x86_64-unknown-linux-gnu, release, one thread). Needs the toolchain of
# P256/program/rust-toolchain.toml.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
program="$here/../../../program"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -R "$program/." "$work/"
cp "$here/../entry_points.rs" "$work/src/entry_points.rs"
printf '\n#[cfg(test)]\nmod entry_points;\n' >> "$work/src/lib.rs"
cp "$here/generator.rs" "$work/src/c_keys_generator.rs"
printf '\n#[cfg(test)]\nmod c_keys_generator;\n' >> "$work/src/lib.rs"
cd "$work"
C_KEYS_CASES="$here/cases.txt" C_KEYS_VECTORS="$here/../C-keys-cases.txt" \
  CARGO_TARGET_DIR="$work/target" cargo test --locked --release \
  --target x86_64-unknown-linux-gnu --lib c_keys_generator::generate -- --ignored --test-threads=1
