#!/bin/sh
# Regenerate P256/Tests/Generated/D-ecdsa-native.txt byte for byte from cases.txt: copy
# P256/program to a scratch directory, add generator.rs as a test module, and run it natively
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
cp "$here/generator.rs" "$work/src/d_ecdsa_native_generator.rs"
printf '\n#[cfg(test)]\nmod d_ecdsa_native_generator;\n' >> "$work/src/lib.rs"
cd "$work"
D_ECDSA_CASES="$here/cases.txt" D_ECDSA_VECTORS="$here/../D-ecdsa-native.txt" \
  CARGO_TARGET_DIR="$work/target" cargo test --locked --release \
  --target x86_64-unknown-linux-gnu --lib d_ecdsa_native_generator::generate -- --ignored \
  --test-threads=1
