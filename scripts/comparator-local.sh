#!/usr/bin/env bash
# Runs comparator on one crate during development, without CI's sandbox or isolated statement
# build: comparator's fake Landrun executes builds unsandboxed. CI's Comparator workflow is the
# authoritative check. Usage: scripts/comparator-local.sh <Crate>

set -euo pipefail
cd "$(dirname "$0")/.."
crate=${1:?usage: scripts/comparator-local.sh <Crate>}

# Matches ci/setup-comparator.sh
COMPARATOR_VERSION=v4.34.0
comparator=.cache/comparator

if [[ ! -x "$comparator/.lake/build/bin/comparator" ]]; then
  rm -rf -- "$comparator"
  git clone --quiet https://github.com/leanprover/comparator.git "$comparator"
  git -C "$comparator" checkout --quiet "$COMPARATOR_VERSION"
  cmp lean-toolchain "$comparator/lean-toolchain"
  (cd "$comparator" && lake build lean4export comparator)
fi

# A standalone crate (one with its own lakefile.lean) is its own Lake package: run Lake in its directory.
project=. config=$crate/comparator.config.json
if [[ -f "$crate/lakefile.lean" ]]; then project=$crate config=comparator.config.json; fi
comparator=$PWD/$comparator
cd "$project"
lake build "$crate.Statements"
COMPARATOR_LANDRUN="$comparator/scripts/fake-landrun.sh" \
COMPARATOR_LEAN4EXPORT="$comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  lake env "$comparator/.lake/build/bin/comparator" "$config" \
  2> >(grep -v 'WARNING: THIS IS NOT REAL LANDRUN' >&2)
