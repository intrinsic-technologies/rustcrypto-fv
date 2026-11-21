#!/usr/bin/env bash
# Installed by ci/setup-comparator.sh as `landrun`, in front of the real binary. Keeps Lake's
# artifact-cache writes inside the sandbox's writable .lake directory rather than beside the
# read-only dependency artifacts, and lets Lake run Python: loading lean-x86-proofs' lakefile
# runs its instruction generator `tools/isa2theorem/gen.py`, which only checks its outputs here
# because the setup step already generated them.

set -euo pipefail

export LAKE_CACHE_DIR="$PWD/.lake/cache"
python=$(readlink -f -- "$(command -v python3)")
exec "$(dirname -- "$0")/landrun-real" --env LAKE_CACHE_DIR --rox "$python" "$@"
