#!/usr/bin/env bash
# Run from the repository root after GitHub Actions has installed Lean/Go and loaded SSH.
# Shared by every crate: the trusted dependency is built once per job, before project sources.
# PROJECT is the Lake project of the crate checked: the repository root (the default), or a
# standalone crate's directory, whose own manifest pins the dependencies.

set -euo pipefail
: "${RUNNER_TEMP:?}" "${GITHUB_ENV:?}" "${GITHUB_PATH:?}"
PROJECT=${PROJECT:-.}

# Pinned Landrun and comparator releases, matching Lean 4.34.0
LANDRUN_VERSION=v0.1.16
COMPARATOR_VERSION=v4.34.0

# Limit the deploy key's lifetime to fetching/building the dependencies: lean-x86, which the
# statement trusts, and lean-x86-proofs' library, which only proofs import
(
  trap 'ssh-add -D >/dev/null 2>&1 || true' EXIT
  cd "$PROJECT"
  LAKE_CACHE_DIR="$PWD/.lake/cache" lake build @x86 x86proofs/X86Proofs
)

# Keep the dependency outside the sandbox's writable .lake directory
mv "$PROJECT/.lake/packages" "$RUNNER_TEMP/dependencies"
ln -s "$RUNNER_TEMP/dependencies" "$PROJECT/.lake/packages"

# Install Landrun
GOBIN="$RUNNER_TEMP/bin" go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_VERSION"
mv "$RUNNER_TEMP/bin/landrun" "$RUNNER_TEMP/bin/landrun-real"
install -m 755 ci/landrun.sh "$RUNNER_TEMP/bin/landrun"

# Install Comparator if needed
if [[ "${INSTALL_COMPARATOR:-false}" == true ]]; then
  git clone https://github.com/leanprover/comparator.git "$RUNNER_TEMP/comparator"
  git -C "$RUNNER_TEMP/comparator" checkout "$COMPARATOR_VERSION"
  cmp "$PROJECT/lean-toolchain" "$RUNNER_TEMP/comparator/lean-toolchain"
  (cd "$RUNNER_TEMP/comparator" && lake build lean4export comparator)
fi

# Landrun needs actual Lean binaries, and upstream comparator requires AF_UNIX blocking
sudo loginctl enable-linger "$(id -un)"
sudo systemctl start "user@$(id -u).service"
echo "XDG_RUNTIME_DIR=/run/user/$(id -u)" >> "$GITHUB_ENV"
echo "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus" >> "$GITHUB_ENV"
echo "$(cd "$PROJECT" && lean --print-prefix)/bin" >> "$GITHUB_PATH"
