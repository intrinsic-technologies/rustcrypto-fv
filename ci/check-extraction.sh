#!/usr/bin/env bash
# Regenerates a crate's extraction directories, checks their complete contents (including
# binary data) against the checked-in files, and restores the originals on exit.
# Usage: bash ci/check-extraction.sh <Crate>

set -euo pipefail
cd "$(dirname "$0")/.."
crate=${1:?usage: ci/check-extraction.sh <Crate>}

# Every `Extracted` directory of the crate, before and after regeneration
extracted() { find "$crate" -type d -name Extracted -not -path '*/.lake/*' | sort; }

mapfile -t outputs < <(extracted)
reference=$(mktemp -d)

restore() {
  for output in "${outputs[@]}"; do
    rm -rf -- "$output"
    if [[ -d "$reference/$output" ]]; then
      mkdir -p "$(dirname "$output")"
      mv "$reference/$output" "$output"
    fi
  done
  rm -rf -- "$reference"
}
trap restore EXIT

for output in "${outputs[@]}"; do
  mkdir -p "$reference/$(dirname "$output")"
  mv "$output" "$reference/$output"
done

python3 scripts/extract.py "$crate"

# Include directories that only the regenerated extraction contains
mapfile -t outputs < <({ printf '%s\n' "${outputs[@]}"; extracted; } | sed '/^$/d' | sort -u)
status=0
for output in "${outputs[@]}"; do
  if [[ ! -d "$reference/$output" ]]; then
    echo "Unexpected extraction output: $output" >&2
    status=1
  elif [[ ! -d "$output" ]]; then
    echo "Extraction no longer generates: $output" >&2
    status=1
  else
    diff -ru -- "$reference/$output" "$output" || status=1
  fi
done
if [[ $status -eq 0 ]]; then
  echo "Extracted files for $crate match the generator"
fi
exit "$status"
