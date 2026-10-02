#!/usr/bin/env bash
# Build the proof library and both comparison targets, then verify the package.
set -euo pipefail
cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:$PATH"
export LAKE_HOME="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2"

echo "== lake build =="
lake build AGV Challenge Solution

echo "== sorry audit (library must be placeholder-free) =="
if rg -n '\b(sorry|sorryAx|admit)\b' AGV.lean AGV/; then
  echo "FAIL: placeholder found in library"
  exit 1
fi
echo "OK: no placeholders in library"

echo "== Palomar comparator replica =="
./scripts/verify-palomar.sh

echo "== verification passed =="
