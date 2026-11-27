#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lean --version
lake build
audit="$(lake env lean Audit.lean)"
printf '%s\n' "$audit"
if grep -q 'sorryAx' <<<"$audit"; then
  echo "Audit failed: a selected theorem depends on sorryAx." >&2
  exit 1
fi
