#!/usr/bin/env bash
# Reproduce the Lean checks with a pinned third-party dependency, not a vendored copy.
set -euo pipefail
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
pin=29e64ce67b4999f76657bb4b51e306076f59e689
mathlib_pin=5ed2965256430c3649e86755f9576b54eca72435
deps=${ERDOS335_ROOT:-"$src/.deps/erdos-335"}
if [[ ! -d "$deps/.git" ]]; then
  mkdir -p -- "$(dirname -- "$deps")"
  git clone --quiet --no-checkout https://github.com/Ghuffy1/erdos-335.git "$deps"
  git -C "$deps" checkout --quiet --detach "$pin"
fi
deps=$(cd -- "$deps" && pwd)
if [[ "$(git -C "$deps" rev-parse HEAD)" != "$pin" ]]; then
  printf 'Expected Erdős #335 commit %s. Use a clean clone or set ERDOS335_ROOT.\n' "$pin" >&2
  exit 1
fi
cache=$(mktemp -d)
trap 'rm -rf -- "$cache"' EXIT
mkdir -p -- "$cache/Erdos338"
cd -- "$deps"
lean --version
[[ "$(lean --version)" == *'version 4.34.0'* ]] || { echo 'Select Lean 4.34.0.' >&2; exit 1; }
if [[ ${ERDOS338_SKIP_DOWNLOAD:-0} != 1 ]]; then
  lake exe cache get
fi
lake build Erdos335.DysonProgressions Erdos335.DysonCounting Erdos335.WindowEstimates Erdos335.FiniteKneser
[[ "$(git -C .lake/packages/mathlib rev-parse HEAD)" == "$mathlib_pin" ]] || {
  echo 'Unexpected Mathlib commit.' >&2
  exit 1
}
raw=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$cache:$raw"
files=(Erdos338/Growth Erdos338/Pair Erdos338/Fringe Erdos338/Blockers Erdos338/Equality
  UniformLocal RobustLayers PopularityCounting CollisionBridge CatalogueAdapter
  HHPFinite DensityBridge CatalogueResult CoinBox DilationCount MixedDyson MixedWindow
  MixedStable Compression FiniteRay ListMixedBridge Erdos338Solution
  BoundedCatalogue BoundedGlue UniformPopularity RecurrentLayers ModulusShrink Full338
  ReflectedBridge Erdos338/Density Erdos338/QAdic Erdos338)
for module in "${files[@]}"; do
  printf '\nCHECK %s\n' "$module"
  lean -R "$src" -o "$cache/$module.olean" "$src/$module.lean"
done
# Independently import the final compiled objects and inspect their axioms.
audit=$(lean -R "$src" "$src/Audit.lean")
printf '\n%s\n' "$audit"
python3 - "$audit" <<'PYTHON'
import re
import sys
names = {
    "Erdos338.erdos_338",
    "Erdos338.erdos_338.variants.basis_after_finite_removal",
    "Erdos338.erdos_338.variants.same_order_after_finite_removal",
    "Erdos338.erdos_338.variants.eq_order",
    "Erdos338.erdos_338.variants.bounded_by_order",
}
standard = {"propext", "Classical.choice", "Quot.sound"}
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", sys.argv[1])
assert names <= {name for name, _ in entries}, "Missing main declaration audit"
assert len(entries) == 26, "Missing or unexpected supplemental audits"
for name, axioms in entries:
    cited = set(re.split(r"\s*,\s*", axioms.strip()))
    assert cited <= standard, (name, cited - standard)
print("PASS: five main declarations, the reflected bridge, and 20 supplemental audits use only standard Lean axioms.")
PYTHON
