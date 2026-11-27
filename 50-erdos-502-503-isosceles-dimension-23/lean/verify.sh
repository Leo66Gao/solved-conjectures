#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
pin=5ed2965256430c3649e86755f9576b54eca72435
mathlib=${MATHLIB_ROOT:-"$src/.deps/mathlib4"}
if [[ ! -d "$mathlib/.git" ]]; then
  mkdir -p -- "$(dirname -- "$mathlib")"
  git init --quiet "$mathlib"
  git -C "$mathlib" fetch --quiet --depth 1 https://github.com/leanprover-community/mathlib4.git "$pin"
  git -C "$mathlib" checkout --quiet --detach FETCH_HEAD
fi
mathlib=$(cd -- "$mathlib" && pwd)
if [[ $(git -C "$mathlib" rev-parse HEAD) != "$pin" ]]; then
  echo 'Unexpected Mathlib revision. Use the pinned checkout.' >&2; exit 1
fi
envroot=${LEAN_LAKE_ROOT:-"$mathlib"}
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
cd -- "$envroot"
version=$(lean --version)
printf '%s\n' "$version"
[[ "$version" == *'version 4.34.0'* ]]
if [[ ${SKIP_CACHE_DOWNLOAD:-0} != 1 ]]; then
  (cd -- "$mathlib" && lake exe cache get)
fi
raw=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$tmp:$raw"
for name in ModFour BinarySaturation Rank23 QuadraticFeatures Axis GolayCore; do
  printf '\nBUILD %s\n' "$name"
  lean -R "$src" -o "$tmp/$name.olean" "$src/$name.lean"
  leanchecker -v "$name"
  printf 'KERNEL REPLAY %s: PASS\n' "$name"
done
