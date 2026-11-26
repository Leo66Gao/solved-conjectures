#!/bin/sh
set -eu
root=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
if [ "$#" -eq 0 ]; then set -- n9 n10; fi
for dim in "$@"; do
  case "$dim" in
    n9|n10) ;;
    *) printf 'Usage: %s [n9|n10]\n' "$0" >&2; exit 2 ;;
  esac
done
for dim in "$@"; do
  echo "=== $dim ==="
  mkdir "$work/$dim"
  cp "$root/$dim"/verify.cpp "$root/$dim"/verify_arithmetic.py "$root/$dim"/points.tsv "$work/$dim/"
  for f in "$root/$dim"/*.bin.gz; do
    name=$(basename "$f" .gz)
    gzip -cd "$f" > "$work/$dim/$name"
  done
  (cd "$work/$dim"; "${CXX:-g++}" -O3 -std=c++17 verify.cpp -lgmpxx -lgmp -o verify; python3 -O verify_arithmetic.py)
done
