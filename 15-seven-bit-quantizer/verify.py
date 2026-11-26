"""Exact seven-bit witness. Run: python3 verify.py (Python >= 3.10)."""
from collections import Counter
from fractions import Fraction
from itertools import product

A = ((2,3,3,3), (1,2,3,1), (1,1,2,3), (1,3,1,2))
g = (0,1,3,2)
C = set()
for u in product(range(4), repeat=4):
    v = tuple(sum(u[i]*A[i][j] for i in range(4)) % 4 for j in range(4))
    w = sum(g[a] << (2*j) for j,a in enumerate(u+v))
    if w % 2 == 0:
        C.add(w >> 2)
C = sorted(C)
assert len(C) == 128
assert min((x^y).bit_count() for x in C for y in C if x != y) == 5
m = Counter()
S = {c: [0]*14 for c in C}
radii = Counter()
for x in range(1 << 14):
    c = min(C, key=lambda z: ((x^z).bit_count(), x^z))
    m[c] += 1
    radii[(x^c).bit_count()] += 1
    for i in range(14):
        S[c][i] += 1 - 2*((x >> i) & 1)
counts = Counter((m[c], sum(v*v for v in S[c])) for c in C)
assert counts == {(128,114980):64, (128,114996):64}
B = sum(Fraction(sum(v*v for v in S[c]), m[c]) for c in C) / (1 << 14)
assert B == Fraction(28747,4096)
rho = Fraction(1,10)
margin = B - 7*(1 + rho*rho/(6*(1-rho*rho)))
assert margin > 0
print('size, minimum distance:', len(C), 5)
print('distance histogram:', sorted(radii.items()))
print('cell certificate (size, squared sign-sum):', sorted(counts.items()))
print('B:', B, '; B - 7:', B-7)
print('lower-bound margin in units rho^2 / (2 ln 2):', margin)
