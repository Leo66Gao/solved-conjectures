from collections import Counter
from fractions import Fraction
from itertools import product

# Octacode with generator [I | A]. The Gray encoding pairs in low-bit-first
# order are 00, 10, 11, 01 for residues 0, 1, 2, 3.
A = ((2,3,3,3),(1,2,3,1),(1,1,2,3),(1,3,1,2))
short = 0
punct = 1
keep = tuple(i for i in range(16) if i not in (short,punct))
words=set()
for p,q,r,s in product(range(4),repeat=4):
    z = (p,q,r,s,2*p+q+r+s,3*p+2*q+r+3*s,3*p+3*q+2*r+s,3*p+q+3*r+2*s)
    bits = tuple(t for a in z for t in (((a&1)^((a>>1)&1)), (a>>1)&1))
    if not bits[short]:
        words.add(sum(bits[j]*2**i for i,j in enumerate(keep)))
C = sorted(words)
assert len(C) == 128 and len(keep) == 14
hist=Counter()
N=1<<len(keep)
cells={c:[] for c in C}
for x in range(N):
    _, error, c=min(((x^c).bit_count(),x^c,c) for c in C)
    cells[c].append(x)
    hist[error.bit_count()]+=1
B=Fraction(0)
for xs in cells.values():
    s=[sum(1 if not x&(1<<j) else -1 for x in xs) for j in range(len(keep))]
    B+=Fraction(sum(u*u for u in s), N*len(xs))
print(f'C={len(C)}, n={len(keep)}, minimum distance={min((x^y).bit_count() for x in C for y in C if x!=y)}')
print(f'cell sizes={Counter(map(len,cells.values()))}; error histogram={dict(sorted(hist.items()))}')
print(f'B={B}; B-7={B-7}')
