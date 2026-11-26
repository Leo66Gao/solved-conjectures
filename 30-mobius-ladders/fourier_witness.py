"""Exact proof that individual nonzero conserved Fourier sectors can be negative."""
from itertools import product
f=(0,2,3,2)
a=[sum((-1)**((x&i).bit_count())*fx for x,fx in enumerate(f)) for i in range(4)]
assert a==[7,-1,-3,-3]
def sector(h):
    return sum(prod(a[x[j]]*a[x[j]^h]*a[x[j]^x[j-1]^h] for j in range(5))
               for x in product(range(4),repeat=5))
from math import prod
n=[sector(h) for h in range(4)]
assert n[1]==-1383937024
assert sum(n)>a[0]**15
assert sum(n) == 4**5*sum(
    prod(f[x[j-1]^y[j]]*f[x[j]^y[j]]*f[x[(j+1)%5]^y[j]] for j in range(5))
    for x in product(range(4),repeat=5)
    for y in product(range(4),repeat=5)
)
print("Unnormalized Walsh coefficients:", a)
print("Integer sector numerators (denominator 4^15):", n)
print("Total numerator:",sum(n),"; constant benchmark numerator:",a[0]**15)
