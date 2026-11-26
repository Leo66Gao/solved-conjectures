"""Exact weighted Green P12 certificates for all abelian groups of order at most 4."""
from collections import defaultdict,Counter
from itertools import product,permutations
from math import factorial
from three_state import times,T,Z
from math import prod
F=factorial(15)
def count(table,order):
 n=len(table); D=6
 weight=[[int(table[i][j] in order[:k])*D*n//k for k in range(1,n+1)]
         for i in range(n) for j in range(n)]
 A=[[{T(a):v for a,v in enumerate(weight[i*n+j]) if v} for j in range(n)] for i in range(n)]
 b={}
 for I in product(range(n),repeat=3):
   key=tuple(sorted(I))
   if key in b:continue
   K=defaultdict(int)
   for l in range(n):
     h=times(times(A[I[0]][l],A[I[1]][l]),A[I[2]][l])
     for m,c in h.items():K[m]+=c
   b[key]=dict(K)
 t=Counter()
 for L in product(range(n),repeat=4):
   I=(0,)+L
   powers=[tuple(sorted([I[i-1],I[i],I[(i+1)%5]])) for i in range(5)]
   f={Z:1}
   for X in powers:f=times(f,b[X])
   for m,c in f.items():t[m]+=n*c
 for a in range(16):
  for b in range(16-a):
   for c in range(16-a-b):
    d=15-a-b-c;m=(a,b,c,d)
    if any(m[n:]):continue
    t[m]-=D**15*n**10*F//prod(factorial(e) for e in m)
 return t
if __name__=='__main__':
 for n,kind in [(2,'cyclic'),(3,'cyclic'),(4,'cyclic'),(4,'binary')]:
  table=[[(i+j)%n if kind=='cyclic' else i^j for j in range(n)] for i in range(n)]
  affs=[p for p in permutations(range(n)) if all(
    p[table[i][j]]==table[p[i]][table[p[j]][next(a for a in range(n) if table[p[0]][a]==0)]]
    for i in range(n) for j in range(n))]
  todo=set(permutations(range(n)))
  while todo:
   order=min(todo);todo-={tuple(p[i] for i in order) for p in affs}
   t=count(table,order)
   counts=Counter((v>0)-(v<0) for v in t.values())
   print(kind,n,order,counts, flush=True)
   print('negative first',next(((m,c) for m,c in t.items() if c<0),None),flush=True)
   assert all(v>=0 for v in t.values())
   for i in range(n-1):assert t[tuple(15*a for a in T(i))]>0
