"""Exact coefficient certificate for four-point magnitude; requires NumPy solely for int64 arrays."""
from itertools import permutations,combinations
from collections import defaultdict
from math import comb, prod as scalar_product
import numpy as np

def prod(a,b):
    c=defaultdict(int)
    for x,v in a.items():
      for y,w in b.items():c[tuple(i+j for i,j in zip(x,y))]+=v*w
    return {i:v for i,v in c.items() if v}
def add(a,b,m=1):
    r=defaultdict(int,a)
    for j,v in b.items():r[j]+=m*v
    return {j:v for j,v in r.items() if v}
def det(A):
    n=len(A);out={}
    for p in permutations(range(n)):
        term={ (0,)*6:1}
        for i,j in enumerate(p):term=prod(term,A[i][j])
        out=add(out,term,(-1)**sum(a>b for a,b in combinations(p,2)))
    return out

def trans(P):
    m=tuple(max(k[i] for k in P) for i in range(6))
    low=tuple(min(k[i] for k in P) for i in range(6))
    m=tuple(a-b for a,b in zip(m,low))
    length=sum(abs(x) for x in P.values())
    assert length * scalar_product(comb(k,k//2) for k in m)<2**63,(length,m)
    z=np.zeros(tuple(k+1 for k in m),dtype=np.int64)
    for k,x in P.items(): z[tuple(a-b for a,b in zip(k,low))]=x
    for i,d in enumerate(m):
        A=np.array([[comb(d-k,l) if l<=d-k else 0 for k in range(d+1)] for l in range(d+1)],dtype=np.int64)
        z=np.moveaxis(z,i,0)
        z=(A@z.reshape(d+1,-1)).reshape(z.shape)
        z=np.moveaxis(z,0,i)
    return z
def make(mats):
    T=[]
    for i in range(4):
        T.append([])
        for j in range(4):
            mon=tuple(sum(l>=k for l in (i,j)) if i!=j else 0 for k in range(4))+tuple(sum((i in S)!=(j in S) for S in mats[k:k+1]) for k in range(2))
            T[-1].append({mon:1})
    return T
if __name__=='__main__':
 for mats in combinations([{0,1},{0,2},{0,3}],2):
    T=make(mats);w=[]
    for k in range(4):w.append(det([[T[i][j] if j!=k else {(0,)*6:1} for j in range(4)] for i in range(4)]))
    for l in range(6):
        P={}
        for i,j in combinations(range(4),2):
           m=next(iter(T[i][j]))[l]
           if m:P=add(P,prod(prod(w[i],w[j]),T[i][j]),m)
        Z=trans(P)
        assert Z.min()>=0 and Z.max()>0
        print(tuple(tuple(sorted(S)) for S in mats),l+1,int((Z>0).sum()),flush=True)
 print('All 18 derivative polynomials have only nonnegative integer coefficients.')
