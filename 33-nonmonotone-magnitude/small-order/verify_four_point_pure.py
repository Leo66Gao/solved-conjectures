"""Independent, standard-library-only four-point certificate with arbitrary-precision integers.

Instead of direct binomial matrices, reverse each coefficient line and Taylor-shift
it using repeated multiplication by (1+x), via Horner's rule. The Cramer numerators
are built from cofactors, not determinants with a changed column.
"""
from itertools import combinations
from collections import defaultdict
from math import prod

ZERO=(0,)*6
def add(a,b,sgn=1):
    for k,x in b.items():a[k]+=sgn*x
def monprod(a,b):
    return tuple(x+y for x,y in zip(a,b))
def mul(a,b):
    c=defaultdict(int)
    for i,x in a.items():
        for j,y in b.items():c[monprod(i,j)]+=x*y
    return c
def minor_det(U,rows,cols):
    if not rows:return {ZERO:1}
    ans=defaultdict(int)
    for j,col in enumerate(cols):
        a=U[rows[0]][col]
        for k,x in minor_det(U,rows[1:],cols[:j]+cols[j+1:]).items():
            ans[monprod(a,k)]+=(-1 if j%2 else 1)*x
    return ans

def shift_check(P):
    P={k:v for k,v in P.items() if v}
    lo=[min(k[i] for k in P) for i in range(6)]
    dims=[max(k[i] for k in P)-lo[i]+1 for i in range(6)]
    strides=[prod(dims[i+1:]) for i in range(6)];total=prod(dims)
    p=[0]*total
    for k,x in P.items():p[sum((k_i-l_i)*s for k_i,l_i,s in zip(k,lo,strides))]=x
    # For each axis line q-coefficients p_0,p_1,...,p_d, Horner in (1+x)
    # applied in that order gives sum_{i=0}^d p_i (1+x)^{d-i}.
    for k,(length,s) in enumerate(zip(dims,strides)):
        B=length*s
        for base in range(0,total,B):
            for j in range(base,base+s):
                line=p[j:j+B:s]
                z=[line[0]]
                for v in line[1:]:
                    z=[z[0]+v]+[x+y for x,y in zip(z[1:],z)]+[z[-1]]
                p[j:j+B:s]=z
    assert min(p)>=0
    return sum(x>0 for x in p)
def crossing(i,j,S):return int((i in S)!=(j in S))
if __name__=='__main__':
    for S,T in combinations(({0,1},{0,2},{0,3}),2):
        U=[[ZERO if i==j else tuple(int(i>=r)+int(j>=r) for r in range(4))+
            (crossing(i,j,S),crossing(i,j,T)) for j in range(4)] for i in range(4)]
        W=[defaultdict(int) for i in range(4)]
        for i in range(4):
            for j in range(4): # sum of column-i cofactors, the i-th adjugate row sum
                rows=tuple(k for k in range(4) if k!=j);cols=tuple(k for k in range(4) if k!=i)
                add(W[i],minor_det(U,rows,cols),(-1 if (i+j)%2 else 1))
        W=[{k:v for k,v in p.items() if v} for p in W]
        pairs={(i,j):mul(mul(W[i],W[j]),{U[i][j]:1}) for i,j in combinations(range(4),2)}
        for k in range(6):
            P=defaultdict(int)
            for (i,j),p in pairs.items():add(P,p,U[i][j][k])
            c=shift_check(P)
            assert c>0
            print((tuple(sorted(S)),tuple(sorted(T))),k+1,c,flush=True)
    print('All 18 derivative polynomials have only nonnegative integer coefficients.')
