"""Exact sign of magnitude derivative for every induced proper unperturbed split-cube subspace."""
import itertools, math
from collections import Counter
X=list(itertools.product([0,1],repeat=3))[1:]+['+','-']
def dd(x,y):
    if x==y:return 0
    if isinstance(x,str) and isinstance(y,str):return 4
    if isinstance(x,str):return 1+2*sum(y)
    if isinstance(y,str):return 1+2*sum(x)
    return 2*sum(a!=b for a,b in zip(x,y))
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sign=1):
    return trim([(a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)
def der(a):return [i*x for i,x in enumerate(a) if i]
def determinant(M):
    n=len(M);tab={0:[1]}
    for mask in range(1,1<<n):
        i=mask.bit_count()-1; p=[0]
        for j,d in enumerate(M[i]):
            if d is not None and mask&(1<<j):
                sign=(-1)**((mask>>(j+1)).bit_count());p=add(p,[0]*d+tab[mask^(1<<j)],sign)
        tab[mask]=p
    return tab[(1<<n)-1]
def solve(S):
    D=[[dd(x,y) for y in S] for x in S];den=determinant(D)
    num=[-x for x in determinant([r+[0] for r in D]+[[0]*len(D)+[None]])]
    # On (0,1), the sign of -M_q equals sign(num den'-num' den).
    J=add(mul(num,der(den)),mul(der(num),den),-1);n=len(J)-1
    # (1+z)^n J(z/(1+z)), z>0. All coefficients nonnegative imply sign.
    a=[0]*(n+1)
    for i,x in enumerate(J):
        for j in range(n-i+1):a[i+j]+=x*math.comb(n-i,j)
    if min(a)<0 or max(a)==0: raise ArithmeticError((S,a))
seen=Counter()
for k in range(2,9):
    for S in itertools.combinations(X,k):solve(S);seen[k]+=1
print('Sizes and strictly increasing proper unperturbed subspaces:',sorted(seen.items()))
