"""A finite certificate using only integers; optional exact Markov-chain crosscheck."""
from fractions import Fraction as F
from itertools import permutations
from math import factorial
D=10**9
def certify(N=4095):
    inv=[0]+[(D+j-1)//j for j in range(1,N+1)] # ceil(D/j)
    H=[0]
    for u in inv[1:]: H.append(u+H[-1])
    smallest=None
    for n in range(2,N+1):
        X=sum(D*D//(i*(H[n]-H[i-1])) for i in range(2,n+1))
        # E[tau]/n >= X/D. Lower-sum D*exp(X/D) with downward rounding.
        a=b=D
        for k in range(1,81):
            a=a*X//(D*k)
            b+=a
        # log n <= H_n - (1+1/n)/2 <= H_n-1/2, by convex trapezoids.
        margin=b-n*(H[n]-D//2)
        assert margin>0,(n,margin)
        if smallest is None or margin<smallest[0]: smallest=(margin,n)
    print(f'All 2 <= n <= {N} certified. Smallest absolute exponential slack lower bound: {smallest[0]}/{D} at n={smallest[1]}')
def deckcheck(n,T):
    perms=list(permutations(range(n))); start=perms[0]
    v={s:F(s==start) for s in perms}; b=[F(0)]*(n+1);b[1]=F(1)
    # b[k]: k cards already below bookmark. Success probability p_(k+1).
    for t in range(T+1):
        sep=1-factorial(n)*min(v.values())
        assert sep==1-b[n],(n,t,sep,b[n])
        nv={s:F(0) for s in perms};nb=[F(0)]*(n+1);nb[n]=b[n]
        for k in range(1,n):
            i=k+1; p=F(i,n)*sum((F(1,j) for j in range(i,n+1)),F(0))
            nb[k]+=b[k]*(1-p);nb[k+1]+=b[k]*p
        for s,w in v.items():
            for j in range(n): # j from top; insertion destination is j through n-1
                for l in range(j,n):
                    out=s[:j]+s[j+1:l+1]+s[j:j+1]+s[l+1:]
                    nv[out]+=w/F(n*(n-j))
        b,v=nb,nv
    print('Exact separation/bookmark match:',n,'cards, times 0 through',T)
if __name__=='__main__':
    certify()
    for n in range(2,6): deckcheck(n,12)
