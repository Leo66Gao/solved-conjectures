"""Exhaustive, integer-only checks of the shell lemma and entropy certificate.
Default n=1..7 and r=1..10. No numerical entropy, stochastic search, or dependencies.
Optional: python verify.py MAX_N MAX_R
"""
from math import comb, prod
from collections import Counter
from itertools import combinations_with_replacement
import sys

def sign_sums(distances, r):
    counts={0:1}
    for a in distances:
        n=Counter()
        for k,c in counts.items():
            n[k+a]+=c
            n[k+r-a]+=c
        counts=n
    return counts

def prime_factors(k):
    d, f=2,Counter()
    while d*d<=k:
        while k%d==0: f[d]+=1;k//=d
        d+=1
    if k>1:f[k]+=1
    return f

def main(N=7,R=10):
    def convolve(a,b):
        return [sum(x*b[k-j] for j,x in enumerate(a) if 0<=k-j<len(b)) for k in range(len(a)+len(b)-1)]
    p=(3,27,33,1); s=(2,30,30,2)
    u,v=convolve(p,p[::-1]),convolve(s,s)
    assert u==[3,126,1005,1828,1005,126,3] and v==[4,120,1020,1808,1020,120,4]
    assert prod(x**x for x in u)<prod(x**x for x in v)
    print('Quaternary counterexample to independent symmetrization: exact product check passed.',flush=True)
    cases=shells=equal=0
    for n in range(1,N+1):
        # centered score C_d(k) = 2^(-d) E_count log choose(d,.) - log choose(d,k).
        # Multiplying each by 2^n makes the score an integer linear combination of prime logs.
        scores={}
        for d in (n,n-1):
            fs=[prime_factors(comb(d,k)) for k in range(d+1)]
            primes=set().union(*(f.keys() for f in fs))
            for k,f in enumerate(fs):
                scores[d,k]={p:(1<<(n-d))*sum(comb(d,j)*fj[p] for j,fj in enumerate(fs))-(1<<n)*f[p] for p in primes}
        for r in range(1,R+1):
            for v in combinations_with_replacement(range(r//2+1),n):
                cases+=1
                inner=[a for a in v if a!=0]
                m=len(inner)
                if m:
                    cc=sign_sums(inner,r)
                    for j in range(1,(m-1)//2+1):
                        shells+=1
                        le=sum(c for k,c in cc.items() if k<=j*r)
                        bound=2*sum(comb(m-1,i) for i in range(j))
                        assert le<=bound,(r,n,v,j,le,bound)
                c=Counter()
                for k,a in sign_sums(v,r).items():
                    q,rem=divmod(k,r)
                    for p,e in scores[n-(rem!=0),q].items(): c[p]+=e*a
                num=prod(p**e for p,e in c.items() if e>0)
                den=prod(p**-e for p,e in c.items() if e<0)
                assert num<=den,(n,r,v)
                equal+=(num==den)
    print(f'n=1..{N}, r=1..{R}; {cases} sign-radius configurations; {shells} exact one-sided shell checks; {equal} exact tangent equalities; all passed.')
if __name__=='__main__':main(*map(int,sys.argv[1:]))
