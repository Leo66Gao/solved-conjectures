"""Independently determine PGST by saturated integer relation lattices.

Python 3, SymPy 1.14. No tolerance or time sampling.
"""
from math import gcd, prod
from itertools import combinations
import sympy as s
from sympy.matrices.normalforms import smith_normal_decomp
X=s.Symbol('X')
def poly(e): return s.Poly(e,X,domain=s.ZZ)
def get_order(n,rows):
    A=s.Matrix([[1]*n, *rows])
    D,U,V=smith_normal_decomp(A,domain=s.ZZ)
    r=sum(D[i,i]!=0 for i in range(min(D.shape)))
    assert D==U*A*V
    # V is unimodular, so last n-r columns are a Z-basis of the kernel.
    g=n
    for j in range(r,n):
        g=gcd(g,int(sum(k*V[k,j] for k in range(n))))
    return g

def run():
    n_generic=n_magnetic=0
    for n in range(3,16):
        phi=poly(s.cyclotomic_poly(n,X)); e=phi.degree()
        powers=[poly(X**k).rem(phi) for k in range(n)]
        def rows(vecs):
            return [[v.nth(i) for v in vecs] for i in range(e)]
        hops=list(range(1,n//2+1))
        for m in range(1,min(3,len(hops))+1):
            for support in combinations(hops,m):
                orders={n//gcd(n,k) for k in support}
                expected=prod(int(s.cyclotomic_poly(d,X).subs(X,1)) for d in orders)
                got=get_order(n, sum((rows([powers[k*a%n] for k in range(n)]) for a in support), []))
                assert got==expected,(n,support,got,expected)
                n_generic+=1
        # h=1, 1-z, (1-z)^2, 1+2z, z, (1-z)^3. For p^a, h=1+2z 
        # has valuation 1 if p=3 and a>1, and 1 likewise if n=3
        # (1+2z = 3+2(z-1); the two terms have distinct valuations).
        for h,order_v in [
            (poly(1),0),(poly(1-X),1),(poly((1-X)**2),2),
            (poly(1+2*X),1 if n in [3,9] else 0),
            (poly(X),0),(poly((1-X)**3),3)
        ]:
            bar=sum((h.nth(j)*powers[-j%n] for j in range(h.degree()+1)),poly(0))
            lam=[(h*powers[k]+bar*powers[-k%n]).rem(phi) for k in range(n)]
            got=get_order(n,rows(lam))
            ps=list(s.factorint(n)); expected=1
            if len(ps)==1:
                p=ps[0]; parity=(order_v+(p==2))%2
                if parity==1: expected=p
            assert got==expected,(n,h,got,expected)
            n_magnetic+=1
    print('Independent Smith-normal-form generic support PGST checks:',n_generic)
    print('Independent Smith-normal-form fixed magnetic gain PGST checks:',n_magnetic)
if __name__=='__main__': run()
