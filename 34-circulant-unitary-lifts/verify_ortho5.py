#!/usr/bin/env python3
"""Exact finite exceptional cases for order-five orthostochastic lifting.
No trigonometry, algebraic-root approximation, or floating point arithmetic."""
import itertools
import sympy as sp
from functools import lru_cache
t=sp.symbols('t')
def signs(X): return tuple(itertools.product([1,-1],repeat=X))
ALL=signs(5)
def num(expr):
    return sp.Poly(sp.cancel(expr).as_numer_denom()[0],t,domain=sp.QQ)
def can_lift(BAL):
    choices=[(1,1,1,1,1)]+[s for s in ALL if s[0]==1 and s!=(1,1,1,1,1)]
    def compatible(i,j,u,v):
        h=(j-i)%5
        if h>2:return compatible(j,i,v,u)
        z=tuple(u[(j+s)%5]*v[(j+s)%5] for s in range(5))
        return z in BAL[h]
    def search(rows):
        j=len(rows)
        if j==5:return True
        return any(search(rows+[v]) for v in choices
                   if all(compatible(i,j,u,v) for i,u in enumerate(rows)))
    circ=False
    for c in choices:
        if all(tuple(c[s]*c[(s+h)%5] for s in range(5)) in BAL[h] for h in [1,2]):
            circ=True;break
    return search([choices[0]]),circ
if __name__=='__main__':
    for f in (1,-1):
        for pos in (1,2):
            W=[sp.Integer(1)]*5;W[0]=t;W[pos]=1+f*t
            V=[W[(i+2)%5]*W[(i+4)%5]/W[(i+3)%5] for i in range(5)]
            polys={h:{e:num(sum(a*b for a,b in zip(e,X))) for e in ALL} for h,X in [(1,W),(2,V)]}
            fac=set()
            for pp in polys[2].values():
                assert not pp.is_zero # otherwise the finite-exception argument would fail
                for g,_ in pp.factor_list()[1]:
                    # discard roots at t=0 or 1+ft=0, for which some amplitudes vanish.
                    if g.gcd(num(t*(1+f*t))).degree():continue
                    if g.count_roots(0,sp.oo if f==1 else 1):fac.add(g.monic())
            got=[]
            for g in sorted(fac,key=str):
                BAL={h:{e for e,y in polys[h].items() if y.rem(g).is_zero} for h in (1,2)}
                u,c=can_lift(BAL)
                assert u==c,(W,g)
                got.append(int(c))
            print(f'family={f:+d}, position={pos}: {len(got)} irreducible factors with admissible root; {sum(got)} realizable factors; all real lifts matched')
    print('PASS')
