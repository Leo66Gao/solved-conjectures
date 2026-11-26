#!/usr/bin/env python3
"""Independent exact Haar-vector moment test of arbitrary-dimension §5, for invariant polynomial pairs through degree three."""
from itertools import permutations
from functools import lru_cache
import sympy as s

def cycles(p):
    seen=set(); k=0
    for i in range(len(p)):
        if i in seen: continue
        k+=1
        while i not in seen:
            seen.add(i)
            i=p[i]
    return k
@lru_cache(None)
def lc(p):
    return cycles(p)
def compose(p,q):
    return tuple(p[j] for j in q)
def perm(parts,n):
    x=list(range(n)); base=0
    for length in parts:
        for j in range(length): x[base+j]=base+(j+1)%length
        base+=length
    return tuple(x)
@lru_cache(None)
def ps(n):
    return list(permutations(range(n)))
@lru_cache(None)
def moment(a,e,b,partsA,partsB):
    # disjoint tensor-copy supports for traces on A and B.
    n=sum(partsA)+sum(partsB)
    pa,pb=perm(partsA,n),perm((1,)*sum(partsA)+partsB,n)
    return s.Rational(sum(a**lc(compose(pa,z))*e**lc(z)*b**lc(compose(pb,z))
                  for z in ps(n)),s.rf(a*e*b,n))
def test(a,e,b):
    ka=[(2,),(3,)][:min(2,a-1)]
    kb=[(2,),(3,)][:min(2,b-1)]
    def m(i=(), j=()):return moment(a,e,b,i,j)
    GA=s.Matrix([[m(i+k)-m(i)*m(k) for k in ka] for i in ka])
    GB=s.Matrix([[m((),j+l)-m((),j)*m((),l) for l in kb] for j in kb])
    C=s.Matrix([[m(i,j)-m(i)*m((),j) for j in kb] for i in ka])
    predicted=s.Rational(e**2*(a*a-1)*(b*b-1),(a*a*e*e-1)*(b*b*e*e-1))
    assert C[0,0]>0 and C[0,0]**2/(GA[0,0]*GB[0,0])==predicted
    ev=(GA.inv()*C*GB.inv()*C.T).eigenvals()
    assert max(ev)==predicted
    print((a,e,b),"squared canonical correlations through degree 3",ev)
if __name__=="__main__":
    for dims in [(2,2,2),(3,2,4),(12,2,2),(9,2,3),(3,4,11)]:
        test(*dims)
    print("MARGINAL EXACT CHECKS PASSED")
