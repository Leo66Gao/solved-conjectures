#!/usr/bin/env python3
"""Independent direct convolution for two explicit integer witnesses; stdlib only."""
from collections import Counter
from fractions import Fraction
from itertools import product

def make(r, weight, subtract):
    S = {sign * 5**j for j in range(r) for sign in (-1,1)}
    return {**dict.fromkeys(S,1),0:weight},{**dict.fromkeys(S,1),0:-subtract}

def conv(g,a):
    c = Counter()
    for i,gi in g.items():
        for j,aj in a.items():
            c[i+j] += gi*aj
    return c

def check(r,s,t):
    g,a=make(r,s,t)
    assert min(g.values())>=0 and sum(a.values()) and len(a)==2*r+1
    c=conv(g,a)
    d=2*r
    assert Counter(c.values())==Counter({d-s*t:1,s-t:d,1:d,2:2*d*(d-2)//4})
    lhs=sum(v*v for v in c.values())
    assert lhs==(d-s*t)**2+d*(s-t)**2+d+2*d*(d-2)
    rhs=Fraction(sum(v*v for v in g.values())*sum(a.values())**2,len(a))
    print(f"r={r}, s={s}, t={t}: support={len(a)}, convolution norm squared={lhs}, required lower bound={rhs}, deficit={rhs-lhs}, normalized ratio={lhs/rhs}")
    assert lhs<rhs
    return lhs/rhs

def exact_tensor_check():
    # This checks a tensor embedding on tiny, arbitrary integer inputs, not asymptotics.
    g,a=make(2,3,1)
    L=5**2
    g2={x+L*y:u*v for (x,u),(y,v) in product(g.items(),repeat=2)}
    a2={x+L*y:u*v for (x,u),(y,v) in product(a.items(),repeat=2)}
    c=conv(g,a); cc=conv(g2,a2)
    assert len(a2)==len(a)**2
    assert all(cc[x+L*y]==u*v for (x,u),(y,v) in product(c.items(),repeat=2))
    assert sum(z*z for z in cc.values())==sum(z*z for z in c.values())**2
    print("Exact independent 2-block digit-convolution check passed.")
if __name__=="__main__":
    assert check(17,11,4)==Fraction(6958,6975)
    q=check(256,40,18)
    assert q==Fraction(2601,3211)
    assert 513*q**30<1
    print("513 * (2601/3211)^30 < 1 (exact)")
    exact_tensor_check()

def compact_dense_check():
    # One signed Sidon packing: same coefficients in length 1059.
    marks=[1,4,10,17,29,52,67,89,132,164,205,259,303,350,405,505,529]
    rad=max(marks)
    g=[0]*(2*rad+1); a=g.copy()
    for m in marks:
        for i in (rad-m,rad+m): g[i]=a[i]=1
    g[rad]=11; a[rad]=-4
    # Intentionally separate from sparse conv(): summing products for each output.
    l=len(g)
    c=[sum(g[i]*a[j-i] for i in range(max(0,j-l+1),min(l-1,j)+1)) for j in range(2*l-1)]
    assert Counter(c)==Counter({0:1504,-10:1,1:34,2:544,7:34})
    assert sum(z*z for z in c)==3976
    assert sum(g_i*g_i for g_i in g)*sum(a)**2==139500
    print("Compact dense realization on [-529,529]: squared norm 3976.")
if __name__=='__main__':
    compact_dense_check()
