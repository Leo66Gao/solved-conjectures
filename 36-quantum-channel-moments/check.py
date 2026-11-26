#!/usr/bin/env python3
"""Exact finite checks, independent of the random-product bound. Python 3 + SymPy."""
from fractions import Fraction as F
from itertools import permutations, product
import sympy as s

def signperm(x):
    return (-1)**sum(a>b for i,a in enumerate(x) for b in x[i+1:])

def clifford(A, offset):
    # All 24 orientation-preserving signed permutations of the Pauli coordinates.
    channels = []
    for p in permutations(range(3)):
        for signs in product((-1,1),repeat=3):
            if signperm(p)*signs[0]*signs[1]*signs[2]<0:
                continue
            diag=[F(0)]*3; b=[F(0)]*3
            for j in range(3):
                diag[p[j]]=A[j]; b[p[j]]=offset[j]*signs[j]
            channels.append((diag,b))
    assert len(channels)==24
    return channels

def exact_twirl_examples():
    # Standard amplitude damping (survival 9/25), then optional Pauli X.
    for spin in (1,-1):
        A=[F(3,5),spin*F(3,5),spin*F(9,25)]
        channels=clifford(A,[0,0,spin*F(16,25)])
        p=sum(A)/3; u=sum(x*x for x in A)/3
        values=[]
        for n in (1,2,3,4):
            # Each draw has triangular Pauli transfer matrix with this diagonal.
            # Its full tensor power is triangular too, so no roots are estimated.
            spec={}
            for w in product(range(4), repeat=n):
                eig=sum(s.prod([F(1) if i==0 else diag[i-1] for i in w])
                        for diag,b in channels)/24
                spec[eig]=spec.get(eig,0)+1
            assert spec.pop(1)==1
            val=max(abs(a) for a in spec)
            assert val==(abs(p) if n==1 else max(abs(p),u))
            values.append(str(val))
        print("amplitude damping, sign",spin,"p",p,"u",u,"s1..4",values)

def compose(p,q):
    return tuple(p[q[i]] for i in range(len(q)))
def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))
def cycles(p):
    v=set(); c=0
    for i in range(len(p)):
        if i not in v:
            c+=1
            while i not in v:
                v.add(i); i=p[i]
    return c
def haar_stinespring(d,e,n):
    # Exact Weingarten contraction, NOT diagonal-block propagation.
    # Haar_N is the Gram-orthogonal projection onto span of copy permutations.
    # Embedding an input permutation into system x pure E has test overlaps
    # G_d; after Haar projection, tracing E contributes e^cycles pointwise.
    assert n<=d*e
    perms=list(permutations(range(n)))
    C=s.Matrix([[cycles(compose(inverse(i),j)) for j in perms] for i in perms])
    GN=C.applyfunc(lambda c:(d*e)**c)
    GD=C.applyfunc(lambda c:d**c)
    E=s.diag(*[e**cycles(i) for i in perms])
    M=E*GN.inv()*GD
    # M acts on a spanning family; possible extraneous zeros when n>d.
    # Its nonzero spectrum equals that of the full channel moment.
    roots=M.eigenvals()
    assert sum(roots.values())==len(perms) and roots.pop(1)==1
    q=s.Rational(e*(d*d-1),d*d*e*e-1)
    assert max(abs(k) for k in roots)==q
    c=s.Matrix([(d*e)**cycles(i) for i in perms])/s.rf(d*d*e,n)
    assert M*c==c
    assert sum(c[i]*d**cycles(w) for i,w in enumerate(perms))==1
    print("cHaar d,e,t =",d,e,n,"; nonprincipal nonzero spectrum:",
          ", ".join(f"{eig} (x{mult})" for eig,mult in roots.items() if eig!=0),
          "; Wishart fixed moment OK")

if __name__=='__main__':
    exact_twirl_examples()
    for d,e in [(2,2),(3,2),(2,3),(4,2)]:
        for n in [2,3,4]:
            haar_stinespring(d,e,n)
    print("ALL EXACT CHECKS PASSED")
