#!/usr/bin/env python3
"""Exact finite checks for the accompanying proof; Python 3 standard library only.
Gaussian integers are represented as pairs, not floating-point complex numbers.
"""
from itertools import product, permutations
from fractions import Fraction

def add(a,b): return a[0]+b[0],a[1]+b[1]
def mul(a,b): return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def conj(a): return a[0],-a[1]
def gpow(a,n):
    z=(1,0)
    while n:
        if n&1: z=mul(z,a)
        n//=2
        if n: a=mul(a,a)
    return z
def zero(n): return [[(0,0) for _ in range(n)] for _ in range(n)]
def eye(n):
    a=zero(n)
    for i in range(n): a[i][i]=(1,0)
    return a
def mm(a,b):
    n=len(a); c=zero(n)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                c[i][j]=add(c[i][j],mul(a[i][k],b[k][j]))
    return c
def trace(a):
    t=(0,0)
    for j,row in enumerate(a): t=add(t,row[j])
    return t
def rot(w,j): return w[j:]+w[:j]
def reversible(w): return any(rot(w,j)==w[::-1] for j in range(len(w)))
def splitpal(w): return any(w[:j]==w[:j][::-1] and w[j:]==w[j:][::-1] for j in range(len(w)+1))

def ordinary_trace(w):
    n=len(w); assert n>=3
    ops={c:zero(n) for c in set(w)}
    for h in ops.values():
        for j in range(n): h[j][j]=(3,0)
    for j,c in enumerate(w):
        k=(j+1)%n; phase=(0,1) if k==0 else (1,0)
        ops[c][j][k]=phase; ops[c][k][j]=conj(phase)
    a=eye(n)
    for c in w: a=mm(a,ops[c])
    return trace(a)

def verify_words():
    # Full necklace-palindrome equivalence checks; matrix arithmetic for one
    # representative of every binary necklace from length 3 through 8.
    reps=count=bad=0
    for n in range(1,11):
        for t in product('AB',repeat=n):
            w=''.join(t); r=reversible(w)
            assert r==splitpal(w)
            count+=1
            if not 3<=n<=8 or min(rot(w,j) for j in range(n))!=w: continue
            reps+=1
            z=ordinary_trace(w)
            expect=sum(rot(w,j)==w for j in range(n))-sum(rot(w[::-1],j)==w for j in range(n))
            assert z[1]==expect
            bad+=bool(z[1])
    print(f"Ordinary words: {count} palindrome/rotation checks; {reps} exact matrix checks ({bad} chiral).")
    z=ordinary_trace("AABABB"); m=2*z[0]
    assert z[1]==1 and gpow(z,m)[0]<0
    print(f"AABABB: complex seed trace {z[0]}+i; Re(z^{m}) < 0 (Gaussian-integer powering).")

def gram_coeff(c,p):
    # Enumerate ALL index permutations rather than presupposing only rotations.
    # Off-diagonal entries are divided by epsilon; the designated product is
    # the coefficient of the all-variable target monomial divided by epsilon^L.
    n=len(c); z=(0,0)
    for perm in permutations(range(n)):
        if any(c[i]!=c[j] or p[i]!=p[j] for i,j in enumerate(perm)): continue
        v=(1,0)
        for i,j in zip(perm,perm[1:]+perm[:1]):
            if (j-i)%n not in (1,n-1): v=(0,0); break
            v=mul(v,(0,1) if (i,j)==(n-1,0) else ((0,-1) if (i,j)==(0,n-1) else (1,0)))
        z=add(z,v)
    return z

def verify_decorated():
    count=0
    for c,nvals in [('ABAB',3),('ABCAB',2),('ABABAB',2),('ABCABC',2)]:
        # The end colors differ in every tested cyclic pattern.
        n=len(c)
        for p in product((Fraction(-2),Fraction(1,2),Fraction(3))[:nvals],repeat=n):
            w=tuple(zip(c,p)); h=sum(rot(w,j)==w for j in range(n))
            expected=(0,0 if reversible(w) else h)
            assert gram_coeff(c,p)==expected
            count+=1
    print(f"Decorated Gram cycles: {count} exact all-permutation coefficient checks (signed rational exponents).")


def verify_incommensurate():
    # Work in the nonorthogonal basis v_i. Then the matrix of P_i=v_i v_i*
    # is E_ii G. With x_i=2^(i+1), p_j=log_2 a_j, every x_i^p_j=a_j^(i+1)
    # is rational, even though p_j need not be rational or commensurable.
    powers=[2,3,Fraction(1,3),2,5,Fraction(1,2),2,3,Fraction(1,5),3]
    c='AB'*5; n=len(c); eps=Fraction(1,4); G=eye(n)
    for j in range(n):
        k=(j+1)%n; wt=(0,eps) if k==0 else (eps,0)
        G[j][k]=wt; G[k][j]=conj(wt)
    result=eye(n)
    for j,(color,a) in enumerate(zip(c,powers)):
        factor=eye(n)
        for i in range(n):
            if c[i]==color:
                d=Fraction(a)**(i+1)-1
                for s in range(n): factor[i][s]=add(factor[i][s],mul((d,0),G[i][s]))
        result=mm(result,factor)
    z=trace(result)
    assert not reversible(tuple(zip(c,powers))) and z[1]!=0
    print(f"Incommensurate mixed-sign, class-five witness: Im(trace) = {z[1]}.")

if __name__=="__main__":
    verify_words(); verify_decorated(); verify_incommensurate()
    print("All exact checks passed.")
