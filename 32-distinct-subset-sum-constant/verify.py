"""Private work for Leo Gao, with OpenAI AI assistance. Recheck all numerics.
Python 3 + scipy + numpy; no network. Floating computations are corroboration;
the 0.737 certificate is entirely rational."""
import math
from fractions import Fraction as F
from math import pi, sin, tan, atan, exp
import numpy as np
from scipy.optimize import brentq, minimize_scalar
def trans(k):
    return [[(F(2)**(i+1-k) if j==0 else F(2)**(i+j-k) if j<=k-1-i else F(0)) for j in range(k)] for i in range(k)]
def qdir(k,s):
    p=trans(k);v=[F(int(i==0)) for i in range(k)]
    for _ in range(2*s):v=[sum(v[i]*p[i][j] for i in range(k)) for j in range(k)]
    return v[0]/2
def spec(k,s):
    acc=1/(k+1)
    for m in range(1,k):
        a=brentq(lambda x:(k-.5)*x+atan(3*tan(x/2))-m*pi,(m*pi/(k+1))-1e-12,m*pi/k+1e-12)
        acc+=(2/(k+1+(9*k-3)*tan(a/2)**2))*exp(-s*math.log1p(8*sin(a/2)**2))
    return acc
def theta(a):
    return (2*a)**(1/3)*(1+2*sum(exp(-2*pi*pi*a*m*m) for m in range(1,100)))
def det_mod(q,k,s):
    from sympy import Matrix
    w=k-1;L=2*s;r=w*L+1;d=r-1;M=2*Matrix.eye(r)
    for h in range(L):
        for j in range(w):
            i=h*w+j;M[i,i+1]-=1
            M[i,(h+1)*w+w-j if h<L-1 else 0]-=1
    M[d,0]-=1
    assert int(M.det()) == q
    c=[int(x)%q for x in M.adjugate()[:,0]];assert len(set(c))==r
    layers=[set() for _ in range(r+1)]
    for bits in range(1<<r):
        k0=bits.bit_count();v=sum(c[i] for i in range(r) if bits>>i&1)%q
        assert v not in layers[k0];layers[k0].add(v)
for k in range(2,15):
    for s in [1,2,5,10]:
        v=qdir(k,s);r=2*s*(k-1)+1
        assert (v*2**r).denominator==1
        assert abs(float(v)-spec(k,s))<1e-11
        if r<=10: det_mod(int(v*2**r),k,s)
print("52 exact-chain/spectral checks; all r<=10 tested by determinant & modular cardinality layers.")
alpha=F(2,15)
x=4*F(31415,10000)**2/15
q=F(72,1000)
assert 1/q < sum(x**j/math.factorial(j) for j in range(12))
v=1+2*(q+q**4/(1-q**5))
assert 2*alpha*v**3 < F(737,1000)**3
print("Exact rational certificate C(2/15)<0.737 verified (using pi>3.1415).")
for k in [20,50,100,200,500,1000]:
    s=round(float(alpha)*k*k);r=2*s*(k-1)+1
    print(k,s,round(r**(1/3)*spec(k,s),8))
opt=minimize_scalar(theta,bounds=(.01,1),method='bounded',options={'xatol':1e-13})
print('numerical optimum only',opt.x,opt.fun)
def sweep(k,s):
    p=[F(1)]+[F(0)]*k
    for t in range(2*s):
        for i in (range(k) if t%2==0 else reversed(range(k))):
            p[i]=p[i+1]=(p[i]+p[i+1])/2
    return p[0]
for k in range(2,12):
    for s in range(1,7):
        assert qdir(k,s)==sweep(k,s)
print("60 exact alternating-adjacent-sweep vs reflected-chain identifications.")
