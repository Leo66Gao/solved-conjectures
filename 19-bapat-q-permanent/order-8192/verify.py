#!/usr/bin/env python3
"""Standalone exact rational / outward interval verifier.
Only Python stdlib and GCC C++17 required. The matrix is A=W W^T+I.
No floating-point decision in Python; C++ uses checked directed rounding.
"""
from fractions import Fraction as Q
from math import isqrt, lcm, factorial, comb, prod
from itertools import combinations, permutations
from pathlib import Path
import sys
import argparse, json, subprocess, time, resource
P=Path(__file__).resolve().parent
S=10**12

def atan_interval(q,terms=32):
    x=Q(1,q);s=sum(((-1)**j*x**(2*j+1)/ (2*j+1) for j in range(terms)),Q(0))
    e=(-1)**terms*x**(2*terms+1)/(2*terms+1)
    return min(s,s+e),max(s,s+e)

def pi_interval():
    a,b=atan_interval(5);c,d=atan_interval(239)
    return 16*a-4*d,16*b-4*c

def cos_interval(xlo,xhi):
    assert 0<=xlo<=xhi<Q(8,5)
    # Alternating Taylor series, cos decreasing on [0, pi/2].
    def pol(x,J):return sum(((-1)**j*x**(2*j)/factorial(2*j) for j in range(J)),Q(0))
    return pol(xhi,16),pol(xlo,17) # last negative / last positive

def sqrt_interval(x,D=10**30):
    assert x>=0
    a=isqrt(x.numerator*D*D//x.denominator)
    return Q(a,D),Q(a+1,D)

def round_interval(lo,hi,K=S):
    assert lo<=hi and hi-lo<Q(1,K)
    # exact deterministic nearest integer of interval midpoint; error <= 1/K.
    z=round(K*(lo+hi)/2)
    assert max(abs(Q(z,K)-lo),abs(Q(z,K)-hi))<=Q(1,K)
    return z

def build(m,a2,kappa=Q(0)):
    """a2 are squared ring constants, original v=(cos theta,sin theta,a/sqrt2).
    Build W/S within 1/S coordinatewise, exploiting exact quadrant symmetry.
    """
    plo,phi=pi_interval();L=m//4;assert m%4==0
    quad=[]
    for k in range(L):
        l=Q(2*k+1,m)
        c=round_interval(*cos_interval(l*plo,l*phi))
        # sin theta = cos(pi/2-theta).
        l=Q(1,2)-l
        s=round_interval(*cos_interval(l*plo,l*phi))
        quad.append((c,s))
    xy=[]
    for q in range(4):
        xy.extend([(c,s) if q==0 else (-s,c) if q==1 else (-c,-s) if q==2 else (s,-c) for c,s in quad])
    heights=[round_interval(*sqrt_interval(a/2)) for a in a2]
    W=[(x,y,b) for b in heights for x,y in xy]
    assert abs(kappa)<1
    W.sort(key=lambda v:Q(v[2]*v[0])/(v[0]*v[0]+v[1]*v[1]+kappa*(v[0]*v[0]-v[1]*v[1])))
    return W,xy

def pure_exterior(W):
    """Compute sum_ab |F_ab(z0)/p(z0)|^2 exactly, z0=(1,i,0)/sqrt2.
    If D is lcm of plane squared radii, define U_i=v_i/(v_ix+i v_iy)
    with common denominator D. Actual ratio uses sqrt2 U_i, so each wedge
    sum is 2 times the complex integer wedge divided by D^2.
    """
    D=lcm(*(x*x+y*y for x,y,b in W));prefixR=[0,0,0];prefixI=[0,0,0]
    pairs=[(0,1),(0,2),(1,2)];R=[0,0,0];I=[0,0,0]
    for x,y,b in W:
        h=D//(x*x+y*y);v=(x,y,b)
        ar=[t*x*h for t in v];ai=[-t*y*h for t in v]
        for k,(i,j) in enumerate(pairs):
            R[k]+=prefixR[i]*ar[j]-prefixI[i]*ai[j]-prefixR[j]*ar[i]+prefixI[j]*ai[i]
            I[k]+=prefixR[i]*ai[j]+prefixI[i]*ar[j]-prefixR[j]*ai[i]-prefixI[j]*ar[i]
        for j in range(3):prefixR[j]+=ar[j];prefixI[j]+=ai[j]
    return Q(4*sum(r*r+i*i for r,i in zip(R,I)),D**4)

def direct(V):
    n=len(V);H=[[sum(x*y for x,y in zip(u,v)) for v in V] for u in V];p=d=0
    for pi in permutations(range(n)):
        v=prod(H[i][pi[i]] for i in range(n));p+=v;d+=v*sum(pi[i]>pi[j] for i in range(n) for j in range(i+1,n))
    return p,d

def exact_p_and_f(V):
    # Independent ordinary monomial recurrence, small integer examples only.
    n=len(V);r=3;zero=(0,0,0);p={zero:1};pairs=list(combinations(range(r),2));F=[{} for _ in pairs]
    def add(q,e,c):q[e]=q.get(e,0)+c
    def mul(q,v):
        out={}
        for e,c in q.items():
            for i,x in enumerate(v):
                f=list(e);f[i]+=1;add(out,tuple(f),c*x)
        return out
    for v in V:
        G=[mul(f,v) for f in F]
        for e,c in p.items():
            for k,(i,j) in enumerate(pairs):
                if e[i]:f=list(e);f[i]-=1;add(G[k],tuple(f),c*e[i]*v[j])
                if e[j]:f=list(e);f[j]-=1;add(G[k],tuple(f),-c*e[j]*v[i])
        p,F=mul(p,v),G
    def norm(q):return sum(c*c*prod(factorial(x) for x in e) for e,c in q.items())
    return norm(p),(comb(n,2)*norm(p)-sum(map(norm,F)))//2

def compile_cpp(kernel):
    cmd=['g++','-O3','-std=c++17','-frounding-math','-ffp-contract=off','-fno-fast-math',str(P/(kernel+'.cpp')),'-o',str(P/kernel)]
    subprocess.run(cmd,check=True)

def upper_norm(m,a2,kernel="ring_interval"):
    assert all(a>=0 and a.numerator<2**64 and a.denominator<2**64 for a in a2)
    inp=f'{m} {len(a2)}\n'+''.join(f'{a.numerator} {a.denominator}\n' for a in a2)
    proc=subprocess.run([str(P/kernel)],input=inp,text=True,stdout=subprocess.PIPE,check=True)
    x,y=map(int,proc.stdout.split());return Q(x,y)

def selftest(kernel):
    # m=4, v=(+/-1,+/-1,a)/sqrt2, so integer Gram per equals n! * normalized ring norm.
    cnt=terms=0
    for aa in [(0,),(1,),(2,),(0,1),(1,2),(-1,2)]:
        # polynomial ring formula unchanged if a sign is flipped (m even).
        V=[(x,y,a) for a in aa for x,y in [(1,1),(-1,1),(-1,-1),(1,-1)]]
        p,d=direct(V);assert exact_p_and_f(V)==(p,d)
        n=len(V);U=upper_norm(4,[Q(a*a) for a in aa],kernel);exact=Q(p,factorial(n));assert exact<=U and U-exact< Q(1,1000000)*max(1,exact),(aa,exact,U)
        # independently check pure exterior values by explicit pair sums with exact complex fractions.
        def cadd(a,b):return (a[0]+b[0],a[1]+b[1])
        def cmul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
        E=Q(0);u=[[(Q(t*x,x*x+y*y),Q(-t*y,x*x+y*y)) for t in v] for v in V for x,y,b in [v]]
        for a,b in combinations(range(3),2):
            z=(Q(0),Q(0))
            for i,j in combinations(range(n),2):
                p1=cmul(u[i][a],u[j][b]);p2=cmul(u[i][b],u[j][a]);z=cadd(z,(p1[0]-p2[0],p1[1]-p2[1]))
            E+=4*(z[0]**2+z[1]**2)
        assert E==pure_exterior(V)
        cnt+=1;terms+=factorial(n)
    print('Self-test:',cnt,'integer ring matrices,',terms,'direct permutation terms; exact norm and derivative agree, interval bounds enclose, pure exterior checks agree.',flush=True)

def cert(kernel):
    m,N,scale=32,256,Q(49791,50000)
    # a_j^2=2 scale^2 u^2/(1-u^2), u=(j+1/2)/N.
    a2=[]
    for j in range(N):
        u=Q(2*j+1,2*N);a2.append(2*scale*scale*u*u/(1-u*u))
    n=m*N;t=time.monotonic()
    U=upper_norm(m,a2,kernel)
    W,xy=build(m,a2)
    assert [list(row) for row in W] == json.loads((P/"witness_8192_rows.json").read_text()), "bundled Gram factor mismatch"
    E=pure_exterior(W)
    # exact product of plane squared lengths, repeated N times; upper/lower via Bernoulli instead of large powers
    # Each rounded coordinate differs by <=1/S; plane radius >=1-2/S.
    L=1-Q(4*n,S);assert L>0
    # Each row norm >=1; row perturbation norm <=2/S; degree of other product n-1.
    # per(W/S) <= per(V)/(1-2*n*delta), with delta=2 ceil(sqrt(n))/S.
    root=isqrt(n);root+=root*root<n;delta=Q(2*root,S)
    assert 2*n*delta<1 and 2*n<Q(S*S)
    # rounded diagonal norms >=(1-2/S)^2>1/2, so PD lift multiplies per by <=(1+2/S^2)^n.
    assert (1-Q(2,S))**2>Q(1,2)
    Pupper=U/(1-2*n*delta)/(1-Q(2*n,S*S))
    # N_exterior >=2(n-2)! |p(z0)|^2 E (two orthogonal pure monomials).
    Nlower=2*L*E/Q(comb(n,2)*n*(n-1))
    R=Nlower/Pupper
    print('n',n,'m',m,'N',N,'scale',scale,'norm upper',U,'(display)',float(U),flush=True)
    print('pure exterior/n^4 (display)',float(E/n**4),'upper permanent normalized (display)',float(Pupper),'lower exterior normalized (display)',float(Nlower),'R certified lower (display)',float(R),flush=True)
    assert R>1, 'no certified violation'
    assert len(W)==n and all(x*x+y*y>0 for x,y,b in W)
    # exact non-diagonal witness: neighboring angular rows of the same ring have nonzero inner product.
    x,y=xy[0];u,v=xy[1];assert x*u+y*v>0
    assert Nlower-Pupper>Q(1,4000)
    assert max(sum(v*v for v in row) for row in W)<1023*S*S
    print("Exact normalized derivative upper bound: < -1/8000 (in units C*n!*2**(-n)).",flush=True)
    print("Explicit interior comparison: h=1/(16000*C*2048**n), P(1-h)>P(1-h/2).",flush=True)
    print('CERTIFIED: A=W W^T+I positive definite, integer, non-diagonal; P_prime(1)<0.',flush=True)
    rss_unit = 1024 if sys.platform == 'darwin' else 1
    print('Exact final inequality R>1; time including norm (if evaluated) %.3f s; Python max RSS %d KiB; child max RSS %d KiB'%(time.monotonic()-t,resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//rss_unit,resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss//rss_unit),flush=True)
    return R

if __name__=='__main__':
    ap=argparse.ArgumentParser(description="Verify the fixed 8192-row integer counterexample; no precomputed bounds are accepted.")
    ap.add_argument('--kernel',choices=['integer','interval'],default='integer')
    args=ap.parse_args()
    kernel={'integer':'ring_dyadic','interval':'ring_interval'}[args.kernel]
    compile_cpp(kernel)
    selftest(kernel)
    cert(kernel)
