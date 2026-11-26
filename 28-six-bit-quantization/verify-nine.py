"""Exact certificate for unrestricted nine-to-six noisy quantization.
Standard-library only. Optional args: inclusive cardinality limits in [3,22].
"""
from math import comb
from fractions import Fraction as F
from collections import Counter
from functools import lru_cache
from sys import argv
def gen(f,last,m):
 if len(f)==m:yield tuple(sorted(f));return
 cand={1}
 for b in f:
  if b%2==0:cand.add(b+1)
  t=b & ~(b>>1)
  while t:
   u=t&-t;cand.add(b+u);t-=u
 for x in sorted(cand):
  if x<=last or x>=512:continue
  pr=([x-1] if x&1 else [])+[x-(1<<(j-1)) for j in range(1,x.bit_length()) if x>>(j-1)&3==2]
  if all(y in f for y in pr):
   f.add(x);yield from gen(f,x,m);f.remove(x)
def hist(S,d):
 W=Counter()
 for y in range(1<<d):
  a=[0]*(d+1)
  for x in S:a[(x^y).bit_count()]+=1
  W[tuple(a)]+=1
 return W
Q=1<<80
def up(a,b):return -(-a//b)
def lgsmall(a,b):
 z=Q*(a-b)//(a+b);h=up(Q*(a-b),a+b);sl=sh=0;lo=z*z//Q;hi=up(h*h,Q)
 for i in range(21):
  sl+=2*z//(2*i+1);sh+=up(2*h,2*i+1)
  z=z*lo//Q;h=up(h*hi,Q)
 return sl,sh+up(2*h*Q,43*(Q-hi))
L2=lgsmall(2,1)
def ln(a,b=1):
 k=a.bit_length()-b.bit_length()
 if (a<b<<k if k>=0 else a<<-k<b):k-=1
 aa=a if k>=0 else a<<(-k);bb=b if k<0 else b<<k
 assert bb<=aa<=2*bb
 l,h=lgsmall(aa,bb);return l+k*L2[k<0],h+k*L2[k>=0]
D=1<<40; end=D*(2**15-1)//2**16
@lru_cache(None)
def hb(a):return up(a*ln(D,a)[1]+(D-a)*ln(D,D-a)[1],D)
@lru_cache(None)
def powers(d,a):
 return [a**i*(D-a)**(d-i) for i in range(d+1)]
D=1<<60
end=D*(2**15-1)//2**16
rho=F(1,2**15)
def go(m):
    ct=leaves=0
    minimum=F(99)
    for S in gen({0},0,m):
        ct+=1
        d=S[-1].bit_length()
        if m==8 and S==tuple(range(8)):
            continue
        B=F(sum(sum(1-2*(x>>i&1) for x in S)**2 for i in range(d)),m*m)
        start=D>>20
        if m==8:
            start=D>>48
        W=hist(S,d)
        M=D**d
        lm=ln(m)[0]
        @lru_cache(None)
        def Hlow(a):
            vs=powers(d,a)
            total=0
            for v,freq in W.items():
                w=sum(i*j for i,j in zip(v,vs))
                total+=freq*w*ln(M,w)[0]
            return lm+total//(m*M)
        for a,b,lamb in ((start,D//4,F(7,5)),(D//4,end,F(11,10))):
            t=3+lamb*((1-F(8,m)) if m<22 else 1)
            T=t.numerator
            U=t.denominator
            assert d>=t
            if b==end:
                slack=d-B-t
                minimum=min(minimum,slack)
                assert (B+(F(2**d,m)-1)*rho**2)<(d-t)*(2-(1+rho)**d),(m,S,slack)
            if a==start:
                if m==8:
                    beta=F(sum((x^(1<<i)) not in S for x in S for i in range(d)),m)
                    c=beta*(1-F(d-1,2**48))
                    assert c>d-3 and c*(32-2)>(d-3)*33
                    assert ln(d)[1]<2*Q and 48*L2[0]>32*Q
                else:
                    assert U*lm>T*L2[1]+(d*U-T)*hb(start),(m,S)
            stack=[(a,b)]
            while stack:
                l,h=stack.pop()
                if U*Hlow(l)>T*L2[1]+(d*U-T)*hb(h):
                    leaves+=1
                    continue
                mid=(l+h)//2
                assert l<mid<h,(m,S,l,h)
                stack.extend(((l,mid),(mid,h)))
        Hlow.cache_clear()
    print(f'm={m:2} candidates={ct} intervals={leaves} high_slack={minimum}',flush=True)
for m in range(int(argv[1]) if len(argv)>1 else 3,(int(argv[2]) if len(argv)>2 else 22)+1):
    go(m)
