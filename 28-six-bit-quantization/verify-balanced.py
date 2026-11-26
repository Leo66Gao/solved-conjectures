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
  if x<=last or x>=1<<n:continue
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
D=1<<100
end=D*(2**15-1)//2**16
rho=F(1,2**15)

n=int(argv[1]);m=1<<(n-6)
lo0=int(argv[2]) if len(argv)>2 else 0
hi0=int(argv[3]) if len(argv)>3 else (1<<30)
assert n in (10,11)
r=n-6
tested=leaves=0
for k,S in enumerate(gen({0},0,m)):
    if not lo0<=k<hi0:continue
    tested+=1
    if S==tuple(range(m)):continue
    d=S[-1].bit_length()
    t=r
    B=F(sum(sum(1-2*(x>>i&1) for x in S)**2 for i in range(d)),m*m)
    # Near p=1/2, use the strongest uniform Parseval cap that passes.
    rho=F(1,2**6)
    while not (2-(1+rho)**d>0 and (B+(F(2**d,m)-1)*rho**2)<(d-t)*(2-(1+rho)**d)):
        rho/=2
        assert rho>=F(1,2**18),(k,S)
    end=(D*(1-rho))//2
    # Near p=0: all shapes except the face have more boundary edges.
    k0=20
    beta=F(sum((x^(1<<i)) not in S for x in S for i in range(d)),m)
    while True:
        c=beta*(1-F(d-1,2**k0))
        L=F(k0*L2[0],Q)
        if c>d-t and c*(L-F(ln(d)[1],Q))>(d-t)*(L+1):
            break
        k0+=1
        assert k0<=80,(k,S)
    start=D>>k0
    W=hist(S,d);M=D**d;lm=ln(m)[0]
    @lru_cache(None)
    def Hlow(a):
        vs=powers(d,a)
        total=0
        for v,freq in W.items():
            w=sum(i*j for i,j in zip(v,vs))
            total+=freq*w*ln(M,w)[0]
        return lm+total//(m*M)
    stack=[(start,end)];count=0
    while stack:
        l,h=stack.pop()
        if Hlow(l)>t*L2[1]+(d-t)*hb(h):
            leaves+=1;count+=1;continue
        mid=(l+h)//2
        assert l<mid<h,(k,S,l,h)
        stack.extend(((l,mid),(mid,h)))
    print('shape',k,'intervals',count,'rho',rho,'low cutoff',k0,flush=True)
print('DONE',n,lo0,hi0,'shapes',tested,'intervals',leaves,flush=True)
