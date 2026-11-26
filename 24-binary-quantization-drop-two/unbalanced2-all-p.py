"""Rigorous integer certificate for the affine cell bound, hence all unrestricted k=n-2.
Standard-library only. Optional args: inclusive first and last m, in [3,16].
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
  if x<=last:continue
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
def go(m):
 t=F(7,2)-(F(6,m) if m<16 else 0);T=t.numerator;U=t.denominator
 ct=leaves=0;minimum=F(10);high=F(1,2**15)
 for S in gen({0},0,m):
  ct+=1;d=S[-1].bit_length()
  if m==4 and S==(0,1,2,3):continue
  B=F(sum(sum(1-2*(x>>i&1) for x in S)**2 for i in range(d)),m*m)
  slack=d-B-t;minimum=min(minimum,slack)
  # Infinite interval up to rho=2^-15. P_A(y)*2^d has nonconstant Walsh energy 2^d/m-1.
  assert (B+(F(2**d,m)-1)*high**2)<(d-t)*(2-(1+high)**d),(m,S)
  # Low p: H(P_A)>=ln m. Exceptions have m=4,d=3; see note.
  start=D>>20
  if m==4:
   assert d==3 and S==(0,1,2,4)
   # beta=3-2(3/4)=3/2; ln3<1.1; L>=20 ln2>13.
   assert sum((x^(1<<i)) not in S for x in S for i in range(d))==6
   assert ln(3)[1]*10<11*Q and L2[0]*20>13*Q
   c=F(3,2)*(1-F(2,2**20))
   assert c>1 and c*(13-F(11,10))>14
  else:
   assert U*ln(m)[0]>T*L2[1]+(d*U-T)*hb(start),(m,S)
  W=hist(S,d); M=D**d; lm=ln(m)[0]
  @lru_cache(None)
  def Hlow(a):
   vs=powers(d,a);total=0
   for v,freq in W.items():
    w=sum(i*j for i,j in zip(v,vs));total+=freq*w*ln(M,w)[0]
   return lm+total//(m*M)
  stack=[(start,end)]
  while stack:
   l,h=stack.pop()
   if U*Hlow(l)>T*L2[1]+(d*U-T)*hb(h):leaves+=1;continue
   mid=(l+h)//2;assert l<mid<h,(m,S,l,h)
   stack.extend(((l,mid),(mid,h)))
  Hlow.cache_clear()
 print(f'm={m:2} candidates={ct} dyadic_intervals={leaves} min_high_noise_slack={minimum}',flush=True)
for m in range(int(argv[1]) if len(argv)>1 else 3,(int(argv[2]) if len(argv)>2 else 16)+1):go(m)
