"""Exact low-noise cell certificate for arbitrary ten-to-six maps. 
Combines with verify-balanced.py 10 for cells of size 16.
"""
from fractions import Fraction as F
from functools import lru_cache
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
@lru_cache(None)
def hb(a):return up(a*ln(D,a)[1]+(D-a)*ln(D,D-a)[1],D)

D=1<<60
low=D>>16
g=hb(low)
for m in range(1,45):
    if m==16:
        continue
    t=4+F(10,7)*((1-F(16,m)) if m<44 else 1)
    if t<=0:
        continue
    T=t.numerator;U=t.denominator
    assert U*ln(m)[0]>T*L2[1]+(10*U-T)*g,(m,t)
print("Exact size-only check for arbitrary ten-to-six maps succeeded on 0 <= p <= 2^-16; m=16 handled separately by the balanced certificate.")
