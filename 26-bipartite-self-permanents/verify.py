"""Pure integer reconstruction of the row certificate, no third-party modules."""
from math import comb
from collections import defaultdict
def add(*P):
 out=defaultdict(int)
 for p in P:
  for a,b in p.items(): out[a]+=b
 return {a:b for a,b in out.items() if b}
def mul(P,Q):
 out=defaultdict(int)
 for (i,j),p in P.items():
  for (k,l),q in Q.items():out[i+k,j+l]+=p*q
 return {a:b for a,b in out.items() if b}
def scale(P,c):return {a:b*c for a,b in P.items()}
one={(0,0):1}; a=add(one,{(2,1):1});b={(1,0):1,(2,1):-1}
A=add(mul(a,a),mul(b,b));y=add(A,scale(one,-1))
sa={(i,j):i*v for (i,j),v in A.items() if i}
d=add(mul(sa,sa),scale(mul(A,mul(y,y)),-1))
assert min(i for i,j in d)>=4
d={(i-4,j):v for (i,j),v in d.items()}
assert max(i for i,j in d)==8 and max(j for i,j in d)==6
T=[[sum(v*comb(8-k,i-k)*comb(6-l,j-l) for (k,l),v in d.items()
        if i>=k and j>=l) for j in range(7)] for i in range(9)]
expected=[[3,30,117,228,237,126,27],[24,220,796,1464,1456,748,156],
 [83,688,2299,4024,3913,2008,425],[162,1194,3684,6260,6186,3330,752],
 [195,1250,3587,6100,6389,3746,925],[148,800,2180,3840,4412,2912,812],
 [69,300,813,1520,1971,1524,491],[18,58,172,340,514,490,184],
 [2,4,16,32,58,76,28]]
assert T==expected and min(map(min,T))>0
for r in T:print(*r)
print("PASS: all 63 transformed integer coefficients agree with the paper and are positive.")
