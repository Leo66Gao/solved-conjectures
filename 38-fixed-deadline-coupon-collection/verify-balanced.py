"""Reproduce every finite rational comparison used in the balanced theorem."""
from fractions import Fraction as F
from math import prod
def check():
 best=None; count=0
 for t in range(1,8):
  for r in range(2,36):
   q=t+r
   for i in range(64):
    l,h=F(i,64),F(i+1,64)
    def S(k,u):return sum((v-u)**(-k) for v in range(t+1,q+1))
    N=t+F(r,q)*min(l*(1-l),h*(1-h))
    d=F(r,q)*(1-2*h)
    low=N*(S(1,l)**2+S(2,l))+2*d*S(1,l if d>=0 else h)-F(2*r,q)
    assert low>0, (t,r,i,low)
    count+=1
    if best is None or low<best[0]:best=(low,t,r,i)
 print(f"All {count} rational derivative enclosures strictly positive; minimum {best[0]}, at (t,r,i)={best[1:]}.")
def fall(v,r): return prod(v-j for j in range(r))
def b(q,r,y):
 if not r:return F(1)
 j=int(y);u=y-j
 if u==0:return F(fall(j,r),fall(q,r))
 return (F(fall(j,r-1),fall(q-u,r))*
         (j-r+1+F(r,q)*u*(q-u-j)))
def identities():
 total=end=cx=0
 for q in range(2,12):
  for r in range(1,q+1):
   vals=[b(q,r,F(k,7)) for k in range(7*q+1)]
   for k in range(len(vals)-2):
    assert vals[k]+vals[k+2]>=2*vals[k+1];cx+=1
   for k in range(len(vals)-1):
    y=F(k,7)
    if y<=q-1:
     assert (q-y)*(b(q,r,y+1)-b(q,r,y))==r*(b(q,r-1,y)-b(q,r,y))
     total+=1
    else:
     assert 1+(r-1)*b(q,r,y)<=r*b(q,r-1,y);end+=1
 print(f"Additional exact grid sanity checks: {total} recurrence, {end} shortened-jump and {cx} convexity comparisons.")
if __name__=='__main__':check();identities()
