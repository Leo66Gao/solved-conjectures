"""Pure-Python check using a single residue-field witness for both real embeddings."""
from collections import Counter
from itertools import combinations
from math import prod
def coords(r):
 return [(0,0),(-2*r,4),(3-r,r+5),(6,0),(3-r,-r-1),(3,3),(r+6,r+4),(-2*r-3,1)]
# x,y represent (x,sqrt(3)y); squared lengths are 36 times the base-unit squared lengths.
def sizes(r):return [72,108+24*r,180+72*r,72+24*r,36,108+36*r,36+12*r]
w='1255567726765637767546434743';assert sorted(Counter(w).values())==list(range(1,8))
def pair(x,y):return (x[0]-y[0])**2+3*(x[1]-y[1])**2
# Exact integral quadratic polynomial identity modulo X²-6.
for (a,b),k in zip(combinations(range(8),2),map(int,w)):
 def e(x):return pair(coords(x)[a],coords(x)[b])-sizes(x)[k-1]
 c=e(0);v=(e(1)-e(-1))//2;u=e(1)-c-v
 assert v==0 and 6*u+c==0
def det(a):
 if len(a)==1:return a[0][0]
 return sum((-1)**j*v*det([r[:j]+r[j+1:] for r in a[1:]]) for j,v in enumerate(a[0]))
def certificate(p,r):
 assert r*r%p==6%p
 E=coords(r); norm=lambda u:u[0]**2+3*u[1]**2
 A=prod(det([[1,x,y] for x,y in z])%p for z in combinations(E,3))%p
 B=prod(det([[1,x,y,norm((x,y))] for x,y in z])%p for z in combinations(E,4))%p
 C=prod((x-y)%p for x,y in combinations(sizes(r),2))%p
 return A,B,C
# Which subconfigurations are themselves crescents? General position is hereditary.
def subset_crescents(k):
 d=dict(zip(combinations(range(8),2),w))
 return [s for s in combinations(range(8),k) if sorted(Counter(d[e] for e in combinations(s,2)).values())==list(range(1,k))]
assert [len(subset_crescents(k)) for k in range(3,8)]==[8,3,1,0,1]
assert subset_crescents(7)==[tuple(range(1,8))]
if __name__=='__main__':
 for p in range(7,2000):
  if any(p%i==0 for i in range(2,int(p**0.5)+1)):continue
  for r in range(p):
   if r*r%p!=6:continue
   a=certificate(p,r)
   if all(a):
    print('prime',p,'root',r,'products for triples, quadruples, distinct labels:',a);exit()
