from math import comb
from functools import lru_cache
from itertools import combinations
def bc(x,y):
 return comb(x,y) if 0<=y<=x else 0
def w(k,l,A,B):
 return bc(k+l-1,l)*A+bc(k+l-1,k)*B
def sgn(n,b,u,v,k,l):
 assert k*u+l*v==n and min(u,v)>=3
 D=(u-1)*(v-1); A=u*(v-1); B=v*(u-1)
 z=D*w(k,l,A,B)
 for c in (b+1,b+2):
  for j in range(min(l,c//v)+1):
   i,r=divmod(c-j*v,u)
   if r==0 and i<=k:
    z-=w(i,j,A,B)*w(k-i,l-j,A,B)
 return z
def witness(n,b):
 for u in range(3,b+3):
  for j in [0,1,2]:
   v=(n%u)+u*j
   if v<3: continue
   k=(n-v)//u
   if k<1:continue
   if sgn(n,b,u,v,k,1)<0:return (u,v,k,1)
 for l in range(2,10):
  for u in range(3,b+3):
   for v in range(3,min(b+3,(n-u)//l)+1):
    k,r=divmod(n-v*l,u)
    if r or k<1: continue
    if sgn(n,b,u,v,k,l)<0:return(u,v,k,l)
 return None
if __name__=='__main__':
 import sys
 for b in range(12,int(sys.argv[1])+1,3):
  fail=[]; cnt=0
  for n in range(2*b+3,b*(b+1)):
   if n%(b+1)<=n//(b+1): continue
   cnt+=1
   if not witness(n,b):fail.append(n-b-3)
  print(b,cnt,len(fail),fail[:30],flush=True)
