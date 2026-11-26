import json
from math import prod
from math import isqrt
def nextprime(q):
 r=max(2,q+1)
 while any(r%d==0 for d in range(2,isqrt(r)+1)):r+=1
 return r
from functools import lru_cache
from pathlib import Path
orders=[e["order"] for e in json.load(open("extremizers.json")) if "weights" in e]
best=11539557639468829579
count=0
bestP=[]
def constraints(s):
 c=[]
 for t in range(7):
  b=1<<t
  rows=[x for x in s if x<2*b]
  low=[];high=[]
  for x,y in zip(rows,rows[1:]):
   if x<b<=y: low.append((x,y-b))
   if y<b<=x: high.append((y,x-b))
  c.append((set((x&~y,y&~x) for x,y in low),set((x&~y,y&~x) for x,y in high)))
 return c
Cs=[constraints(s) for s in orders]
# Run multiple initial caps; final successful pass then proves minimality.
def solve(cap):
 global count,best,bestP
 @lru_cache(maxsize=100000)
 def np(q):return int(nextprime(q))
 def dfs(t,p,d,cs):
  global count,best,bestP
  count+=1
  if t==7:
   if d[-1]<best:best=d[-1];bestP=list(p);print("improvement",best,bestP,flush=True)
   return
  limit=min(cap,best-1)
  low=max([p[-1] if p else 1]+[d[x]//d[y] for x,y in cs[t][0]])
  high=min([(limit//d[-1])]+[(d[x]-1)//d[y] for x,y in cs[t][1]])
  q=np(low)
  while q<=high and d[-1]*q**(7-t)<=min(cap,best-1):
   dfs(t+1,p+[q],d+[q*x for x in d],cs)
   if t==6:break
   q=np(q)
 for c in Cs:dfs(0,[],[1],c)
 print("bound",cap,"best",best,"calls",count,flush=True)
for cap in [10**7,10**8,10**9,10**10,10**11,10**12,10**13,10**14]:
 solve(cap)
 if best<=cap:break
