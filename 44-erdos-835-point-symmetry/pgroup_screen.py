"""Enumerate small 2-groups by normalized central 2-cocycles, eliminating
isomorphic duplicates by testing explicit marked-generator images. Then test
necessary color characters for a regular order-32 action."""
from itertools import product
from collections import Counter,defaultdict
from functools import lru_cache
def piv_insert(P,x):
 while x:
  i=x.bit_length()-1
  if i not in P:P[i]=x;return True
  x^=P[i]
 return False
def cocycles(M):
 n=len(M); N=(n-1)**2
 def bit(a,b):return (1<<((a-1)*(n-1)+b-1)) if a and b else 0
 eq={}
 for a,b,c in product(range(1,n),repeat=3):
  piv_insert(eq,bit(a,b)^bit(M[a][b],c)^bit(b,c)^bit(a,M[b][c]))
 # First span the coboundaries, then obtain a complementary basis among cocycles.
 cob={}
 for h in range(1,n):
  v=0
  for a,b in product(range(1,n),repeat=2):
   if ((a==h)^(b==h)^(M[a][b]==h)):v^=bit(a,b)
  piv_insert(cob,v)
 basis=[]
 for j in range(N):
  if j in eq:continue
  v=1<<j
  for i,row in sorted(eq.items()):
   if (row&v).bit_count()&1:v|=1<<i
  if piv_insert(cob,v):basis.append(v)
 vecs=[0]
 for b in basis:vecs += [v^b for v in vecs]
 for v in vecs:
  yield tuple(tuple(M[a%n][b%n]+n*((a//n)^(b//n)^bool(v&bit(a%n,b%n))) for b in range(2*n)) for a in range(2*n))
def orders(M):
 n=len(M);out=[]
 for a in range(n):
  x=a;i=1
  while x:x=M[x][a];i+=1
  out.append(i)
 return out
def mark(M):
 n=len(M);ords=orders(M);sig=[(ords[x],sum(M[x][z]==M[z][x] for z in range(n)))for x in range(n)]
 seen={0};gens=[];walk=[]
 while len(seen)<n:
  # Bigger cyclic subgroups and smaller centralizers tend to reduce image tests
  a=max(set(range(n))-seen,key=lambda x:(ords[x],-sig[x][1]))
  gens.append(a);seen={0};todo=[0];walk=[]
  for x in todo:
   for j,g in enumerate(gens):
    y=M[x][g]
    if y not in seen:
     seen.add(y);todo.append(y);walk.append((x,j,y))
 return sig,gens,walk
def iso(m,M,cached):
 s,gs,walk=cached
 t=mark(M)[0];n=len(M);coords=range(n)
 for targets in product(*[[x for x in coords if t[x]==s[g]] for g in gs]):
  if len(set(targets))<len(gs):continue
  im=[-1]*n;im[0]=0;seen={0}
  for a,j,b in walk:
   u=M[im[a]][targets[j]]
   if u in seen or t[u]!=s[b]:break
   seen.add(u);im[b]=u
  else:
   if all(im[m[a][g]]==M[im[a]][targets[j]] for a in coords for j,g in enumerate(gs)):return True
 return False
def subgroup(M,H,g):
 gens=(*H,g)
 A={0};Q=[0]
 for x in Q:
  for y in gens:
   z=M[x][y]
   if z not in A:A.add(z);Q.append(z)
 return frozenset(A)
def subs(M):
 n=len(M);I=frozenset({0});out={I};Q=[I]
 for H in Q:
  for g in range(n):
   if g in H:continue
   K=subgroup(M,H,g)
   if K not in out:out.add(K);Q.append(K)
 return Q
def colors(M,ss):
 n=len(M);ords=orders(M)
 sq=set(M[i][i]for i in range(n))-{0}
 inv=[i for i in range(1,n)if ords[i]==2]
 lo=[5 if i in sq else 3 for i in inv];hi=[5 if i in sq else 7 for i in inv]
 inverse=[M[x].index(0) for x in range(n)]
 conj=[[M[M[inverse[t]][g]][t]for t in range(n)]for g in inv]
 opts={}
 for H in ss:
  z=n//len(H)
  if z>17:continue
  fx=tuple(sum(x in H for x in line)//len(H)for line in conj)
  if any(u>v for u,v in zip(fx,hi)):continue
  opts[z,fx]=H
 opts=sorted(opts.items(),reverse=True)
 @lru_cache(None)
 def rec(i,rem,fx):
  if not rem:return () if all(x<=y for x,y in zip(lo,fx))else None
  if any(xx+rem<ll for xx,ll in zip(fx,lo)):return None
  for j in range(i,len(opts)):
   (z,v),H=opts[j]
   if z>rem:continue
   nf=tuple(x+y for x,y in zip(v,fx))
   if any(x>h for x,h in zip(nf,hi)):continue
   out=rec(j,rem-z,nf)
   if out is not None:return (H,)+out
  return None
 return rec(0,17,(0,)*len(inv))
def main():
 groups=[((0,),)]
 for n in [2,4,8,16,32]:
  seen=defaultdict(list);fresh=[]
  for B in groups:
   for M in cocycles(B):
    s,g,w=mark(M);sg=tuple(sorted(s));L=seen[sg]
    if any(iso(m,M,v) for m,v in L):continue
    L.append((M,(s,g,w)));fresh.append(M)
  groups=fresh;print('order',n,'isomorphism types',len(groups),flush=True)
  assert len(groups)=={2:1,4:2,8:5,16:14,32:51}[n]
 if n!=32:return
 candidates=0;survive=0
 for i,M in enumerate(groups):
  o=orders(M)
  if max(o)>4:continue
  ss=subs(M)
  if any(len(H)==16 and all(M[x][y]==M[y][x]for x in H for y in H)for H in ss):continue
  candidates+=1
  Z=[x for x in range(32) if all(M[x][y]==M[y][x] for y in range(32))]
  sq=set(M[x][x] for x in range(32))-{0}
  print('candidate',i,'center',Z,'square set',sorted(sq),'sizes of abelian and normal data',flush=True)
  import json
  from pathlib import Path
  path=Path(__file__).resolve().parent/'group_tables'
  path.mkdir(exist_ok=True)
  (path/('candidate-%d.json'%i)).write_text(json.dumps(M,separators=(',',':'))+'\n')
  ans=colors(M,ss)
  if ans is not None:
   survive+=1;print('survive',i,'order distribution',sorted(Counter(o).items()),'stabilizers',list(map(sorted,ans)),flush=True)
 print('after abelian-order and exponent bounds:',candidates,'regular cases with feasible involution color counts:',survive)
if __name__=='__main__':main()
