"""Independent exhaustive coset-character check for subgroups of order 16."""
from pgroup_screen import cocycles,mark,iso,orders,subs
from collections import defaultdict
def types16():
 groups=[((0,),)]
 for n in (2,4,8,16):
  recorded=defaultdict(list);fresh=[]
  for base in groups:
   for M in cocycles(base):
    s,g,w=mark(M);k=tuple(sorted(s))
    if any(iso(B,M,z) for B,z in recorded[k]):continue
    recorded[k].append((M,(s,g,w)));fresh.append(M)
  groups=fresh;assert len(groups)=={2:1,4:2,8:5,16:14}[n]
 return groups
def test(M):
 n=len(M);V=range(n);ss=subs(M);inverse=[M[x].index(0)for x in V]
 K=sorted([h for h in ss if len(h) in (2,4)],key=lambda h:(len(h),sorted(h)))
 square={M[x][x]for x in V}-{0}
 o={}
 for H in ss:
  z=n//len(H)
  f=tuple(sum(all(M[M[inverse[x]][k]][x] in H for k in h)for x in V)//len(H)for h in K)
  o[(z,f)]=H
 def actions(total,lo,hi,minorbit):
  opts=sorted(((z,f)for z,f in o if z>=minorbit and all(a<=b for a,b in zip(f,hi))),reverse=True)
  out=set()
  def add(i,rem,f):
   if rem==0:
    if all(l<=u for l,u in zip(lo,f)):out.add(f)
    return
   for j in range(i,len(opts)):
    z,df=opts[j]
    if z>rem:continue
    nf=tuple(x+y for x,y in zip(f,df))
    if all(a<=b for a,b in zip(nf,hi)):add(j,rem-z,nf)
  add(0,total,(0,)*len(K));return out
 possible=actions(32,[0]*len(K),[2 if len(h)==2 and max(h)not in square else 0 for h in K],8)
 both=0
 for f in possible:
  lo=[1 if len(h)>2 or f[i]==2 else(5 if max(h)in square else 3) for i,h in enumerate(K)]
  hi=[3 if len(h)>2 else (1 if f[i]==2 else(5 if max(h)in square else 7))for i,h in enumerate(K)]
  both+=len(actions(17,lo,hi,1))
 return len(possible),both
if __name__=='__main__':
 for i,M in enumerate(types16()):
  if max(orders(M))>4 or all(M[x][y]==M[y][x] for x in range(16)for y in range(16)):continue
  pt,both=test(M);print(i,'admissible point profiles',pt,'compatible color profiles',both)
  assert both==0
