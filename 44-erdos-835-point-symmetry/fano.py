"""Tiny independent obstruction: cannot pack 5 Steiner triple systems on 7 points."""
from itertools import combinations
T=list(combinations(range(7),3));E=list(combinations(range(7),2))
m=[sum(1<<E.index(e) for e in combinations(t,2)) for t in T]
systems=[]
def gen(free,chosen):
 if not free:systems.append(chosen);return
 p=free&-free
 for i,t in enumerate(m):
  if p&t and t&free==t:gen(free^t,chosen|(1<<i))
gen((1<<21)-1,0)
disj=[(i,j)for i,a in enumerate(systems)for j,b in enumerate(systems[:i])if not a&b]
trips=[(i,j,k)for i,j in disj for k in range(j) if not systems[i]&systems[k] and not systems[j]&systems[k]]
print('Fano systems',len(systems),'disjoint pairs',len(disj),'disjoint triples',len(trips))
assert (len(systems),len(disj),len(trips))==(30,120,0)
