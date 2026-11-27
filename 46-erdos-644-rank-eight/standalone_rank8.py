"""Exact checker for f(8,7,2)=7. Python 3.10+; no solver, data file, or dependencies."""
from itertools import combinations,combinations_with_replacement,permutations
from collections import Counter
from time import monotonic
U=127
T=tuple(s for s in range(128) if s.bit_count()==3)
# E lists all point types of size >3; total excess above size 3 is four.
by={i:[s for s in range(128) if s.bit_count()==3+i] for i in range(1,5)}
def multis(e,k):
 if not k:yield ();return
 if e==0:return
 for h in range(k//e+1):
  for z in combinations_with_replacement(by[e],h):
   for q in multis(e-1,k-h*e):yield tuple(sorted(z+q))
P=[[sum(1<<p[i] for i in range(7) if s>>i&1) for s in range(128)] for p in permutations(range(7))]
todo=set(multis(4,4));nraw=len(todo);rep=[]
while todo:
 E=min(todo);rep.append(E)
 todo.difference_update(tuple(sorted(p[v] for v in E)) for p in P)
leaves=0;checked=0;skipped=0
def investigate(E):
 # A designated pair is absent from all seven original edges; its two spectra union to U.
 # 3+3<7, so at least one of those two spectra belongs to E.
 A=tuple(t for t in T if all(t&v for v in E))
 if not any(x|y==U for x in E for y in A+E if x!=y) and U not in E:return
 global checked;checked+=1
 D=tuple(7-sum(s>>j&1 for s in E) for j in range(7))
 def rec(ds,C,chosen):
  global leaves
  if not any(ds):
   R=chosen+E
   assert len(R)==15 and all(u&v for u,v in combinations(R,2))
   leaves+=1
   if not any(u|v==U for u,v in combinations(R,2)):return
   # Any XOR-zero triple of original rows makes simultaneous odd X-parity impossible.
   assert any(all(((U^v)&y).bit_count()%2==0 for v in R) for y in T),('counterexample',R)
   return
  rr=[j for j,d in enumerate(ds) if d]
  if any(not any(t>>j&1 for t in C) for j in rr):return
  # Complete all multiplicities of triples containing one selected row; then eliminate it.
  j=min(rr,key=lambda i:sum(t>>i&1 for t in C))
  inc=[t for t in C if t>>j&1];out=[t for t in C if not(t>>j&1)]
  def place(idx,k,r,used):
   if not k:
    nxt=tuple(t for t in out if all(t&v for v in used) and all(r[i] for i in range(7) if t>>i&1))
    rec(r,nxt,chosen+used);return
   for s in range(idx,len(inc)):
    v=inc[s]
    if all(r[i] for i in range(7) if v>>i&1): # all inc triples meet at j
     nr=tuple(r[i]-(v>>i&1) for i in range(7));place(s,k-1,nr,used+(v,))
  place(0,ds[j],ds,())
 rec(D,A,())
for E in rep:investigate(E)
H={h for h in range(1<<15) if h.bit_count()==8 and (h&255).bit_count()%2 and h&257!=257}
assert len(H)==2352
nine=[w for w in range(1<<15) if w.bit_count()==9]
assert len(nine)==5005 and all(any((w^(1<<i)) in H for i in range(15) if w>>i&1) for w in nine)
assert all(h & (32767^255) for h in H)
print('Exceptional multisets:',nraw,'S7-orbits:',len(rep),'orbits requiring recursion:',checked)
print('Completed regular spectrum configurations checked:',leaves)
print('Every bad configuration missing a pair has an XOR-zero triple.')
print('Construction:',len(H),'edges;',len(nine),'complements of six-sets verified; tau=7.')
