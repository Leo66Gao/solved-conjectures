"""Independently checks prime witnesses, LP certificates and their completeness against C++ output (Python standard library)."""
from math import gcd,prod,isqrt
from pathlib import Path
import json
def prime(q):return q>=2 and all(q%d for d in range(2,isqrt(q)+1))
def score(p):
 assert len(set(p))==len(p) and all(prime(q) for q in p)
 div=[1]
 for q in p:div=div+[d*q for d in div]
 div.sort();return sum(gcd(x,y)==1 for x,y in zip(div,div[1:]))
ps=[[2],[2,3],[2,3,5],[2,3,5,7],[2,5,7,11,19],[3,5,13,19,29,41],[3,7,11,47,113,191,277]]
for primes,mx in zip(ps,(1,2,4,7,13,22,38)):
 assert score(primes)==mx;print(len(primes),prod(primes),mx)
certs=json.loads(Path("extremizers.json").read_text());possible=0
leaves={tuple(map(int,l.split()[2:])) for l in Path("independent38.txt").read_text().splitlines() if l.startswith("leaf 38 ")}
assert len(leaves)==len(certs)==96
for c in certs:
 s=c["order"];leaves.remove(tuple(s));assert set(s)==set(range(128))
 A=[[((b>>i)&1)-((a>>i)&1) for i in range(7)] for a,b in zip(s,s[1:])]
 if "weights" in c:
  w=c["weights"];assert all(x>0 for x in w) and all(sum(a*b for a,b in zip(row,w))>0 for row in A);possible+=1
 else:
  d={int(i):v for i,v in c["dependence"].items()}
  assert len(d)>0 and all(v>0 for v in d.values())
  assert all(sum(v*A[i][j] for i,v in d.items())==0 for j in range(7))
assert not leaves and possible==44
print("All 96 certified: 44 realizable and 52 nonrealizable.")
