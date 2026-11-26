"""LP proposes realizations; certificates are verified independently by check.py."""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction
from math import lcm,gcd
def make(row):
 masks=[int(x) for x in row.split()[2:]]
 A=np.array([[((b>>i)&1)-((a>>i)&1) for i in range(7)] for a,b in zip(masks,masks[1:])],dtype=int)
 R=linprog(np.ones(7),A_ub=-A,b_ub=-np.ones(len(A)),bounds=[(None,None)]*7,method="highs")
 if R.success:
  v=[Fraction(float(x)).limit_denominator(100000) for x in R.x];d=lcm(*(x.denominator for x in v)); w=[int(x*d) for x in v]
  assert min(A@w)>0
  return dict(order=masks,weights=w)
 r=linprog(np.zeros(len(A)),A_eq=np.vstack((A.T,np.ones(len(A)))),b_eq=[0]*7+[1],bounds=(0,None))
 assert r.success
 v=[Fraction(float(x)).limit_denominator(100000) for x in r.x];d=lcm(*(x.denominator for x in v)); w=[int(x*d) for x in v]
 assert min(w)>=0 and max(w)>0 and all(q==0 for q in A.T@w)
 return dict(order=masks,dependence={i:w[i] for i in range(len(w)) if w[i]})
ls=[make(l) for l in Path('independent38.txt').read_text().splitlines() if l.startswith('leaf')]
print(len(ls),sum('weights' in e for e in ls));Path('extremizers.json').write_text(json.dumps(ls))
