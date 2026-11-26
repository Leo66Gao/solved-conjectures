"""Exact scalar inequalities for the dimension-nine Fallat–Xing certificate."""
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import os
os.chdir(Path(__file__).resolve().parent)

def check(condition, reason):
    if not condition:
        raise RuntimeError(reason)

pairs=[(Q(a,b),Q(u,10**6)) for a,b,u in (map(int,line.split()) for line in open('points.tsv'))]
check(len(pairs)==9, 'wrong node count')
check(pairs[0][0]==Q(-9,10) and pairs[-1][0]==Q(199,200), 'wrong interval endpoints')
check(Q(1268,100)**2<161, 'left strict endpoint bound')
check(pairs[0][1]>0 and 161*pairs[0][1]**2<Q(787,5)**2, 'left tangent')
check(Q(27,25)+Q(1,44)<Q(10,9), 'near-one strict slope comparison')
check({Q(-3,7), Q(3,5)}.issubset({p[0] for p in pairs}), 'missing transition points')
for i,((a,U),(b,V)) in enumerate(zip(pairs,pairs[1:])):
    check(a<b and U>0 and V>0, 'bad node order or sign')
    m=(a+b)/2
    k=4 if m<Q(-3,7) else (3 if m<Q(3,5) else 2)
    X=k*m-(9-k)
    B=X*X+4*k*(9-k)
    for point, bound in [(a,U),(b,V)]:
        C=B+k*X*(point-m)
        check(C>0 and C*C>bound*bound*B, f'tangent test failed on interval {i}')
print('Exact scalar checks: all 16 interior tangent inequalities and the left/right boundary inequalities passed.',flush=True)
for args in [['left'],[],['0','9']]:
    subprocess.run(['./verify',*args],check=True)
