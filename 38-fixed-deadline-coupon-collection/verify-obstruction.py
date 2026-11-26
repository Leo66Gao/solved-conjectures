from importlib.machinery import SourceFileLoader
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
B=SourceFileLoader('balanced',str(Path(__file__).with_name('verify-balanced.py'))).load_module().b
law={3:F(191,768)}
for a in (2,5):
 for i,j in combinations(range(a,a+3),2):law[(1<<i)|(1<<j)]=F(577,4608)
assert sum(law.values())==1
p=[sum(w for A,w in law.items() if (A>>i)&1) for i in range(8)]
out=F()
for A,w in law.items():
 for C,v in law.items():
  D=A|C;y=F(D.bit_count(),2)
  drift=sum(p[i]-F(1,4) for i in range(8) if not D&(1<<i))/2
  out+=w*v*(B(4,2,y+1)-B(4,2,y))*drift
assert out==F(2854979,856141332480)
print(out)
