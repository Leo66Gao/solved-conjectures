"""Small independent exact tests (all permanents via direct permutation enumeration)."""
from math import factorial
from fractions import Fraction as F
from itertools import combinations as cb,permutations as pm
def per(a):return sum((prod(a[i][j] for i,j in enumerate(u)) for u in pm(range(len(a)))),F(0))
def prod(a):
 p=1
 for t in a:p*=t
 return p
def block(X):
 m,n=len(X),len(X[0])
 return [[F(i==j) if (i<m)==(j<m) else (X[i][j-m] if i<m else X[j][i-m]) for j in range(m+n)] for i in range(m+n)]
def sq(X):return [[a*a for a in r] for r in X]
def inspect(X):
 r,c=len(X),len(X[0])
 P,Q=per(block(X)),per(block(sq(X)))
 assert Q<=P
 W=sq(X);G=[[sum(a*b for a,b in zip(x,y)) for y in W] for x in W]
 S=prod((1+sum(a*a for a in x))**2+(sum(x)-sum(a*a for a in x))**2 for x in W)
 U=per([[x+int(i==j) for j,x in enumerate(row)] for i,row in enumerate(G)])
 assert Q**2<=U**2<=S
 # Independent sector formula via minor permanents
 T=sum(per([[X[i][j] for j in J] for i in I])**2 for k in range(min(r,c)+1)
     for I in cb(range(r),k) for J in cb(range(c),k))
 assert T==P
 return P,Q
def ft(a):return [[F(x) for x in row] for row in a]
sets=[ft([[1,0],[0,1]]),[[F(3,5),F(4,5)],[-F(4,5),F(3,5)]]]
H=ft([[1,1,1,1],[1,-1,1,-1],[1,1,-1,-1],[1,-1,-1,1]])
for k,l in [(2,3),(3,3),(4,3),(4,4)]:
 sets.append([[x/2 for x in row[:l]] for row in H[:k]])
for X in sets:
 a,b=inspect(X);print(len(X),len(X[0]),'P=',a,'Q=',b, 'PASS')
