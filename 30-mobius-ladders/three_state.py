"""
Exact homogeneous coefficient certificate for the 10-vertex ladder on regular
three equal-block graphons. Standard library only; Python 3.
"""
from collections import defaultdict,Counter
from itertools import product
from math import factorial
Z=(0,0,0,0)
T=lambda i:tuple(int(i==j) for j in range(4))
def times(f,g):
    h=defaultdict(int)
    for m,c in f.items():
      for n,d in g.items():h[tuple(a+b for a,b in zip(m,n))]+=c*d
    return {m:c for m,c in h.items() if c}
def tensor(A):
 b={}
 for i,j,k in product(range(3),repeat=3):
    F=defaultdict(int)
    for l in range(3):
       p=times(times(A[i][l],A[j][l]),A[k][l])
       for m,c in p.items():F[m]+=c
    b[i,j,k]=dict(F)
 return b
def count(vertices):
 M=[]
 for x,y,z in vertices: 
    M.append([[6-x-y,x,y],[x,6-x-z,z],[y,z,6-y-z]])
 A=[[{T(a):M[a][i][j] for a in range(4) if M[a][i][j]} for j in range(3)] for i in range(3)]
 b=tensor(A)
 t=defaultdict(int)
 for I in product(range(3),repeat=5):
   f={Z:1}
   for i in range(5):
      f=times(f,b[I[i-1],I[i],I[(i+1)%5]])
   for m,c in f.items():t[m]+=c
 for a in range(16):
    for b in range(16-a):
       for c in range(16-a-b):
          d=15-a-b-c; m=a,b,c,d
          t[m]-=2**15*3**10*factorial(15)//(factorial(a)*factorial(b)*factorial(c)*factorial(d))
 return dict(t)
if __name__=='__main__':
 for x in [0,3]:
    t=count([(2,2,2),(x,x,x),(0,3,3),(0,0,6)])
    signs=Counter((c>0)-(c<0) for c in t.values())
    assert signs=={1:790,0:26}, signs
    assert t[15,0,0,0]==0
    assert all(t[tuple(15*e for e in T(i))]>0 for i in (1,2,3))
    print("simplex", x, "strictly positive coefficients:", signs[1],
          "zero:", signs[0], "negative:", signs[-1])
