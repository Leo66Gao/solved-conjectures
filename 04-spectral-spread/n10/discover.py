"""Numerical search for witnesses used by the separate exact checker."""
import math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
N=10
SCALE=1000000
IDX=np.arange(1<<(2*N-1))
I,J=np.indices((N,N))
D=np.column_stack((np.ones(len(IDX),dtype=np.int8),1-2*((IDX[:,None]>>np.arange(N-1))&1))).astype(np.int8)
E=(1-2*((IDX[:,None]>>(N-1+np.arange(N)))&1)).astype(np.int8)
H=(1-D[:,:,None]*D[:,None,:]*E[:,np.minimum(I,J)])//2
di=H[:, np.arange(N), np.arange(N)]
f=H[np.arange(len(IDX)),di.argmax(axis=1),:]
g=di-f
canon=(H==di[:,:,None]*di[:,None,:]).all(axis=(1,2))
k1=f.sum(axis=1); k2=g.sum(axis=1)
intr=(di.sum(axis=1)>0)&((k1==k2)|((k1*k2==6)&(k1+k2==5)))&(H==f[:,:,None]*f[:,None,:]+g[:,:,None]*g[:,None,:]).all(axis=(1,2))
sel=~(canon|intr)
H=H[sel]
cache={}
def solve(a):
 if a in cache: return cache[a]
 e=np.linalg.eigvalsh(1-float(1-a)*H)
 lo,hi=e[:,0],e[:,-1]
 U=math.ceil(SCALE*max(hi-lo))+4
 L=np.rint((SCALE*(lo+hi)-U)/2).astype(np.int32)
 cache[a]=(U,L)
 print(a,U,flush=True)
 return cache[a]
def tangent_pass(a,b,k):
 m=(a+b)/2
 B=(k*m-(N-k))**2+4*k*(N-k)
 for x in [a,b]:
  U=F(solve(x)[0],SCALE)
  C=B+k*(k*m-(N-k))*(x-m)
  if C<=0 or C*C<=U*U*B: return False
 return True
def subdiv(a,b,k):
 if tangent_pass(a,b,k): return [(a,b,k)]
 m=(a+b)/2
 return subdiv(a,m,k)+subdiv(m,b,k)
zs=[F(-9,10),F(-7,9),F(-1,7),F(199,200)]
intervals=sum((subdiv(a,b,k) for a,b,k in zip(zs,zs[1:],(5,4,3))),[])
nodes=sorted({t for i in intervals for t in i[:2]})
D=Path(__file__).parent
with (D/'points.tsv').open('w') as f:
 for a in nodes: f.write(f'{a.numerator} {a.denominator} {solve(a)[0]}\n')
for j,a in enumerate(nodes): solve(a)[1].astype('<i4').tofile(D/f'lower{j:03d}.bin')
print('done',len(nodes),len(intervals))

# At a=-1, signatures do not change eigenvalues. Keep only eps masks
# with at least two sign changes; the other sign matrices are analytic.
left=[i for i in range(1<<N) if ((i^(i>>1))&((1<<(N-1))-1)).bit_count()>=2]
E0=1-2*((np.array(left)[:,None]>>np.arange(N))&1)
e0=np.linalg.eigvalsh(E0[:,np.minimum(I,J)])
leftU=14140000
np.rint((SCALE*(e0[:,0]+e0[:,-1])-leftU)/2).astype('<i4').tofile(D/'left.bin')
