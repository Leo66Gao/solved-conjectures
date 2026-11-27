"""Independent exact test of the alternating kernel and its quadratic refinement."""
from itertools import combinations
import random
rng=random.Random(230277)
def t(a):return a*(a-1)//2%2
def dot(x,y):return sum(i*j for i,j in zip(x,y))
def check(d,r,n):
 # spaces: o, beta, D followed by z=(p,m)
 C=[[0]*d for _ in range(d)]
 for i in range(d):
    for j in range(i,d):C[i][j]=C[j][i]=rng.randint(-4,4)
 H=[[int(i<r and j==i^1) for j in range(d)]for i in range(d)]
 B=[[2*C[i][j]+H[i][j] for j in range(d)]for i in range(d)]
 es=list(combinations(range(r),2)); en={e:j for j,e in enumerate(es)}
 a=[C[i][i]&1 for i in range(d)]+[int(j==i^1) for i,j in es]
 # Build upper triangular part of symmetric alternating form from its specification.
 dim=2+r+d+len(es); start=2+r
 up=[0]*dim
 def pair(i,j):
    assert i!=j
    i,j=sorted((i,j));up[i]^=1<<j
 pair(0,1)
 for i in range(r):pair(2+i,start+(i^1))
 for i in range(d):
    for j in range(i+1,d):
        if (C[i][j]+H[i][j])%2:pair(start+i,start+j)
 for e in es:
    e2=tuple(sorted(j^1 for j in e))
    if e<e2:pair(start+d+en[e],start+d+en[e2])
 for i,j in combinations(range(len(a)),2):
    if a[i] and a[j]:pair(start+i,start+j)
 lin=sum(t(C[i][i])<<(start+i) for i in range(d))+sum(int(j==i^1)<<(start+d+k) for k,(i,j) in enumerate(es))
 def ref(u):
    v=u;w=(u&lin).bit_count()
    while v:
        b=v&-v;v-=b;w+=(u&up[b.bit_length()-1]).bit_count()
    return w&1
 def feat(x):
    bx=[dot(row,x) for row in B];q=dot(x,bx)//2
    vec=[1,t(q)]+[t(x[i])^((q*x[i])&1) for i in range(r)]+[v&1 for v in x]+[x[i]*x[j]&1 for i,j in es]
    return sum(v<<i for i,v in enumerate(vec))
 pts=[tuple(rng.randrange(-6,7) for j in range(d)) for i in range(n)]
 data=[feat(x) for x in pts]
 assert ref(2)==0
 assert not any(map(ref,data))
 for i in range(n):
    for j in range(i+1,n):
        z=[a-b for a,b in zip(pts[i],pts[j])]
        val=t(dot(z,[dot(row,z) for row in B])//2)
        assert ref(data[i]^data[j])==val # R(x)=R(y)=0.
 print("d,r,n, tested evaluation pairs:",d,r,n,n*(n-1)//2)
check(4,4,32);check(7,4,40);check(23,22,50)
print("PASS: R(e_beta)=R(V(x))=0 and polar R(V(x),V(y))=t(Q(x-y)).")
