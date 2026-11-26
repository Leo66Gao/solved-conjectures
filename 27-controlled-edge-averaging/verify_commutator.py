"""Exact checks for the two-ended argument in TRANSPORT.md, Leo Gao / AI-assisted."""
from fractions import Fraction as F
from random import Random
rng=Random(121727)
def upd(p,e):
    i,j,mu=e; q=p.copy();delta=mu*(p[i]-p[j]);q[i]-=delta;q[j]+=delta;return q
def prod(g,p,q):
    return sum(x*y*z for x,y,z in zip(g,p,q))
trials=128
for it in range(trials):
    D=rng.randrange(2,14); N=D+1; a=D//3;b=D-a;T=rng.randrange(25,65)
    edges=[]
    for _ in range(T):
        i=rng.randrange(D);edges.append((i,i+1,rng.choice([F(0),F(1,5),F(1,4),F(1,3),F(1,2)])))
    p=[[F(int(i==0)) for i in range(N)]]
    q=[None]*T+[[F(int(i==D)) for i in range(N)]]
    for e in edges:p.append(upd(p[-1],e))
    for s in reversed(range(T)):q[s]=upd(q[s+1],edges[s])
    g=[max(F(0),min(F(1),F(i-a,b-a))) for i in range(N)]
    for s,(i,j,mu) in enumerate(edges):
        dp=prod(g,p[s+1],q[s+1])-prod(g,p[s],q[s])
        rhs=mu*(g[i]-g[j])*(p[s][j]*q[s+1][i]-p[s][i]*q[s+1][j])
        assert dp==rhs
    assert p[-1][D]**2*(b-a)**2*(1+a)**3<=4*T
print(trials,'exact random forward/backward histories: each commutator and off-diagonal estimate verified')
