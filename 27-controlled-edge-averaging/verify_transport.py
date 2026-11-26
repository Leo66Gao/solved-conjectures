"""Private check for Leo Gao; developed with OpenAI AI assistance.
Exact fractions, no external packages. Exhaustive limited histories, not a proof."""
from fractions import Fraction as F
from collections import deque
def check(N, edges, T):
    d=[N]*N;d[0]=0;q=deque([0]);ne=[[] for x in d]
    for i,j in edges:ne[i].append(j);ne[j].append(i)
    while q:
        i=q.popleft()
        for j in ne[i]:
            if d[j]>d[i]+1:d[j]=d[i]+1;q.append(j)
    p=[F(0)]*N;p[0]=F(1); states={tuple(p)}
    count=0
    for t in range(T+1):
        for p in states:
            assert sum(p)==1 and all(p[i]*(d[i]+1)<=1 for i in range(N))
            for R in range(max(d)+1):
                excess=sum(p[i]*max(0,d[i]-R) for i in range(N))
                assert excess**2*(R+1)<=t
        count+=len(states)
        if t==T:break
        nx=set()
        for p in states:
            for i,j in edges:
                for mu in (F(0),F(1,4),F(1,2)):
                    a=list(p);x=mu*(a[i]-a[j]);a[i]-=x;a[j]+=x;nx.add(tuple(a))
        states=nx
    return count
for (k,edges,t) in [(5,[(0,1),(1,2),(2,3),(3,4)],7),(5,[(0,1),(1,2),(2,0),(2,3),(3,4)],7),(5,[(0,1),(0,2),(0,3),(0,4)],6)]:
    print(k,edges,t,check(k,edges,t),'exact state/time pairs validated')
