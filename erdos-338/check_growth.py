"""No external dependencies. Exact modular DP cross-checks, not an infinite proof."""
from collections import deque
from math import inf


def data(d):
    ps = [1] + [2**(2**(i-1)+i) for i in range(1,d+1)]
    P=ps[-1]
    C={P}
    for i in range(1,d+1):
        u=ps[i]//ps[i-1]
        C.update(k*(P//ps[i]) for k in range(1,u))
    return P, sorted(2*c for c in C)


def orders(d):
    P,E=data(d)
    m=8*P
    # A modular word must contain >=1 tail element. Variable final tail lifts all large n.
    # Ordinary modular shortest paths, initialized with a required tail letter.
    dist=[-1]*m
    dist[0]=dist[1]=1
    q=deque([0,1])
    edges=[1]+E
    while q:
        x=q.popleft()
        for e in edges:
            y=(x+e)%m
            if dist[y]==-1:
                dist[y]=dist[x]+1
                q.append(y)
    # Subset DP (0/1 per exception), then append as many tail ones as needed.
    # 0 mod m tail is allowed to be the required first tail.
    z=[inf]*m
    z[0]=z[1]=1
    for e in E:
        z=[min(z[i],z[(i-e)%m]+1) for i in range(m)]
    for i in range(2*m):
        j=i%m
        z[j]=min(z[j],z[j-1]+1)
    assert max(dist)==dist[-1]==d+4
    assert m-1-sum(E)>=P
    assert P<=z[-1]<=max(z)<=m
    return d+4,m,sum(E),max(dist),max(z),z[-1]


if __name__=='__main__':
    print('h M sum_exceptions ordinary restricted restricted_at_M-1')
    for d in range(1,5): print(*orders(d))
