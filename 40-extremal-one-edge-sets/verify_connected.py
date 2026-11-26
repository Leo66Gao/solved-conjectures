"""Additional checks for CONNECTED.md; pure Python."""
from math import comb
from fractions import Fraction as Q
from itertools import combinations,product
from verify import brute

def W(n,r,t):
    A=[[] for i in range(n)]
    def edge(i,j):
        A[i].append(j);A[j].append(i)
    for i in range(r):
        edge(0,2*i+1);edge(2*i+1,2*i+2)
        if i<t: edge(0,2*i+2)
    for i in range(2*r+1,n): edge(0,i)
    return A

def candidate(A,r):
    for w in range(len(A)):
        ends=[sum(v!=w for v in A[i]) for i in range(len(A)) if i!=w]
        if max(ends,default=0)<=1 and sum(ends)==2*r:return True
    return False

def mean(n,k,r,t):
    # Include sizes and edge totals; not just the univariate coefficients.
    m=n-2*r-1
    A=comb(r,k)*3**(r-k)*2**m
    L=Q(n+2*k-1,2)-Q(r-k,3)
    # Hub is selected, then insert leaves and pairs.
    D={0:(1,1)}
    def add(D,options):
        d={}
        for (i,(c,s)),(edge,bits) in product(D.items(),options):
            if i+edge>k:continue
            a,b=d.get(i+edge,(0,0));d[i+edge]=a+c,b+s+c*bits
        return d
    for j in range(m): D=add(D,[(0,0),(1,1)])
    for j in range(r):
        D=add(D,[(0,0),(1,1),(1,1),(3,2)] if j<t else [(0,0),(0,1),(1,1),(2,2)])
    c,s=D[k]
    return (A*L+s)/(A+c)

if __name__=='__main__':
    for n in range(2,7):
        es=list(combinations(range(n),2))
        c=0
        for mask in range(1<<len(es)):
            if mask.bit_count()<n-1: continue
            A=[[] for i in range(n)]
            for i,(u,v) in enumerate(es):
                if mask>>i&1: A[u].append(v);A[v].append(u)
            seen={0}; st=[0]
            while st:
                for v in A[st.pop()]:
                    if v not in seen: seen.add(v);st.append(v)
            if len(seen)<n:continue
            c+=1
            for k,(num,sz) in brute(A).items():
                if not k or n<=2*k:continue
                U=Q(n+2*k-1,2);a=Q(sz,num)
                assert a<=U
                if not candidate(A,k):
                    assert a<=U-Q(1,3)
                    if not candidate(A,k+1): assert a<=U-Q(1,2)
        print('n =',n,'connected labeled graphs =',c)
    samples=0
    for k in range(1,5):
        for r in (k,k+1):
            for t in range(r+1):
                for n in range(2*r+1,min(14,2*r+6)):
                    num,sz=brute(W(n,r,t))[k];assert Q(sz,num)==mean(n,k,r,t); samples+=1
    print('direct-subset and generating-function comparisons:',samples)
    for k in range(1,15):
        for n in (18*k+3,18*k+4,25*k+10):
            scores=[mean(n,k,r,t) for r in (k,k+1) for t in range(r,-1,-1)]
            assert all(x>y for x,y in zip(scores,scores[1:])) and scores[-1]>Q(n+2*k-2,2)
    print('Checked exact strict ordering of both groups for k=1..14 at three orders each.')
