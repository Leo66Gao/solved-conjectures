"""Pure Python, exact, four mutually checked counting/generation paths. Run python3 verify.py."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import comb

def code(A):
    def root(v,p):
        return '(' + ''.join(sorted(root(w,v) for w in A[v] if w!=p)) + ')'
    return min(root(v,None) for v in range(len(A)))

def attach(trees):
    out={}
    for A in trees:
        n=len(A)
        for u in range(n):
            B=[x[:] for x in A]+[[u]]
            B[u].append(n)
            out.setdefault(code(B),B)
    return out

def spider(n,r):
    A=[[] for _ in range(n)]
    def edge(u,v): A[u].append(v); A[v].append(u)
    for j in range(r):
        edge(0,2*j+1);edge(2*j+1,2*j+2)
    for j in range(2*r+1,n): edge(0,j)
    return A

def brute(A):
    n=len(A)
    edges=[(1<<u)|(1<<v) for u in range(n) for v in A[u] if u<v]
    out=defaultdict(lambda:[0,0])
    for mask in range(1<<n):
        k=sum((mask & e)==e for e in edges)
        out[k][0]+=1;out[k][1]+=mask.bit_count()
    return dict(out)

def dp(A):
    # Inductively combine child subtrees, keeping root bit, edge count, and
    # both the number and total cardinality of all subsets with these data.
    def rec(u,p):
        d={(0,0):(1,0),(1,0):(1,1)}
        for v in A[u]:
            if v==p: continue
            b=rec(v,u); h=defaultdict(lambda:[0,0])
            for (i,s),(c,t) in d.items():
                for (j,z),(c2,t2) in b.items():
                    w=h[(i,s+z+i*j)]
                    w[0]+=c*c2; w[1]+=t*c2+c*t2
            d=h
        return d
    out=defaultdict(lambda:[0,0])
    for (_,k),(c,t) in rec(0,None).items():
        out[k][0]+=c;out[k][1]+=t
    return dict(out)

# A second independent generation: recursively list all multisets of rooted
# isomorphism classes whose orders sum to n-1, then forget the root.
def rooted(max_n):
    levels=[[],[()]]
    types=[(1,())]
    for n in range(2,max_n+1):
        def mul(rem,first):
            if not rem:
                yield ();return
            for i in range(first,len(types)):
                size,item=types[i]
                if size>rem: break
                for rest in mul(rem-size,i):
                    yield (item,)+rest
        level=list(mul(n-1,0))
        types.extend((n,t) for t in level);levels.append(level)
    return levels

def unroot(item):
    A=[]
    def add(t,p):
        v=len(A); A.append([])
        if p!=None: A[p].append(v);A[v].append(p)
        for ch in t: add(ch,v)
    add(item,None);return code(A)

def numerator_1(n):
    return Q(5*n-13+(n+1)*2**(n-4),2*n-5+2**(n-3))
def numerator_2(n):
    m=n-5
    return Q(n,2)+Q(2**m-2*m*m,6*2**m+4*m+4)

if __name__=='__main__':
    R=rooted(11);trees={'()':[[]]}
    print('n | tree count | highest mean (multiplicity) | highest mean excluding top shape (multiplicity)')
    for n in range(2,12):
        trees=attach(trees.values())
        assert set(trees)=={unroot(t) for t in R[n]}
        vals={}
        for key,A in trees.items():
            b=brute(A)
            assert b==dp(A)
            c,s=b[1]; vals[key]=Q(s,c)
            for k,(c,s) in b.items():
                if k==0 or n<2*k+1: continue
                U=Q(n+2*k-1,2)
                if key!=code(spider(n,k)):
                    assert Q(s,c)<=U-Q(1,3)
                    if n>=2*k+3 and key!=code(spider(n,k+1)):
                        assert Q(s,c)<=U-Q(1,2)
        if n>=4:
            v1=vals.pop(code(spider(n,1))); m1=sum(x==v1 for x in vals.values())+1
            v2=max(vals.values());m2=sum(x==v2 for x in vals.values())
            assert v1>=v2 and v1==numerator_1(n)
            if n>=5:
                assert v2==vals[code(spider(n,2))]==numerator_2(n)
                assert m2==1
            print(n,len(trees),f'{v1} ({m1})',f'{v2} ({m2})',sep=' | ')
    # Exponential estimates and exact checks on both hub polynomials in the proof.
    assert 18*Q(9,16)**16<Q(1,512) and Q(21*9,4*512)<Q(1,6)
    def trimprod(f,g,k):
        return [sum(f[i]*g[j-i] for i in range(max(0,j-len(g)+1),min(j,len(f)-1)+1)) for j in range(k+1)]
    for k in range(1,8):
        for r in (k,k+1):
            for n in range(2*r+1,2*r+22):
                m=n-2*r-1; f=[1]
                for j in range(r): f=trimprod(f,[2,1,1],k)
                for j in range(m): f=trimprod(f,[1,1],k)
                assert dp(spider(n,r))[k][0]==comb(r,k)*3**(r-k)*2**m+f[k]
    print('All checks passed.')
