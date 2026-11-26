"""Inspect five-/six-string site partition patterns for the trifferent-fusion lemma.
Exact combinatorial analysis. (Not by itself a block-positivity verifier.)
"""
import itertools as it
import sys
from functools import cache
from collections import Counter, defaultdict
from math import comb
from fractions import Fraction
from pathlib import Path

def normalize(P):
    lookup={}
    return tuple(lookup.setdefault(x,len(lookup)) for x in P)

def partitions(m):
    if not m:yield ()
    else:
        for X in partitions(m-1):
            for v in range(max(X,default=-1)+2):
                yield X+(v,)

def xor(xs):
    x=0
    for y in xs:x^=y
    return x

def run(m,d, upto=None, t=Fraction(1,2), from_t_cli=False):
    r=t/(1-t)
    costs={(g,h):2*r**g*(1-t)**h for h in range(1,comb(m-1,2)+1) for g in range(1,h+1)}
    pairs=list(it.combinations(range(1,m),2))
    P=sorted(X for X in partitions(m) if 3<=len(set(X))<=m)
    Pidx={X:i for i,X in enumerate(P)}
    B=[sum(1<<k for k,(j,l) in enumerate(pairs) if len({X[0],X[j],X[l]})==3) for X in P]
    Br={y:i for i,y in enumerate(B)}
    assert len(Br)==len(B)
    triples=list(it.combinations(range(m),3)); pp=list(it.combinations(range(m),2))
    T=[sum(1<<i for i,A in enumerate(triples) if len({X[j] for j in A})==3) for X in P]
    E=[sum(1<<i for i,(a,b) in enumerate(pp) if X[a]!=X[b]) for X in P]
    Tbits=list(range(len(triples)))

    maps=[tuple(1<<Pidx[normalize(X[i] for i in s)] for X in P) for s in it.permutations(range(m))]

    def bits(mask):
        while mask:
            b=mask&-mask;mask-=b;yield b.bit_length()-1
    @cache
    def canon(Z):
        k=tuple(bits(Z))
        return min(sum(p[i] for i in k) for p in maps)
    @cache
    def trifferent(Z):
        e=t=0
        for i in bits(Z):e|=E[i];t|=T[i]
        for j,(a,b,c) in enumerate(triples):
            if not t>>j&1:
                if all(e>>pp.index(q)&1 for q in ((a,b),(a,c),(b,c))):return False
        return True
    def psd(A):
        # Exact LDL with simultaneous symmetric pivoting and zero-pivot handling.
        A=[list(x) for x in A]
        while A:
            if any(A[i][i]<0 for i in range(len(A))):return False
            i=next((j for j in range(len(A)) if A[j][j]>0),None)
            if i is None:return not any(any(row) for row in A)
            R=[j for j in range(len(A)) if j!=i]
            A=[[A[j][k]-A[j][i]*A[i][k]/A[i][i] for k in R] for j in R]
        return True

    @cache
    def fusion_psd(Z,Q):
        if r==1:return True
        D=[[sum(P[i][x]!=P[i][z] for i in bits(Z))-(P[Q][x]!=P[Q][z])
            for z in range(m)] for x in range(m)]
        assert all(a>=0 for row in D for a in row)
        return psd([[r**a for a in row] for row in D])

    @cache
    def charges(Z):
        W=list(zip(*(P[i] for i in bits(Z)))) if Z else [()]*m
        W=list(dict.fromkeys(W)); n=Z.bit_count()
        if len(W)<=2:return True
        S=[0]*(len(W)**2)
        for x,z in it.product(range(len(W)),repeat=2):
            S[x*len(W)+z]=sum(1<<i for i in range(n) if W[x][i]!=W[z][i])
        for x in range(len(W)):
            D=S[x*len(W):(x+1)*len(W)]
            for p in range(1,1<<n):
                pool=[]
                for z,delta in enumerate(D):
                    if not delta or delta & p !=delta: continue
                    o=p^delta
                    G=[u for u,ed in enumerate(D) if not (ed&o)]
                    if len(G)<3:continue
                    if not any(sum(len({W[v][i] for v in L})==3 for i in range(n))%2 for L in it.combinations(G,3)):continue
                    if any(not D[u]&p for u in range(len(W)) if u!=x):return False
                    g=min(S[a*len(W)+b].bit_count() for a,b in it.combinations(G,2))
                    pool.append((z,costs[g,delta.bit_count()]))
                for j in range(1,len(pool)+1):
                    for PZ in it.combinations(pool,j):
                        if sum(cost for z,cost in PZ)<=1:continue
                        if any(len({W[z][i] for z,cost in PZ if W[z][i]!=W[x][i]})>1 for i in range(n)):continue
                        return False
        return True

    @cache
    def reduction(Z):
        c=Z.bit_count()
        if c<=3 or trifferent(Z) or charges(Z):return 3
        S=Z
        while S:
            if S.bit_count()>=2:
                b=xor(B[i] for i in bits(S))
                if b==0: return reduction(canon(Z^S))
                if b in Br and trifferent(S) and fusion_psd(S,Br[b]):
                    bit=1<<Br[b]
                    if bit & (Z^S): ans=reduction(canon((Z^S)^bit))
                    else: ans=reduction(canon((Z^S)|bit))
                    if ans<=3:return 3
            S=(S-1)&Z
        return c

    Xs={0};D=comb(m-1,2); core=[]
    print('t=',t, 'words=',m, 'input maximum alphabet=',d, 'columns<=',min(upto or D,D),flush=True)
    for n in range(1,min(upto or D,D)+1):
        Ys=set()
        for X in sorted(Xs):
            Ts={0}
            for i in bits(X):Ts|={x^B[i] for x in Ts}
            for i in (j for j,p in enumerate(P) if len(set(p))<=d):
                if B[i] in Ts:continue
                Ys.add(canon(X|(1<<i)))
        Xs=Ys
        bad=[Z for Z in Xs if reduction(Z)>3]
        print(m,d,n,len(Xs),len(bad),flush=True)
        if bad:
            if m==5 and d==5 and n==4 and t==Fraction(1,2):
                assert len(bad)==18 and all(all(len(set(P[i]))==3 for i in bits(Z)) for Z in bad)
            print('max levels and first core:',max(max(len(set(P[i])) for i in bits(Z)) for Z in bad),[P[i] for i in bits(min(bad))],flush=True)
            core.extend(tuple(''.join(map(str,x)) for x in zip(*(P[i] for i in bits(Z)))) for Z in sorted(bad))
    if m==5 and d==5 and upto is None:
        if t==Fraction(1,2):assert len(core)==18
        for w in core: print(' '.join(w))
    return Xs,core

if __name__=='__main__':
    m,d=map(int,sys.argv[1:3]); t=Fraction(sys.argv[3]) if len(sys.argv)>=4 else Fraction(1,2)
    upto=int(sys.argv[4]) if len(sys.argv)>=5 else None
    run(m,d,upto,t)
