#!/usr/bin/env python3
"""Small exact checks of the proof, not an asymptotic certificate."""
from itertools import combinations
from functools import lru_cache

def parity(x): return x.bit_count() & 1
def dot(a,x): return parity(a&x)

def translate(f, h, n):
    return sum(((f>>(x^h))&1)<<x for x in range(1<<n))

def table(f,n): return tuple((f>>x)&1 for x in range(1<<n))
def truth(p): return sum(b<<i for i,b in enumerate(p))
def polars(p):
    m=len(p)
    return [[p[x^y]^p[x]^p[y]^p[0] for y in range(m)] for x in range(m)]
def essential(p):
    m=len(p)
    per=[h for h in range(m) if all(p[x]==p[x^h] for x in range(m))]
    return {a for a in range(m) if not any(dot(a,h) for h in per)}
def rank_polar(p):
    m=len(p)
    rad=sum(all(p[x^h]^p[x]^p[h]^p[0]==0 for x in range(m)) for h in range(m))
    assert rad and (rad&(rad-1))==0
    return (m.bit_length()-rad.bit_length())

def monomials(n,skip=-1):
    variables=[i for i in range(n) if i!=skip]
    return [()] + [(i,) for i in variables] + list(combinations(variables,2))
def choices(n,skip=-1):
    terms=monomials(n,skip)
    masks=[truth([int(all((x>>i)&1 for i in term)) for x in range(1<<n)]) for term in terms]
    val=[0]
    for z in masks: val+= [f^z for f in val]
    return val

def check_rank_and_slices(n):
    total=above=slices=0
    for f in choices(n):
        total+=1; p=table(f,n); r=rank_polar(p)
        assert r%2==0
        d=2*sum(p)-(1<<n)
        if not d: continue
        E=essential(p)
        assert len(E)==(1<<r)
        assert abs(d)==(1<<(n-r//2))
        if d<0: continue
        above+=1
        for ell in E-{0}:
            # Parametrize each fiber affinely by deleting a pivot variable.
            pivot=(ell&-ell).bit_length()-1
            for b in (0,1):
                q=[]
                for y in range(1<<(n-1)):
                    x=(y & ((1<<pivot)-1))| ((y>>pivot)<<(pivot+1))
                    x^=(b^dot(ell,x))<<pivot
                    assert dot(ell,x)==b
                    q.append(p[x])
                assert rank_polar(q)==r-2
                slices+=1
    return total,above,slices

def pairs_and_witness(n):
    C=[choices(n,i) for i in range(n)]
    high=[[f for f in c if f.bit_count()>(1<<(n-1))] for c in C]
    E={f:essential(table(f,n)) for c in high for f in c}
    @lru_cache(None)
    def opp(f,j): return f&translate(f,1<<j,n)
    pairs=fs=0
    for i,j in combinations(range(n),2):
        for f in high[i]:
            for g in high[j]:
                pairs+=1
                if opp(f,j)&opp(g,i): continue
                fs+=1
                assert bool((E[f]&E[g])-{0})
                mask=(1<<(1<<n))-1
                assert not (opp(f^mask,j)&opp(g^mask,i))
                corr=(1<<n)-2*(f^g).bit_count()
                W=mask & ~(f^translate(f,1<<j,n)) & ~(g^translate(g,1<<i,n))
                assert corr==-W.bit_count()
    def visit(ls):
        i=len(ls)
        if i==n: return ls
        for f in high[i]:
            if f.bit_count()!=3*(1<<(n-2)): continue
            if all(not (opp(g,i)&opp(f,j)) for j,g in enumerate(ls)):
                h=visit(ls+[f])
                if h: return h
        return None
    w=visit([]); assert w
    assert sum(f.bit_count() for f in w)//2==24
    # Independent explicit square scan, rather than intersected truth tables.
    assert all(not(all((w[k]>>v)&1 for v,k in [(x,i),(x,j),(x^(1<<j),i),(x^(1<<i),j)]))
               for x in range(1<<n) for i,j in combinations(range(n),2))
    return pairs,fs,[hex(f) for f in w]

if __name__=="__main__":
    print("Q4 quadratic polynomials, above-half, restricted fibers:",check_rank_and_slices(4))
    print("Q4 high-direction pairs, compatible pairs, Q4 24-edge witness tables:",pairs_and_witness(4))

    mask=(1<<32)-1
    def cubic(x):
        a,b,s,v,w=[(x>>k)&1 for k in range(5)]
        h=(1^v)&(1^w)
        return (1^s^(s&b)^((1^s)&h),s^((1^s)&a)^(h&a))
    f,g=(truth([cubic(x)[k] for x in range(32)]) for k in range(2))
    assert f.bit_count()==g.bit_count()==20
    assert not(f&translate(f,2,5)&g&translate(g,1,5))
    none=mask&~f&~translate(f,2,5)&~g&~translate(g,1,5)
    assert none.bit_count()==4
    print("Q5 cubic boundary: fractions 20/32 and 20/32; no retained square; 1 empty coordinate-(1,2) square.")
    from fractions import Fraction
    from math import isqrt
    # Independent DP on four subtrees, including trees with 2 or 3 children.
    tree=[Fraction(0),Fraction(1)]
    for n in range(2,65):
        best=Fraction(0)
        for a in range(n//4+1):
            for b in range(a,(n-a)//3+1):
                for c in range(b,(n-a-b)//2+1):
                    d=n-a-b-c
                    if d==n: continue
                    best=max(best,(tree[a]+tree[b]+tree[c]+tree[d])/2)
        tree.append(best)
        L=4**((n.bit_length()-1)//2); t=(4*L-n)//3
        assert best==Fraction(n+t,2*isqrt(L))
    print("Four-ary tree DP: formula confirmed for every n=1..64")
    # Use cubic-time-free bitset permutations to check all Q16 squares.
    q4=[0xcff3,0xf5af,0xbbdd,0x7e7e]
    n=16; vnum=1<<n; raw=[bytearray(vnum//8) for _ in range(n)]
    hi_raw=[bytearray(vnum//8) for _ in range(n)]
    high_deg=bytearray(vnum//8)
    for x in range(vnum):
        parts=[(x>>(4*i))&15 for i in range(4)]
        z=sum(parity(a)<<i for i,a in enumerate(parts))
        loc,bit=x//8,1<<(x%8)
        if x.bit_count()>2: high_deg[loc]|=bit
        for i in range(4):
            outer=(q4[i]>>z)&1
            for a in range(4):
                j=4*i+a
                if (x>>j)&1: hi_raw[j][loc]|=bit
                if outer==((q4[a]>>parts[i])&1): raw[j][loc]|=bit
    fs=[int.from_bytes(a,"little") for a in raw]
    high_deg=int.from_bytes(high_deg,"little")
    hi=[int.from_bytes(a,"little") for a in hi_raw]; full=(1<<vnum)-1
    def flip(f,j):
        d=1<<j; return ((f & (full^hi[j]))<<d) | ((f&hi[j])>>d)
    for j,f in enumerate(fs):
        assert f.bit_count()==40960 and f==flip(f,j)
        anf=f
        for k in range(n): anf ^= (anf<<(1<<k))&hi[k]
        assert not(anf&high_deg)
    for i,j in combinations(range(n),2):
        assert fs[i]^flip(fs[i],j)^fs[j]^flip(fs[j],i)==full
    print("Q16 tensor: all direction rules quadratic by Möbius transform; all 1,966,080 faces odd; 327,680 / 524,288 edges.")
