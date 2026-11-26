"""Exact integer checks only; the theorem itself is proved analytically."""
from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import comb
import random

def part(q,m):
    return sum((-1)**k*comb(q,k)*(q-k)**m for k in range(q+1))

def coefficients(n,law):
    """Return coefficients of t^m in CDF numerator for integer masses."""
    ret=Counter()
    for missed in range(1<<n):
        t=sum(w for A,w in law.items() if not A&missed)
        ret[t]+=(-1)**missed.bit_count()
    return [(k,w) for k,w in ret.items() if w]

def numerator(c,m):
    return sum(w*k**m for k,w in c)

def direct(n,law,m):
    states={0:1}
    for _ in range(m):
        nxt=Counter()
        for b,k in states.items():
            for a,w in law.items():
                nxt[a|b]+=k*w
        states=nxt
    return states.get((1<<n)-1,0)

def is_uniform_partition(q,law):
    return (len(law)==q and len(set(law.values()))==1 and
            all(not (a&b) for a,b in combinations(law,2)))

def main():
    n,q=6,3; universe=[a for a in range(1<<n) if a.bit_count()<=2]
    subset=[a for a in universe if a.bit_count()==2]
    laws=tests=ties=0
    for draw in combinations_with_replacement(universe,4):
        law=Counter(draw); c=coefficients(n,law);laws+=1
        for m in (3,4,5,6,7,10):
            a=numerator(c,m); b=part(q,m)
            assert a*q**m<=b*4**m;tests+=1
            if a*q**m==b*4**m: ties+=1
        if laws%331==0:
            for m in (2,4,9): assert direct(n,law,m)==numerator(c,m)
    print(f"All denominator-4 laws on six coupons with packages of size 0,1,2: {laws} laws; {tests} comparisons; {ties} ties.")
    # Include a denominator divisible by q and assignments restricted to actual pairs.
    cnt=tie=0
    for draw in combinations_with_replacement(subset,3):
        law=Counter(draw);c=coefficients(n,law)
        for m in (3,4,7,15):
            a=numerator(c,m); b=part(q,m)
            assert a<=b and (a==b)==is_uniform_partition(q,law)
            cnt+=1;tie+=a==b
    print(f"All denominator-3 pair laws: {cnt} CDF comparisons; {tie} ties, exactly uniform partitions.")
    # Near-partition interior/one-defect tests, including at a certified late integer horizon.
    # m=256 n^2 exceeds 256 n log(2n) since n>=2 => n>=log(2n).
    rng=random.Random(42); cmp=local=0
    blocks=[3,12,48]
    for weights in [(1,1,1),(7,9,11),(850,849,851)]:
        good=dict(zip(blocks,weights));G=sum(weights)
        cg=coefficients(n,good)
        for trial in range(8):
            bad=Counter(rng.choices([x for x in universe if x not in blocks],k=3)); B=sum(bad.values())
            law=Counter(good);law.update(bad);c=coefficients(n,law)
            for m in (4,11,31,256*n*n):
                assert numerator(c,m)*q**m<part(q,m)*(G+B)**m;cmp+=1
            for m in (1,2,4,8):
                # Exactly one forced bad draw, any position. Enumerate good union states.
                states=Counter({0:1})
                for _ in range(m-1):
                    nxt=Counter()
                    for a,i in good.items():
                        for b,j in states.items(): nxt[a|b]+=i*j
                    states=nxt
                count=sum(i*j for a,i in bad.items() for b,j in states.items() if (a|b)==(1<<n)-1)
                assert count==B*numerator(cg,m-1);local+=1
    print(f"Mixed laws: {cmp} strict comparisons, including 24 at m={256*n*n}; {local} exact one-defect identities.")
if __name__=='__main__': main()
