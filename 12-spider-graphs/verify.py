"""Independent exact checks, not a substitute for the asymptotic proof. Uses sympy."""
from itertools import product,permutations
from collections import Counter
from math import comb,prod
from polynomials import tagged,x,t
from investigate import witness
def direct(b,V,c):
    # Direct integer composition weights, no polynomial algebra, no normalization.
    n=sum(V); vals=[]
    def path(ws):
        return ws[0]*prod(v-1 for v in ws[1:])
    total=0
    for ws in set(permutations(V)):
        total+=path(ws)
        for j in range(1,len(ws)):
            h=sum(ws[:j]); f=path(ws[:j])*path(ws[j:])
            if h<=c: total+=f
            if b<h<=b+c: total-=f
    return total
from fractions import Fraction
def randomized(b,V,c):
    assert min(V)>c
    n=sum(V); M=len(V); count=Counter(V)
    R=lambda v:Fraction(v,v-1)
    def dp(C,acc,first,last_weight,hit):
        if not sum(C):
            return first*(1-last_weight) if hit else first
        out=0
        for i,v in enumerate(count):
            if not C[i]:continue
            C2=list(C);C2[i]-=1
            out+=Fraction(C[i],sum(C))*dp(C2,acc+v,first or R(v),
                         R(v) if b<acc<=b+c else last_weight, hit or b<acc<=b+c)
        return out
    from math import factorial
    cnt=factorial(M)//prod(factorial(v) for v in count.values())
    return cnt*prod(v-1 for v in V)*dp(list(count.values()),0,0,0,False)
for c in range(2,6):
 d=c+1
 for L in range(6):
  V=[d]*(5-L)+[d+1]*L
  for b in range(c,(sum(V)-c-1)//2+1):
   assert direct(b,V,c)==randomized(b,V,c)
P=tagged(0,6);Q=tagged(2,2)
assert P.total_degree()<=6 and P.degree(x)==5
assert (P.as_expr().expand().coeff(x,5)+768*(4*t-13)).expand()==0
assert (Q.as_expr()+16*(16*t+5)*x+2*(4*t+5)*(8*t+9)).expand()==0
rows={(6,6):{0:[1]*4,2:[5]*4,4:[]},
      (10,5):{0:[1]*4,1:[4]*4,2:[3],3:[],4:[2]},
      (14,5):{0:[1]*3,2:[4]*3,3:[4],4:[1]},
      (14,7):{0:[1]*4,3:[6]*4,4:[5],5:[],6:[2]}}
for (delta,d),tab in rows.items():
 for b,V in tab.items():
    assert (2*b+delta+4-sum(V))%d==0
    tot=2**len(V)
    inside=sum(sum(v*q for v,q in zip(V,B))%d in {(b+i)%d for i in (1,2,3)} for B in product((0,1),repeat=len(V)))
    assert d*inside>tot*(d-1)
assert [b for b in range(0,140,4) if b%5 not in rows[14,5] and b%7 not in rows[14,7]]==[16,36]
print('PASS: exact randomized coefficient vs direct composition weights; two symbolic polynomials; all 17 residue table entries; final CRT classes')
for b in (12,15,18):
    count=0
    for n in range(2*b+3,b*(b+1)):
        if n%(b+1)<=n//(b+1):continue
        assert witness(n,b);count+=1
    print(f'PASS: c=2, b={b}: {count} non-coin cases have a negative elementary coefficient; all other a are excluded by missing connected partitions')
