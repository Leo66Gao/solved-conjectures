#!/usr/bin/env python3
"""Reproduce the Penney counterexample and exact counts, Python standard library only."""
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache
import argparse

def words(n):
    return [''.join(a) for a in product('01',repeat=n)]

def prefix_states(v,w):
    return sorted({t[:i] for t in (v,w) for i in range(len(t))},key=lambda x:(len(x),x))

def markov_win(v,w,p):
    """Solve the transient first-step equations using exact Gaussian elimination."""
    if w in v: return Q(0)
    states=prefix_states(v,w); z=len(states)
    eq=[[Q(i==j) for j in range(z)]+[Q(0)] for i in range(z)]
    for i,u in enumerate(states):
        for symbol,mass in [('0',1-p),('1',p)]:
            s=u+symbol
            if s.endswith(v):eq[i][-1]+=mass
            elif not s.endswith(w):
                t=max((j for j in states if s.endswith(j)), key=len)
                eq[i][states.index(t)]-=mass
    for i in range(z):
        j=next(j for j in range(i,z) if eq[j][i]); eq[i],eq[j]=eq[j],eq[i]
        h=eq[i][i];eq[i]=[x/h for x in eq[i]]
        for j in range(z):
            if i!=j and (h:=eq[j][i]):eq[j]=[x-h*y for x,y in zip(eq[j],eq[i])]
    return eq[0][-1]

def exact_counts(N,p, *, with_ties=False):
    a,b=p.numerator,p.denominator
    by_len=[[],*(words(i) for i in range(1,N+1))]
    weight={s:b**len(s)*a**(N-s.count('1'))*(b-a)**(N-s.count('0')) for ww in by_len for s in ww}
    @lru_cache(None)
    def pref(s):return [(s[:i],weight[s[:i]]) for i in range(1,len(s)+1)]
    def corr(u,v):return sum(h for t,h in pref(v) if u.endswith(t))
    ac={x:corr(x,x) for x in weight}
    total=ties=0
    for n in range(1,N+1):
        for v in by_len[n]:
            for short in by_len[1:n]:
                for w in short:
                    if w not in v:
                        d=(ac[w]-corr(w,v))-(ac[v]-corr(v,w))
                        total+=d>0;ties+=d==0
        yield (total,ties) if with_ties else total

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('-N',type=int,default=8);N=ap.parse_args().N
    for m in range(3,13):
        for p in [Q(1,17),Q(2,7),Q(1,3),Q(1,2),Q(7,8)]:
            assert markov_win('01'+'0'*(m-1),'0'*m,p)==(1-(1-p)**(m-1))/(1+p)
    for p in [Q(1,17),Q(2,7),Q(9,20),Q(1,2),Q(7,8)]:
        assert markov_win('1100','000',p)==p*p*(p*p-3*p+3)/(p*p-p+1)
    print('55 independent exact absorbing-chain checks passed.')
    for a,b in [('45086610067','45086610068'),('29289321881','29289321882'),('47098343217','47098343218'),('48533057514','48533057515')]:
        p,q=Q(a)/10**11,Q(b)/10**11
        print('counts at p =',p,'and',q,'for caps 4 through',N)
        xx=list(exact_counts(N,p,with_ties=True));yy=list(exact_counts(N,q,with_ties=True))
        print('ties at cap',N,xx[-1][1],yy[-1][1])
        x=[u for u,t in xx];y=[u for u,t in yy]
        print([(n,x[n-1],y[n-1],y[n-1]-x[n-1]) for n in range(4,N+1)])

    # Wider finite-cap example, including the eventual local reversal at N=9.
    for p in (Q(4709,10000),Q(471,1000)):
        print('wider test p=',p, '(counts,ties) by cap 5 ...',N,list(exact_counts(N,p,with_ties=True))[4:])

    # Independent full enumeration at cap five, using only transition equations.
    W5=[words(i) for i in range(1,6)]
    for p,expected in ((Q(4709,10000),27),(Q(471,1000),28)):
        count=sum(markov_win(v,w,p)>Q(1,2) for nv in range(1,5) for v in W5[nv]
                  for nw in range(nv) for w in W5[nw])
        assert count==expected
        print('direct Markov all-pairs cap 5 p=',p,'favorable=',count)
