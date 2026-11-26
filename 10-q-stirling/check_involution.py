"""Enumerate both last-letter involutions exactly (standard library only)."""
from itertools import product
from collections import Counter

def mon(word):
    h=t=neg=0; xs=[]
    for l in word:
        if l=='T': t+=1
        else: xs.append(h+1)
        if l=='R': neg+=1
        h+=l!='H'
    return (t,tuple(sorted(xs))),(-1)**neg

def generic():
    checked=0
    for n in range(11):
        for p in product('HRT',repeat=n):
            def invol(p):
                i=next((i for i in range(n-1,-1,-1) if p[i]!='T'),None)
                if i is None:return p
                return p[:i]+('R' if p[i]=='H' else 'H',)+p[i+1:]
            q=invol(p); assert invol(q)==p
            if p==q: assert p==('T',)*n
            else:
                (w,s),(v,t)=mon(p),mon(q)
                assert w==v and s==-t
            checked+=1
    return checked

def colored(a,n):
    def trav(prefix,h):
        if len(prefix)==n: yield prefix;return
        for up in (0,1):
            for label in range(1-up,a(h)+1):
                yield from trav(prefix+((up,label),),h+up)
    def toggle(p):
        for i in range(n-1,-1,-1):
            up,label=p[i]
            if label:return p[:i]+((1-up,label),)+p[i+1:]
        return p
    seen=0; pairs=Counter()
    for p in trav((),0):
        q=toggle(p); assert toggle(q)==p
        h=0
        for up,label in q:
            assert 1-up<=label<=a(h)
            h+=up
        if p==q: assert p==((1,0),)*n
        else:
            assert sum(j for i,j in p)==sum(j for i,j in q)
            assert (sum(i for i,j in p)-h)%2
        pairs[sum(j for i,j in p)]+=(-1)**(n-sum(i for i,j in p));seen+=1
    assert pairs[0]==1 and all(c==0 for j,c in pairs.items() if j)
    return seen

if __name__=='__main__':
    print(generic(),'general signed words verified.')
    runs=(lambda j:j,lambda j:2*j+1,lambda j:3*j+1,lambda j:(0,5,1,3)[j%4])
    count=sum(colored(a,n) for a in runs for n in range(6))
    print(count,'q-labelled histories verified in 24 specializations.')
