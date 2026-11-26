from functools import lru_cache
from itertools import accumulate

def greedy(m,n):
    a,b=[n]*m,[m]*n
    w=[]
    while max(a):
        i=max(range(m),key=a.__getitem__)
        j=max(range(n),key=b.__getitem__)
        q=min(a[i],b[j])
        w.append(q); a[i]-=q;b[j]-=q
    return w

def exact(m,n):
    @lru_cache(None)
    def g(a,b):
        if not a or not b:return (0,)*(a+b+1)
        out=[0]*(a+b+1)
        for i in range(1,a+1):
            for j in range(0,b+1):
                w=min(i*n,j*m);cost=i+j-1
                for k,x in enumerate(g(a-i,b-j)):
                    out[k+cost]=max(out[k+cost],w+x)
        return tuple(accumulate(out,max))
    return g(m,n)

if __name__=='__main__':
    import sys
    M=int(sys.argv[1]) if len(sys.argv)>1 else 16
    for n in range(2,M+1):
        for m in range(1,n):
            g=list(accumulate([0]+greedy(m,n)))
            f=exact(m,n)[:len(g)]
            if tuple(g)!=f:
                print(m,n,g,f);raise SystemExit
        print('verified through',n,flush=True)
