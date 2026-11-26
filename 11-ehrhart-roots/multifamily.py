"""Certify several simultaneous conjugate pairs using rational univariate polynomial arithmetic."""
from certify import m,star
import sympy as S
def pol(x):return S.Poly(x,m, domain=S.QQ)
one=pol(1)
def triple(k,r):
    p,d,w=map(pol,star(k))
    if r==1:return p,d,w
    return p*p,r*p*d,r*p*w+r*(r-1)*d*d
def merge(X,Y):
    p,a,b=X;q,c,d=Y
    return p*q, a*q+p*c, b*q+2*a*c+p*d
def count(K,h,block=0):
    A=triple(K,1)
    for j in range(h,2*h+1):
        A=merge(A,triple(j,5))
    a,b,c=A
    f=a*pol((m+1)*(3*m+2)+block*m*(m+1))+b*pol(4*m+3)+c
    f=f.clear_denoms()[1].primitive()[1]
    assert f.gcd(f.diff()).degree()==0
    nr=f.count_roots(-S.oo,S.oo)
    n=K+3+5*sum(j+1 for j in range(h,2*h+1))
    return n,f.degree(),nr,(f.degree()-nr)//2
if __name__=='__main__':
    for h,K in [(2,1000),(3,5000),(4,3000),(5,3000)]:
        for block in (0,1):
            n,d,real,pairs=count(K,h,block)
            print('h,K,top,n,degree,real,nonreal pairs:',h,K,block,n,d,real,pairs)
