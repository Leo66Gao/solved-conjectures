"""Python >=3.10 + SymPy. Exact arithmetic throughout, including independent subtree counts."""
import sympy as s
from math import comb
m=s.symbols('m')
def star(k):
    u=(s.Rational(k,2)+1)*m
    v=k*m*(m+2)/12
    return 1+u,(u*(u+1)+v)/2,(u*(u+1)*(2*u+1)+(6*u+3)*v)/6
def certificates(K=53,l=1,r=10):
    p,D,W=star(K);q,d,w=star(l)
    a=p*q*q;b=D*q*q+r*p*q*d
    c=W*q*q+r*p*q*w+r*(r-1)*p*d*d+2*r*D*d*q
    for block in (False,True):
        f=s.Poly(s.expand(((m+1)*(3*m+2)*a+(4*m+3)*b+c+int(block)*m*(m+1)*a)/2),m)
        den,ip=f.clear_denoms();content,ip=ip.primitive()
        print('block' if block else 'singleton', '(ascending) quintic:',ip.all_coeffs()[::-1], 'prefactor',content/den)
        print('discriminant:',s.discriminant(ip.as_expr(),m),'real root count',ip.count_roots(-s.oo,s.oo))
        assert ip.degree()==5 and ip.count_roots(-s.oo,s.oo)==3
        for t in range(6):
            assert (t+1)**(K+l*r)*q.subs(m,t)**(r-2)*f.eval(t)==brute(t,K,l,r,block)
def convolve(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b): out[i+j]+=v*w
    return out
def attach(t,children):   # count lattice points by their total deficit under new singleton
    joint=[1]
    for row in children: joint=convolve(joint,row)
    out=[0]*(len(joint)+t)
    for deficit,n in enumerate(joint):
        for new in range(t+deficit+1):out[new]+=n
    return out
def brute(t,K,l,r,block):
    leaf=attach(t,[]);big=attach(t,[leaf]*K);small=attach(t,[leaf]*l)
    if not block: return sum(attach(t,[attach(t,[big]+[small]*r)]))
    row=big
    for _ in range(r):row=convolve(row,small)
    return sum(n*comb(2*t+i+2,2) for i,n in enumerate(row))
if __name__=='__main__': certificates()
