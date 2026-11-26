"""Exact algebra for the singular shortest-leg-three slice; uses SymPy."""
from sympy import symbols,expand,Poly,factor
from math import comb,prod
x,t=symbols('x t')
def tagged(r,l):
    # n=2b+4t+6, b=4x+r; there are l 5s; all other parts are 4s.
    k=2*x+t+(2*r+6-5*l)//4
    assert (2*r+6-5*l)%4==0
    def w(h,j):
        return 16 if not j else prod(h+i for i in range(1,j))*(16*h+15*j)
    expr=12*w(k,l)
    for i in (1,2,3):
        for j in range(l+1):
            if (r+i-5*j)%4:continue
            h=x+(r+i-5*j)//4
            expr-=comb(l,j)*w(h,j)*w(k-h,l-j)
    return Poly(expr,x,t)
if __name__=='__main__':
 for r,l in ((0,6),(2,2)):
    p=tagged(r,l)
    print('b mod 4:',r,'; L:',l)
    for i in range(l,-1,-1):
        print(i, factor(p.as_expr().expand().coeff(x,i)))
