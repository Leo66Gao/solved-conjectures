"""Exact polynomial positivity certificate for the all-offset equal-normal theorem.
Leo Gao, AI-assisted. Requires SymPy.
"""
import sympy as s
r,A,B=s.symbols('r A B')
x,y,z=s.symbols('x y z')
Q=3*A*B-A-B
W=A+r*B
L=r*(2*W-Q)
D=(1+2*r)*W+L*r*(1-B)
N=(1+2*r)*Q+L*(2*B-1)
C=r*B+A*(1+r*(1-B))
polys=(
 D*(B*(1+r)-Q+A*(2*B-1))-C*N,
 D*(A*(1+r)-r*Q+r*A*(2*B-1))-r*C*N,
)
for f in polys:
 p=s.Poly(f,r,A,B); d,e,g=p.degree_list();q=s.Poly(0,x,y,z)
 for (i,j,k),co in p.terms():
  q+=s.Poly(co*x**i*(y+s.Rational(1,2))**j*(z+s.Rational(1,2))**k*(1+x)**(d-i)*(1+y)**(e-j)*(1+z)**(g-k),x,y,z)
 assert q.coeffs() and min(q.coeffs())>=0
 print(f'degrees {(d,e,g)}; {len(q.terms())} nonzero terms; smallest nonzero coefficient {min(q.coeffs())}')
