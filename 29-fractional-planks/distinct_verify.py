"""Exact coefficient certificates for the triangle with distinct medians. Leo Gao, AI-assisted."""
import sympy as s
import itertools
a,b,c=s.symbols("a b c"); x,y,z=s.symbols("x y z")
A=1-b+b*c; B=1-c+c*a; C=1-a+a*b
# names A=alpha, B=gamma, C=beta; common denominator 2*A*B*C
U=A*(C+B-A); V=B*(A+C-B); W=C*(A+B-C)
def cert(f):
 p=s.Poly(f,a,b,c);ds=p.degree_list();q=s.Poly(0,x,y,z)
 for (i,j,k),v in p.terms():
  q+=s.Poly(v*x**i*y**j*z**k*(1+x)**(ds[0]-i)*(1+y)**(ds[1]-j)*(1+z)**(ds[2]-k),x,y,z)
 return q
for name,v in [('U',U),('V',V),('W',W)]:
 p=cert(v);print(name,min(p.coeffs()),len(p.terms()));assert min(p.coeffs())>=0
for bits in itertools.product((0,1),repeat=3):
 l=[((1-b)*V,c*W),(a*U,(1-c)*W),((1-a)*U,b*V)]
 f=3*A*B*C-s.Add(*(e[h] for e,h in zip(l,bits)))
 p=cert(f);print(bits,min(p.coeffs()),len(p.terms()));assert min(p.coeffs())>=0
