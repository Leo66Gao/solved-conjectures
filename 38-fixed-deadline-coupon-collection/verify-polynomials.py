"""Prove the four polynomial identities by exact evaluation at 2d+1 points."""
from fractions import Fraction as F
from math import prod
polys = {
 2:[45,99,72,19,1],
 3:[3968,14880,22200,16702,6540,1200,68],
 4:[92300,497350,1143965,1462904,1131922,537956,150953,22138,1196],
 5:[1811232,12643200,38944680,69530280,79352100,60087366,30229390,9768970,1853430,162620,1592]}
for d, P in polys.items():
 a={2:1,3:3,4:2,5:1}[d]
 c=1+F(1,d) if d<5 else F(1)
 assert min(P)>0
 for x in range(2*d+1):
  u=F(x,x+1);L=[1/(v-u) for v in range(2,d+2)]
  E=(c+u*(1-u))*(sum(L)**2+sum(i*i for i in L))+2*(1-2*u)*sum(L)-2
  D=a*prod((i*x+i+1)**2 for i in range(1,d+1))
  assert E*D==sum(h*x**j for j,h in enumerate(P))
 # Each L_i term before taking reciprocal powers contains (x+1) in its numerator;
 # it cancels every denominator x+1 in u(1-u) and (1-2u)L_1.
 # Hence the scaled expression is a polynomial of degree at most 2d.
 print(f"d={d}: polynomial identity verified at {2*d+1} distinct points, all coefficients strictly positive")
