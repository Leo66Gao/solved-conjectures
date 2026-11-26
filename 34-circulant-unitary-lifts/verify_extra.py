"""Exact checks for the trimer at N=9 and five-dimensional rectangle argument."""
from itertools import product, combinations
from sympy import Matrix,I,sqrt,eye,diag,Rational,expand,simplify
w=(-1+I*sqrt(3))/2
r=range(3)
cp=lambda x:expand(x,complex=True)
F=Matrix(3,3,lambda i,j:cp(w**(i*j)/sqrt(3)))
G=[eye(3),F,diag(1,w,1)*F] # chirp j(j+1)/2 mod 3 = 0,1,0.
simp=lambda M:M.applyfunc(cp)
def norm(z):return cp(z*z.conjugate())
for i in r:
    for j in r:
        A=simp(G[i].H*G[j])
        if i==j:assert A==eye(3)
        else:assert all(norm(x)==Rational(1,3) for x in A)
H=[Rational(2,3),Rational(2,3),-Rational(1,3)]
blocks=[[simp(H[(l-i)%3]*G[i].H*G[l]) for l in r] for i in r]
U=Matrix(9,9,lambda i,j:blocks[i%3][j%3][i//3,j//3])
assert simp(U*U.H)==eye(9)
p=[norm(U[0,j]) for j in range(9)]
assert [q*27 for q in p]==[12,4,1,0,4,1,0,4,1]
for i,j in product(range(9),repeat=2): assert norm(U[i,j])==p[(j-i)%9]
print('N=9 exact algebraic Gram = I, all 81 squared entries verified; 27p =', [q*27 for q in p])
for k in range(2,11):
    count=0
    for eps in product(range(3),repeat=k):
        if sum(eps)%3==1 and eps.count(0)==eps.count(1)==eps.count(2):count+=1
    assert count==0
print('k=2,...,10: no triple-root multiset with zero sum and product omega (exhaustive)')
for m in [2,3]:
    for S in combinations(range(5),m):
        assert 1 in [len(set(S)&{(x+h)%5 for x in S}) for h in range(1,5)]
print('N=5 all weight-2 and -3 supports excluded by singleton overlap')
# Positive four-modulus test: a=b=c=d=1/2. Choose first-triangle phases
# A=0, B=2pi/3, C=4pi/3, then E2 needs 5t to align phases.
# Verify the before-rotation two-term length and triangle identities.
h=Rational(1,2)
z=[0,h,h,h*w,h]
def c(v):return cp(v).conjugate()
d1=cp(sum(z[j]*c(z[j-1]) for j in range(5)))
s=cp(z[3]*c(z[1])+z[4]*c(z[2]))
assert d1==0 and norm(s)==h**4
print('N=5 exact nondegenerate example: shift 1 zero and shift-2 closing lengths equal')
print('PASS')
# Exact positive six-state example. Rationals ensure the new perturbation is not
# a floating point density approximation. Reuse the exact 3-point F above.
k=3; delta=Rational(1,20*k)
z=1-delta**2/2+I*delta*sqrt(1-delta**2/4)
V=eye(k)+(z-1)*Matrix.ones(k)/k
f0=simp(V); fp=simp(V*F); fm=simp(-V*F.H)
block2=[[f0,fp],[fm,f0]]
Up=Matrix(6,6,lambda i,j: cp(block2[i%2][j%2][i//2,j//2]/sqrt(2)))
assert simp(Up*Up.H)==eye(6)
p=[norm(Up[0,j]) for j in range(6)]
assert [q*64800 for q in p]==[32398,10800,1,10800,1,10800]
assert all(norm(Up[i,j])==p[(j-i)%6] for i,j in product(range(6),repeat=2))
print('N=6 positive kernel: exact Gram=I, all 36 squared entries verified; 64800p=',[q*64800 for q in p])
print('PASS (including positive example)')
