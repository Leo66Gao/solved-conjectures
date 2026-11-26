"""Exact rational checks for the two-equal-normal fractional plank note.
Leo Gao, AI-assisted. Standard-library Python 3 only.
"""
from fractions import Fraction as F
a0=F(8,5); emin=F(1,35); amin=F(11,7)
assert a0-emin==amin
lam=1/(3*(2-amin))
assert lam==F(7,9)
assert 2*lam-1==F(5,9)
gamma=F(3,70); c=F(4,35); Y=F(1,2)
assert (F(5,6)*emin)/(2*lam-1)==gamma
assert F(5,2)*emin+gamma==c
assert 25*emin/(1+15*emin)==Y
Lam=(Y-gamma)/(1+c); assert Lam==F(16,39)
alpha=1-F(15,4)*emin; beta=F(2,3); rho=F(13,30)
assert alpha==F(25,28)
assert Lam*alpha>rho*beta
assert beta<=1-2*gamma
m=alpha/2
D0=1-2*gamma-beta/2-Lam*(1+c-m)
R2=(Lam**2+beta**2-2*rho*Lam*beta)/4
assert D0==F(419,1365)
assert D0>0
assert D0**2-R2==F(1648,5589675)>0
X=(F(4,5)*alpha)**2+(beta/5)**2-2*rho*(F(4,5)*alpha)*(beta/5)
Z=(F(4,5)/amin)**2*(alpha**2+beta**2+2*rho*alpha*beta)
assert F(15,4)*amin*alpha > (1+beta)**2
assert X-F(4,9)==F(11,11025)>0
assert Z-F(4,9)==F(301,27225)>0
print('PASS: forced contact deviations and ellipse containments')
print('a minimum:',amin,'min slope gap after squaring:',D0**2-R2)
print('squared x width above 4/9:',X-F(4,9))
print('squared z width above 4/9:',Z-F(4,9))
