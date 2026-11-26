"""Exact rational verification of ordered paths and shear trimming.
Leo Gao / AI-assisted. Standard library only.
The finite tests are independent checks of the analytic proof, not its basis.
"""
from fractions import Fraction as F
from itertools import combinations

def paths(A,B,C,D):
    L=(0,C);R=(1,D);P=(A,0);Q=(B,1)
    return [[L,P,R],[L,Q,R],[L,Q,P,R],[L,R]]

def pieces(paths, weights, n):
    for p,w in zip(paths,weights):
        for (s,z),(t,u) in zip(p,p[1:]):
            m=w*(t-s)
            v=n(s,z);j=n(t,u)
            if m:
                yield (min(v,j),max(v,j),m)

def testlaws(items):
    items=list(items)
    atoms=sum(m for l,h,m in items if l==h)
    endpoints=sorted({l for l,h,m in items}|{h for l,h,m in items})
    densities=[]
    for l,h in zip(endpoints,endpoints[1:]):
        mid=(h+l)/2
        value=sum(m/(j-k) for k,j,m in items if k<mid<j)
        densities.append((l,h,value))
    assert atoms+sum((h-l)*d for l,h,d in densities)==1
    return atoms,densities

def choose(A,B,C,D):
    # Interpolate to a positive equal-coordinate vector on a horizontal
    # or vertical side, then cancel it with the negative diagonal vector.
    u=(1-A)/D;v=B/(1-C)
    x=(1-B)/(1-D);y=A/C
    chi=1/(C-D)
    m=min(u,v)
    p=(1- m/(m+chi))
    ww=[F(0)]*4;ww[3]=1-p
    if u>=v:
        ww[1]=p*(u-v)/(u+x);ww[2]=p-ww[1]
    else:
        ww[0]=p*(v-u)/(v+y);ww[2]=p-ww[0]
    assert sum(ww)==1 and all(w>=0 for w in ww)
    return ww

if __name__=='__main__':
    zz=[F(j,8) for j in range(1,8)]
    count=0;exact_atoms=0
    for B,A in combinations(zz,2):
        for D,C in combinations(zz,2):
            pp=paths(A,B,C,D)
            ww=choose(A,B,C,D)
            atoms,bands=testlaws(pieces(pp,ww,lambda s,z:z))
            assert not atoms and all(w==1 for l,h,w in bands)
            var=sum(w*sum(max(0,z-u) for (s,z),(t,u) in zip(p,p[1:])) for p,w in zip(pp,ww))
            assert var<=1
            for a in [F(1,8),F(1,6),F(1,3),F(1,2),F(3,4)]:
                atoms,bands=testlaws(pieces(pp,ww,lambda s,z:s+a*z))
                loss=atoms+sum((h-l)*max(0,w-1) for l,h,w in bands)
                assert loss <= a*var
                count+=1;exact_atoms+=int(atoms>0)
    print(f'PASS: {count} exact rational path/shear configurations; {exact_atoms} have atoms.')
    for a in [F(1,8),F(1,3),F(1,2),F(3,4)]:
        for j in range(9):
            B=(1-a)*F(j,8);r=(1-B-a)/(1-B)
            assert 0<=r<=1
            pp=[[(0,0),(B,1),(1,0)]]
            pts=list(pieces(pp,[1],lambda s,z:z))
            _,dens=testlaws(pts)
            assert all(v==1 for _,_,v in dens)
            assert (1-B)*(1-r)==a
            assert B/(B+a)<1
    print('PASS: all 36 endpoint fold samples have exactly the mass and slack predicted.')
