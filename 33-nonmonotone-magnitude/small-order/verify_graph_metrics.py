"""Enumerate graph distances on <=8 points and certify every negative-type case exactly."""
from fractions import Fraction as F
from math import comb, gcd
from collections import Counter
import sys

def exact_metric(n,w):
    r=[[n]*n for i in range(n)]
    for i in range(n):r[i][i]=0
    for j in range(n):
        for i in range(j):
            if w & (1 << (j*(j-1)//2+i)):r[i][j]=r[j][i]=1
    for k in range(n):
        for i in range(n):
            for j in range(n):r[i][j]=min(r[i][j],r[i][k]+r[k][j])
    return r if all(n not in row for row in r) else None

def psd(d):
    B=[[d[i][0]+d[j][0]-d[i][j] for j in range(1,len(d))] for i in range(1,len(d))]
    while B:
        for i,row in enumerate(B):
            if row[i]<0 or (row[i]==0 and any(row)):return False
        if not any(B[0]):B=[row[1:] for row in B[1:]];continue
        p=B[0][0]
        B=[[p*B[i][j]-B[i][0]*B[0][j] for j in range(1,len(B))] for i in range(1,len(B))]
        g=gcd(*(x for row in B for x in row))
        if g>1:B=[[x//g for x in row] for row in B]
    return True

def trim(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a
def add(a,b,sgn=1,shift=0):
    if len(a)<len(b)+shift:a.extend([0]*(len(b)+shift-len(a)))
    for i,v in enumerate(b):a[i+shift]+=sgn*v
    return a

def determinant(M):
    n=len(M);tab=[[1]]+[[]]*((1<<n)-1)
    for mask in range(1,1<<n):
        i=mask.bit_count()-1;p=[0];m=mask
        while m:
            b=m&(-m);j=b.bit_length()-1;m^=b
            d=M[i][j]
            if d is not None:add(p,tab[mask^b],-1 if m.bit_count()%2 else 1,d)
        tab[mask]=trim(p)
    return tab[-1]

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):c[i+j]+=x*y
    return c
def der(a):return [i*v for i,v in enumerate(a) if i]
def variations(seq):
    s=[x>0 for x in seq if x];return sum(x!=y for x,y in zip(s,s[1:]))
def sturm(p):
    p=[F(v) for v in p]
    while not p[0]:p=p[1:]
    seq=[p,der(p)]
    if not seq[-1]:return 0
    while len(seq[-1])>1:
        x,y=seq[-2][:],seq[-1]
        while len(x)>=len(y):
            a=x[-1]/y[-1];i=len(x)-len(y)
            for j,v in enumerate(y):x[i+j]-=a*v
            trim(x)
            if x==[0]:break
        if x==[0]:break
        seq.append([-v for v in x])
    return variations([q[0] for q in seq])-variations([q[-1] for q in seq])
def certificate(d):
    n=len(d);den=determinant(d)
    num=[-x for x in determinant([r+[0] for r in d]+[[0]*n+[None]])]
    p=trim(add(mul(num,der(den)),mul(der(num),den),-1)) # sign of -M_q
    L=len(p)-1;s=[0]*(L+1)
    for i,x in enumerate(p):
        for j in range(L-i+1):s[i+j]+=x*comb(L-i,j)
    if min(s)>=0 and max(s)>0:return 'binomial'
    if max(s)>0 and sturm(s)==0 and next(x for x in s if x)>0:return 'Sturm'
    return 'undecided'

if __name__=='__main__':
    counts=Counter()
    for ln in sys.stdin:
        n,w=map(int,ln.split());counts[n,'all']+=1
        d=exact_metric(n,w)
        if d is None:continue
        counts[n,'connected']+=1
        if n==1 or not psd(d):continue
        counts[n,'negative type']+=1
        if max(map(max,d))>=3:counts[n,'negative type, diam>=3']+=1
        result=certificate(d);counts[n,result]+=1
        if result=='undecided':print('UNDECIDED', n,w,d,flush=True)
    keys=('all','connected','negative type','negative type, diam>=3','binomial','Sturm','undecided')
    print('order',*keys,sep=' | ')
    for n in range(1,9):
        assert counts[n,'all']==[0,1,2,4,11,34,156,1044,12346][n]
        assert counts[n,'connected']==[0,1,1,2,6,21,112,853,11117][n]
        print(n,*(counts[n,k] for k in keys),sep=' | ')
    assert all(counts[n,'undecided']==0 for n in range(1,9))
