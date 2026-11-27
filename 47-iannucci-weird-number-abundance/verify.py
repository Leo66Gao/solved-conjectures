"""Independent finite check of the abundance bound, no external packages.

(1) Check the original definition by exact subset sum on all relevant primes
for 1<=k<=8, reproducing published counts. We don't use a rotation criterion.
(2) Stress the certificate rectangle for arbitrary odd M (not just Mersennes)
and arbitrary coprime odd p,q (even composites), with gcd optional: in fact
p not dividing q suffices. Verify *positive certificates* by integer equality.
"""
from math import isqrt
def sieve(n):
    f=bytearray(b'\x01')*(n+1);f[0:2]=b'\x00\x00'
    for i in range(2,isqrt(n)+1):
        if f[i]:
            sl=slice(i*i,n+1,i);f[sl]=b'\x00'*len(f[sl])
    return f
def by_divisor_subset(k,p,q):
    n=(1<<k)*p*q
    proper=sorted({(1<<i)*t for i in range(k+1) for t in [1,p,q,p*q]}-{n})
    D=sum(proper)-n
    if D<=0:return False
    # Complementation is general, not the proof's modular certificate.
    bits=1
    mask=(1<<(D+1))-1
    for t in proper:
        if t>D:break
        bits=(bits|(bits<<t))&mask
        if (bits>>D)&1:return False
    return True
def validate_divisor():
    expected=(1,1,5,3,10,23,29,53)
    prime=sieve(140000)
    alltested=0
    for k,count in enumerate(expected,1):
        M=(1<<(k+1))-1
        hits=tested=0; peak=0
        # D>M necessary by binary subset-sums. p<=M implies semiperfect;
        # p<2M follows from D>M and q>p; no restriction re q>=2M here.
        for p in range(M+2,2*M,2):
            if not prime[p]:continue
            for q in range(p+2,M+(M*M-1)//(p-M)+1,2):
                if not prime[q]:continue
                tested+=1
                if by_divisor_subset(k,p,q):
                    D=M*(p+q+1)-p*q
                    assert 3*D<(M+1)*(M+2),(k,p,q,D)
                    hits+=1;peak=max(peak,D)
        alltested+=tested
        assert hits==count,(k,hits,count)
        print(f'k={k}: tested {tested}; weird {hits}; max abundance {peak}')
    print('direct subset-sum tested:',alltested)
def validate_rectangle():
    count=0
    for M in range(3,256,2):
        for p in range(M+2,2*M,2):
            d=p-M
            for q in range(p+2,M+2*(M*M-1)//(3*d)+1,2):
                if q%p==0:continue
                count+=1
                # Direct constructive search over every coefficient c such
                # that c*q<=pq. The first representation certifies the result.
                for c in range(min(M,p),-1,-1):
                    b,r=divmod((p-c)*q,p)
                    if b>M:break
                    if r<=M:
                        assert r+b*p+c*q==p*q and 0<=r<=M and 0<=b<=M and 0<=c<=M
                        break
                else:raise AssertionError(('exhausted',M,p,q))
                assert b<=M and r<=M,('failed',M,p,q)
    print('generalized certificate triples:',count)
if __name__=='__main__':
    validate_divisor();validate_rectangle()
