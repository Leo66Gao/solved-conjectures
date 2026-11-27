# A forbidden-rotation proof of Iannucci's abundance bound

**Scope.** This proves the subsidiary conjecture in §3, equation (6), of D. E. Iannucci, *On Primitive Weird Numbers of the Form* \(2^kpq\) (2015), [preprint](https://arxiv.org/abs/1504.02761), [published text](https://iosrjournals.org/iosr-jm/papers/Vol11-issue3/Version-3/K0113386130.pdf). It does not settle either part of [Erdős problem 470](https://www.erdosproblems.com/470). A weird number is abundant but not expressible as a sum of distinct proper divisors. A primitive weird number has no proper weird divisor. All weird numbers of this form are primitive. The infinitude of such numbers is open; [Melfi](https://doi.org/10.1016/j.jnt.2014.07.024) gives a conditional construction.

**Theorem.** If \(n=2^kpq\) is weird, where \(k\ge1\) and \(p<q\) are odd primes, write \(M=2^{k+1}-1\) and \(D=\sigma(n)-2n\). Then
\[
 M<D<\frac{(M+1)(M+2)}3 .
\]

**Proof.** The sum of all proper divisors is \(n+D\). By complementation, weirdness implies that \(D>0\) is not a sum of distinct proper divisors. Since every integer from 0 to \(M\) is a subset sum of \(1,2,\ldots,2^k\) (the powers of two), \(D>M\). Multiplicativity gives
\[
 D=M+Mp+Mq-pq=M(M+1)-(p-M)(q-M).
\]
Any representation \(pq=r+bp+cq\) with integers \(0\le r,b,c\le M\) contradicts weirdness: represent the three coefficients in binary using the disjoint divisor blocks \(2^i,2^ip,2^iq\) with \(0\le i\le k\), and add \((2^k-1)pq\) using all \(2^ipq\) with \(0\le i<k\). In particular \(p>M\), since otherwise \(pq=p\cdot q\) uses coefficient \(c=p\). From \(D>M\) we get \((p-M)(q-M)<M^2\), hence \(p<2M\). Furthermore \(q\ge 2M+1\): if \(q\le 2M-1\), the coefficients in
\[
 pq=\tfrac{q-p}{2}+\tfrac{q+1}{2}p+\tfrac{p-1}{2}q
\]
belong to \([0,M]\).

Put \(d=p-M\), a positive even integer. Suppose to the contrary
\[
 d(q-M)\le T:=2(M^2-1)/3. \tag{1}
\]
Since \(q-M\ge M+1\), this implies \(d\le 2(M-1)/3<2M/3\). For \(M=3\) there is no such positive even \(d\); hence \(M\ge7\).

Let \(A=\lfloor M(p+1)/q\rfloor\) and \(h=A-d\). For any \(a\in[d,A]\), divide \(aq=bp+r\) with \(0\le r<p\). We have \(b\le M\) because \(aq\le M(p+1)<(M+1)p\). Also \(a\le p\) since \(q>2M\), so \(0\le p-a\le M\). If \(r\le M\), then \(pq=r+bp+(p-a)q\) is a forbidden certificate. Therefore for every such \(a\) the residues
\[
 z_a=(-aq\bmod p)\quad\text{belong to }[1,d-1]. \tag{2}
\]
We now have
\[
 \frac{M(p+1)}q-d\ \ge \frac{d(M^2+3M+2)}{2M^2+3Md-2}>d/4,
\]
using (1) and \(3d<2M\). For even \(d\ge4\), this gives \(h\ge\lfloor d/4\rfloor\ge(d-2)/4\) and \(h\ge1\). If \(d=2\), (1) gives \(3q\le M^2+3M-1<M(p+1)\), hence \(h\ge1\); (2) makes two successive residues identical, impossible since \(p\nmid q\). Now take \(d\ge4\). Successive differences \(z_{a+1}-z_a\) lie in \([-(d-2),d-2]\), an interval of length less than \(p=M+d\), and all are congruent to \(-q\bmod p\). They are therefore the same nonzero integer \(w\), with \(h|w|\le d-2\) and so \(1\le |w|\le4\). In particular,
\[
 q=jp-w\quad(j\in\mathbb Z),\qquad z_d=dw\bmod p\in[1,d-1]. \tag{3}
\]

We eliminate the eight possible slopes. Throughout \(d<M\), \(p=M+d\), and \(d<2M/3\).

* \(w=1,-1,2\): \(z_d\) is respectively \(d,M,2d\), none admissible.
* \(w=-2\): \(z_d=M-d<d\) requires \(d>M/2\). As \(p+2<2M+1\) (since \(M\ge7\) and \(d<2M/3\)), parity in (3) gives \(q\ge3p+2\). Then \(d(q-M)>M^2>T\).
* \(w=3\): \(3d<2p\); the only admissible residue is \(3d-p\), requiring \(d>M/2\), hence \(d\ge(M+1)/2\). Parity gives \(q\ge2p-3\). Thus \(d(q-M)\ge (M+1)(2M-2)/2=M^2-1>T\).
* \(w=-3\): if \(3d\ge p\), the residue is either zero or \(2p-3d=2M-d>d\). Otherwise (3) gives \(z_d=M-2d\in(0,d)\), so \(M/3<d<M/2\). Parity gives either \(q\ge4p+3\), contradicting (1) since \(d>M/3\), or \(q=2p+3\). In the latter case \(2d\le M-3\): the only other even integer \(2d<M\) is \(M-1\), which gives \(d(q-M)= (M-1)(M+1)>T\). Set \(a=\lceil p/3\rceil\). We have \(a\ge d\) and \(a\le (M-1)/2\) since \(2d\le M-3\). Thus
\[
 pq=(3a-p)+(2a+1)p+(p-a)q
\]
has three coefficients in \([0,M]\), contradicting weirdness.
* \(w=4\): since \(4d<2p\), (3) requires \(4d>p\), i.e. \(d>M/3\). Parity and \(q>p\) give \(q\ge3p-4\). Thus \(d(q-M)>(M/3)(3M-4)>T\) for \(M\ge7\).
* \(w=-4\): if \(4d\ge p\), the residue is either zero or \(2p-4d=2M-2d>d\). Otherwise (3) gives \(M/4<d<M/3\). Now \(q=p+4\) is impossible since \(p+4<2M+1\) for \(M\ge7\) and \(d<M/3\); parity forces \(q\ge3p+4\). Therefore \(d(q-M)>(M/4)(2M+3M/4)=11M^2/16>T\).

All possibilities contradict (1) or weirdness. Thus \(d(q-M)>T\), which is precisely the desired strict upper bound. QED.

**Novelty and limits.** Iannucci explicitly labels (6) a conjecture and checks \(k\le14\). A literature search did not identify a later proof; this is not an exhaustive priority determination. No distribution of primes is invoked. The proof isolates a necessary small-slope obstruction for high abundance and eliminates it. It neither produces an infinite family nor excludes odd weird numbers.

