# The Fallat–Xing spread conjecture in dimension nine

**Leo Gao** · AI-assisted research · Not peer reviewed

[Read the PDF](manuscript.pdf) · [LaTeX source](manuscript.tex)

> **Abstract.** We verify the Fallat–Xing conjecture for real symmetric matrices of order nine over every nondegenerate real interval. Rank-two attainment follows from a signed-threshold reduction, exact integer certificates, and convex interpolation across the interval. This result does not settle the conjecture in higher dimensions.

**Status:** complete computer-assisted argument for dimension nine, not a resolution in arbitrary dimension. The numerical stage proposes rational witnesses; verification of the witnesses is by integer and rational arithmetic. No external review or proof-assistant certification claimed.

**Theorem.** Let $-1 \le  a < 1$. Among real symmetric nine-by-nine matrices with entries in the closed interval $[a,1]$, the largest spread (maximum eigenvalue minus minimum eigenvalue) is
$$
\max_{1\le k\le 8} b_k(a),\qquad b_k(a)=\sqrt{(ka-(9-k))^2+4k(9-k)}.
$$
The maximizing block size is 4 for $-1<a<-3/7$, 3 for $-3/7<a<3/5$, and 2 for $3/5<a<1$ (both adjacent block sizes at a switch, and 4 or 5 at $a=-1$). Indeed, as a function of $k$ the squared spread is a concave quadratic with vertex at $9/(3+a)$, so the best integer is the nearest one. It is attained by a matrix of rank exactly two with all entries in $\{a,1\}$. By global negation if necessary, then positive scaling, the dimension-nine result extends to every nondegenerate real entry interval.

## Variational reduction

Put $n=9$, write $J$ for the all-ones matrix, and put $\delta =1-a$. A signed-threshold form is $A_H(a)=J-\delta *H$, with
$$
H_{ij}=\frac{1-d_i d_j\varepsilon_{\min(i,j)}}2,\qquad d_i,\varepsilon_i\in\{-1,1\},\quad d_1=1.
$$
There are $2^{2n-1}$ signed parameter choices. The maximum spread over them equals the unrestricted maximum.

For the proof, take a maximizer $A_*$ and corresponding orthonormal extreme eigenvectors $u,v$; then $S=uu^{\mathsf T}-vv^{\mathsf T}$ has $\operatorname{tr}(A_* S)=s(A_*)$. Put $x=u+v,y=u-v$ so that $S=(xy^{\mathsf T}+yx^{\mathsf T})/2$. Perturb $x,y$ by tending-to-zero amounts such that all $y_i$ and $x_i$ are nonzero and all magnitudes $|x_i/y_i|$ are distinct. This is possible since the excluded conditions lie in a finite union of proper polynomial zero sets. No orthogonality of these perturbations is needed. Sort indices in decreasing ratio magnitude. For the perturbed matrix, the sign of its $(i,j)$ coefficient is $d_i\,d_j\,\varepsilon_{\min(i,j)}$, where $d_i=\operatorname{sgn}(y_i)$ and $\varepsilon _i=\operatorname{sgn}(x_i/y_i)$; simultaneous negation of all $d_i$ sets $d_1=1$. This follows by factoring $y_i\,y_j$ and using the sign of the larger-magnitude summand of $x_i/y_i+x_j/y_j$ (or, on the diagonal, the sign of the single ratio). Entrywise choice of the maximizing endpoint for the perturbed linear functional produces exactly a signed-threshold matrix up to permutation. A subsequence chooses the same matrix $C$ in the original order because only finitely many endpoint matrices exist. Taking the limit of the linear comparisons gives $\operatorname{tr}(C S)\ge \operatorname{tr}(A_* S)$; the Rayleigh principle gives $s(C)\ge \operatorname{tr}(C S)$. The reverse inequality is immediate because the signed-threshold matrices are feasible.

Each $s(A_H(a))$ is convex in $a$: it is the supremum of affine functions given by Rayleigh-quotient differences.

## The two analytic classes

If $H$ is the indicator outer product $vv^{\mathsf T}$ of a size-$k$ subset, the feasible matrix $B_k(a)=A_H(a)$ has nonzero eigenvalues given by the symmetric two-by-two quotient with diagonal $k\,a,n-k$ and off-diagonal $\sqrt{k(n-k)}$. For $1\le k<n$, its determinant $-(1-a)k(n-k)$ is negative. Hence the spread equals $b_k(a)$ and the rank is two. For $k=0,n$, the matrix is a constant matrix of spread at most nine, less than $b_2(a)$ for $a<1$.

If $H=J_k+J_k+0$ on two disjoint equal nonempty supports, up to joint permutation, $s(A_H(a))\le b_k(a)$. To see this, set $X=n+k\,\delta $ and $Y=\sqrt{n^2+2k(n-4k)*\delta +k^2\,\delta ^2}$. The antisymmetric difference of the two block indicators is an eigenvector with eigenvalue $-k\,\delta $. The symmetric block sum and the outside indicator give the two other possibly nonzero eigenvalues $(n-k\,\delta  \pm  Y)/2$, with determinant $-(n-2k)k\,\delta <0$ because n=9 is odd. Since $X^2-Y^2=8k^2\delta>0$, the smaller root is above $-k\,\delta $; the larger root is positive. Thus the spread is $(X+Y)/2$, whose square is $b_k(a)^2-(X-Y)^2/4$ by direct expansion. This analytic comparison is strictly favorable to $B_k(a)$.

Checking the entries shows that exactly 18 signed choices are class one and 4 are class two. The verifier checks every remaining 131,050 choices independently.

## Rational-node certificates and their interpolation

For each of nine listed rational nodes in `points.tsv`, and for every nonexceptional $H$, we give a rational $L$ (stored as a signed little-endian integer in its node's `lowerXXX.bin`, after multiplying by 10^6). The verifier certifies both $A_H(a)-LI$ and $(L+U)I-A_H(a)$ positive definite with integer Sylvester tests, where $U$ is the rational in the table after dividing its last column by 10^6. This implies $s(A_H(a))<U$ irrespective of how the numerical search chose $L$.

For efficiency, equal-row groups of $H$ are collapsed. Let $V$ have their indicator vectors as columns, $D=V^{\mathsf T} V$ the diagonal of positive group sizes, and $B$ the reduced symmetric matrix of representative entries of $A_H(a)$. Then $A_H(a)=VBV^{\mathsf T}$; a shift restricted to the span of the columns of $V$ is positive definite iff its congruence $DBD-xD$ is positive definite there (with the opposite sign for an upper shift). The orthogonal complement is killed by $A_H(a)$; the verifier separately checks the shift sign there when the complement is nontrivial. Multiplication by the positive integer clearing denominator preserves these conclusions. Sylvester's criterion is implemented via the fraction-free Bareiss recurrence (no pivoting is needed on a positive definite matrix; encounter a nonpositive leading minor and reject). At each stage the pivot is the next leading principal determinant, and divisions by the previous positive pivot are exact by the determinant identity for bordering minors.

On an interval $[p,q]$ between consecutive nodes, use $k=4,3,2$ for midpoints lying respectively below $-3/7$, between $-3/7$ and $3/5$, or above $3/5$. The chord with the two node bounds $U_p,U_q$ lies above the spread of each nonexceptional matrix by convexity. The tangent to $b_k$ at $m=(p+q)/2$ has value
$$
\frac{B+k(km-(9-k))(a-m)}{\sqrt B},\qquad B=b_k(m)^2.
$$
Exact squaring of the positive numerator shows that this tangent is strictly above the corresponding $U$ at both endpoints. Since both are affine it lies above the chord throughout. The tangent lies below $b_k$ by its convexity (it is the norm of a two-coordinate affine vector). This covers $[-9/10,199/200]$ in eight intervals.

## Left endpoint

At $a=-1$, conjugate by $\operatorname{diag}(d)$ to eliminate the signature. Then the matrix is exactly $\varepsilon_{\min(i,j)}$. If the sign sequence has no change, the spread is nine. With exactly one change, at block size $k$, the quotient has diagonal entries of opposite signs and gap $\sqrt{81+4k(9-k)}\le \sqrt{161}$. For the 494 other sign sequences, the same shifted-positive-definiteness verifier gives $s<1268/100<\sqrt{161}$; these witnesses are in `left.bin`. The full bound at $a=-1$ is therefore $\sqrt{161}=b_4(-1)$.

The tangent to $b_4$ at $-1$ takes value $(787/5)/\sqrt{161}$ at $-9/10$. At that node the rational nonexceptional bound $U=12360407/10^6$ is strictly below it (verify by squaring). Thus the chord from $(-1,\sqrt{161})$ to the right node's bound lies at or below this tangent, which in turn lies below $b_4$. This proves the desired nonexceptional inequality on $[-1,-9/10]$, including any ties at $-1$.

## Right endpoint

Set $u=1/\sqrt{n}$ times the all-ones vector and $P=I-uu^{\mathsf T}$. Relative to $u$ and its orthogonal complement, (A_H) has blocks
$$
\begin{pmatrix}n-\delta h&-\delta b^{\mathsf T}\\-\delta b&-\delta K\end{pmatrix},\quad h=u^{\mathsf T}Hu,\quad b=PHu,\quad K=(PHP)|_{u^\perp}.
$$
Write $c=\lambda_{\max}(K)$. For $0<\delta \le 1/200$, the scalar first block and all eigenvalues of the lower block are separated by at least $n(1-2\delta )$, because $\lVert H\rVert\le n$. By the Rayleigh principle the top eigenvalue is at least the first diagonal block and the bottom eigenvalue is at most $-\delta *c$. For the top eigenvalue, eliminating the lower coordinates gives an upper correction at most $\delta ^2\Vert b\Vert ^2/[n(1-2\delta )]$, by the resolvent norm bound for a real symmetric matrix. For the bottom eigenvalue, eliminate the top coordinate: subtracting the rank-one term $\delta ^2 bb^{\mathsf T}/(n-\delta *h-\lambda_{\min})$ from the lower block can reduce its smallest eigenvalue by at most the same correction. The two inequalities give
$$
s(A_H)\le n+\delta(c-h)+\frac{2\delta^2\lVert b\rVert^2}{n(1-2\delta)}.
$$
The squared norm $\lVert b\rVert^2$ is the average squared deviation of the row sums of $H$ from their mean. Because the row sums lie in $[0,n]$, it is at most $n^2/4$: use $r^2\le n\,r$ and then $\mu *(n-\mu )\le n^2/4$.

Let $E$ have columns $e_i-e_n$ for $i<n$. The exact verifier checks positive definiteness of
$$
\left(25\sum_{i,j}H_{ij}+27n\right)E^{\mathsf T}E-25nE^{\mathsf T}HE.
$$
for every nonexceptional $H$, certifying $c-h<27/25$. Therefore
$$
\begin{aligned}s(A_H)&\le 9+\delta\left(c-h+\frac{9\delta}{2(1-2\delta)}\right)\\&<9+\delta\left(\frac{27}{25}+\frac1{44}\right)<9+\frac{10}{9}\delta\le b_2(a).\end{aligned}
$$
The last inequality follows by comparing squares, since $b_2(a)^2=81+20\,\delta +4\,\delta ^2$. This covers $[199/200,1)$.

## Reproduce

From the repository root run `sh 04-spectral-spread/reproduce.sh n9`, which unpacks the certificate to a temporary directory, compiles the checker with C++17 and GMP, and runs the Python standard-library arithmetic wrapper. To run manually, decompress this directory’s `*.bin.gz` files to the corresponding `*.bin` files first. The saved witness files make floating-point software unnecessary for verification.
```
g++ -O3 -std=c++17 verify.cpp -lgmpxx -lgmp -o verify
python3 -O verify_arithmetic.py
```
Expected result: 16 strict rational interior tangent inequalities plus the left/right scalar checks; 988 left endpoint integer PD tests; 131,050 right endpoint integer PD tests; 262,100 integer PD tests at each of nine middle nodes, 2,358,900 total. The optional `discover.py` reproduces candidate generation with NumPy; use `OPENBLAS_NUM_THREADS=1 python discover.py`. Roundoff variation in generated witness grids does not establish or refute any result: the independently run exact checks are decisive.

## Sources and novelty boundary

- Shaun M. Fallat and YongJun Xing, [On the spread of certain normal matrices](https://doi.org/10.1080/03081087.2012.703189), Linear and Multilinear Algebra 60 (2012), 1391–1407. Original conjecture (rank-two attainment for unrestricted real symmetric interval matrices).
- Neil J. Calkin et al., [On the maximal spread of symmetric Bohemian matrices](https://arxiv.org/abs/2510.15919), covers dimensions through seven and selected other cases. The $a=0,n=9$ case was already known.
- Sidney Holden's signed-threshold reduction and Sahraneshinsamani's two-cluster formula, perturbation and chord–tangent framework are prior work; see Nima Sahraneshinsamani, [Eight Is Enough, source and certificate](https://github.com/snima/sp08-dimension-eight/tree/cf035d2d7ff9db0b0a16471891fe413bd59281ef). This project adapts their mathematical approach with independent dimension-nine witnesses, a compressed rational congruence checker, and an explicit tangent argument for the left endpoint. The cited November 16 package proves all parameters at nine's predecessor dimension eight, the left strip in all dimensions n>=7 and only small n=9 interior neighborhoods besides known points. [The maintained problem record](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/SP-08/README.md) still identifies dimension nine and higher as unresolved outside known strips. Targeted searches found no complete earlier dimension-nine proof; this bounded search does not certify novelty.
