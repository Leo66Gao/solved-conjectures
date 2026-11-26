# Ten input bits, six output bits: proof on the entire crossover interval up to 0.308242798

**Theorem.** Let \(X\) be uniform on \(\{0,1\}^{10}\) and \(Y=X\oplus Z\), where the noise bits are independent Bernoulli(\(p\)). Every deterministic quantizer \(U=f(X)\) with at most 64 output values satisfies
\[
 I(U;Y)\le 6(1-h_2(p))\qquad(0\le p\le20201/65536).
\]
Equality is achieved by reporting six coordinates. No balance assumption is made. Moreover for every \(20202/65536\le p<1/2\), a purely cardinality-based affine cell bound of the type used here is impossible. Thus the verified range of the proof and the obstruction are separated by only \(1/65536\). The obstruction does not assert that any actual quantizer beats coordinate projection.

## Averaging a size-dependent cell inequality

Use nats until the end. Put \(C(p)=\ln2-h(p)\) and \(J(A,p)=I(X_A;X_A\oplus Z)\) for \(X_A\) uniform on a nonempty cell \(A\) of size \(m\). For each of the three crossover intervals below we use the indicated fixed positive slope \(\lambda\):
 
| Interval | \(\lambda\) |
|---|---:|
| \([0,77/256]\) | \(10/7\) |
| \([77/256,631/2048]\) | \(887/625\) |
| \([631/2048,20201/65536]\) | \(141909/100000\) |

We prove
\[
 J(A,p)\ge [4+\lambda(1-16/m)]C(p). \tag{1}
\]
For size 44 the check gives the stronger \(J(A,p)\ge(4+\lambda)C(p)\). For every larger size the same stronger bound follows by writing its uniform distribution as the equiprobable mixture of uniform distributions on its 44-subsets. Output entropy is concave and the conditional noise entropy \(10h(p)\) is constant. The \(m=16\) case is the earlier all-noise per-cell theorem, reproduced by the included **prior-verify-balanced.py 10** and its archived **prior-balanced10.log**. Crucially that theorem is per cell: it does not require the *other* cells to have size 16.

If the partition has \(K\le64\) nonempty cells, its average of (1) is
\[
 I(X;Y\mid U)\ \ge\ [4+\lambda(1-16K/1024)]C(p)\ge4C(p).
\]
Subtract this from \(I(X;Y)=10C(p)\). This gives the desired theorem, converted to bits.

## Reduction to shifted families

A two-point compression is obtained by reflecting (i) a bit, preferring its 0 side, or (ii) two positions \(i<j\), preferring \(x_i=1,x_j=0\); in each nonfixed pair put the larger of its input masses on the preferred side. For two preferred-side points \(x,y\), the BSC kernel entry \(K(x,y)\) is at least \(K(\sigma x,y)\). The two output masses at \(y,\sigma y\) have unchanged sum; their new difference is a sum of nonnegative factors \(K(x,y)-K(\sigma x,y)\) times the absolute input-pair differences, so it is at least the original absolute difference. Entropy cannot increase, and uniformity on a set of size \(m\) is preserved. Nontrivial compressions strictly decrease the sum of binary-encoded point indices and terminate.

A stable family contains the prerequisites when one removes bit 0 or moves a 1 one place down into a vacant preceding bit. These necessary conditions suffice for exhaustive checks: begin at 0 and add words in increasing order, accepting only if all their prerequisites already occur. Every nonzero word has such a predecessor; the integer recursion marks the reverse edges. The full ten-cube is used even when some coordinates are fixed.

## Exact certificate for the three bands

For \(m<44\) write \(t=4+\lambda(1-16/m)\); for \(m=44\) write \(t=4+\lambda\). For \(t\le0\) there is nothing to prove. Otherwise \(0<t<10\) and the output entropy target is \(H(P_A(p))\ge t\ln2+(10-t)h(p)\). For an interval \([a,b]\) and an interior sampled \(c\), monotonicity of output entropy gives \(H'_A(p)\ge0\). Data processing gives \(J'_A(p)\le0\), hence \(H'_A(p)\le10h'(p)\). These statements follow from the BSC semigroup and apply on the open domain; continuity includes the endpoints. As a function of the increasing entropy parameter \(h\), the proof gap
\[
 F_A(p)=H(P_A(p))-t\ln2-(10-t)h(p)
\]
can increase with slope at most \(t\), or decrease with slope magnitude at most \(10-t\). Thus for the full interval it suffices to check at the midpoint a lower bound exceeding
\[
 \max\{t[h(c)-h(a)],(10-t)[h(b)-h(c)]\}.
\]
If the simpler universal bound \(H(P_A)\ge\ln m\) suffices at the largest noise, the interval is certified without enumerating its shapes. Otherwise the code checks all eligible shifted shapes at the midpoint and bisects for the cardinalities not yet certified. It validates full coverage separately for each tested cardinality by a sum of exact dyadic interval lengths.

**Directed arithmetic.** The crossover grid denominator is \(2^{27}\). A point kernel value \(p^d(1-p)^{10-d}\) is scaled by \(Q=2^{44}\) and floored after each multiplication; the propagated error in the scaled kernel is at most 10. Thus for \(g_y=mP_A(y)\), the integer prefix sum \(G_y\) gives \(G_y/Q\le g_y\le\min(1,(G_y+10m)/Q)\). The lower entropy contribution follows from
\(-g_y\ln g_y\ge(G_y/Q)[-\ln \min(1,(G_y+10m)/Q)]\).
The case \(G_y=0\) contributes zero. Hence \(H(P_A)\) has the lower bound \(\ln m+(1/m)\sum_y\) of those terms. To speed evaluation the DFS maintains the integer prefix sums by adding/removing one point kernel per step.

Every logarithm is range-reduced to \(\ln x=e\ln2+\ln v\) with \(1\le v\le2\). Using \(z=(v-1)/(v+1)\), the first 18 terms of \(2\operatorname{atanh} z\) are rounded outwards at scale \(2^{46}\), and the positive remainder is at most \(2z^{37}/[37(1-z^2)]\). For per-output entropy terms only a lower bound on the negative logarithm is needed. The first band uses a table of \(2^{14}\) mantissa bins and the logarithm upper bound at the bin's right edge. Later bands use the tighter upper tangent at the left edge. For a mantissa \((j+r)/2^{14}\) with \(0\le r<1\), that upper bound is the upper endpoint for \(\ln(j/2^{14})\) plus \(r/j\) rounded upwards. The reciprocal \(1/j\) itself is rounded up in the stored table. This proves that all fixed-point tests are one-sided in the needed direction; no floating-point values are used in comparisons.

For implementation overflow checks: \(G_y\le Q\), and in the tangent calculation the denominator exponent of the remainder is at most 29, while the scaled reciprocal is at most \(2^{32}\). Thus the tangent product is below \(2^{61}\). A per-output lower negative logarithm is at most \(44\ln2\) at scale \(2^{46}\), and its product with \(G_y\) below \(2^{95}\). The total over 1024 outputs is below \(2^{105}\). The integer comparison numerator before multiplication by \(mQ\) has absolute size at most \(2^{76}\) (use \(0\le t\le7\), \(m\le44\), slope denominator \(\le10^6\), and \(0\le h\le\ln2\)); hence the product is below \(2^{126}\). These accumulations and products use 128-bit integers.

The remaining finite test is genuine exhaustive verification, not a stochastic search. Across the bands the logs report 4,224 adaptive interval nodes and 2,280,747 checked shape/crossover pairs. Not every interval checks every size, since already certified cardinalities do not need refinement. Equally, when an interval fails for one shape of a particular size, the rest of that size are skipped for that interval and checked after bisection.

## A sharp obstruction to extending this particular proof

Consider two specific sets in the ten-cube:
- \(A\), the full radius-one ball of size 11;
- \(B\), a free coordinate times the radius-one ball in the nine-cube, of size 20.

If a common affine slope in (1) exists, multiplying the inequalities for these two cells by 11 and 25 cancels the slope, and forces \(11J(A,p)+25J(B,p)\ge144C(p)\). Let \(D_A,D_B\) denote their noisy-output divergences from the appropriate uniform laws, counting the free coordinate as zero divergence. Since \(J=10C-D\), the necessary condition is
\[
 11D_A(p)+25D_B(p)\le216C(p).
\]
The exact verifier **verify-obstruction.py** proves the strict reverse inequality for \(20202/65536\le p<1/2\). For the middle interval each radius-one ball has shell polynomials for its output mass, with shell multiplicities \({d\choose r}\). On a closed interval \([a,b]\), use the divergence lower bound at \(b\) and the capacity upper bound at \(a\), by the noise semigroup. Directed rational logarithms certify 1,952 intervals up to the dyadic floor of \(2/5\). At larger noise put \(\rho=1-2p\). Entropy subadditivity gives \(D_A(p)\ge (\rho^2/2) B_A\) and likewise for \(B\), where \(B_A=810/121\) and \(B_B=144/25\) are the sums of squared coordinate means. Thus the weighted coefficient is \(216+18/11\). The even series for the binary deficit gives \(C(p)\le(\rho^2/2)[1+\rho^2/(6(1-\rho^2))]\). The desired strict reverse inequality follows when \(0<\rho^2<1/23\), which covers this entire high-noise cap.

The two cell sizes can be arithmetically averaged to 16 by mixing four 11-point cells and five 20-point cells. This is only a relaxed multiset of sizes, not a tiling of the ten-cube. Any continuation beyond the obstruction must use information the independent-cell comparison discards, such as constraints between cells in a genuine partition.
