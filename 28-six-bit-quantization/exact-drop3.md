# Dropping three noisy input bits: optimality through dimension 13

**Theorem.** For any integer \(3\le n\le13\), let \(X\) be uniform on \(\{0,1\}^n\), and let \(Y=X\oplus Z\) with independent error bits \(Z_i\sim\mathrm{Bernoulli}(p)\). For each deterministic \(U=f(X)\) with at most \(2^{n-3}\) values,
\[
 I(U;Y)\le(n-3)(1-h_2(p)),\qquad 0\le p\le 1/2
\]
in bits. Selecting any \(n-3\) coordinates attains equality. The quantizer need not be balanced. The case n=9 is the only six-bit case here; for n>9 this theorem concerns more than six output bits. The unrestricted six-bit problem is not resolved.

## Reduction to the affine cell inequality

Use nats in the proof. Put \(C=\ln2-h(p)\), and for a nonempty cell \(A\) of size \(m\) let \(J(A)=I(X_A;X_A\oplus Z)\) with \(X_A\) uniform on \(A\). Set \(\lambda(p)=7/5\) for \(p\le\lfloor 2^{60}/5\rfloor/2^{60}\) and \(51/50\) otherwise. We will prove for every nonempty \(A\subseteq\{0,1\}^n\) that
\[
 J(A)\ \ge\ [3+\lambda(p)(1-8/m)]C. \tag{1}
\]
In fact we prove the stronger \(J(A)\ge(3+\lambda(p))C\) at \(m=22\); that bound holds for every \(m>22\) as well, since the uniform law on \(A\) is an equal-weight mixture of uniform laws on its 22-element subsets. Concavity of output entropy proves the assertion, since \(J=H(Y_A)-nh(p)\). For \(m=1,2\) the right side of (1) is nonpositive, so it remains only to check \(m=3,\ldots,22\).

If there are \(K\le2^{n-3}\) nonempty cells, averaging (1) with weights \(m/2^n\) gives
\[
 I(X;Y\mid U)\ge [3+\lambda(p)(1-8K/2^n)]C\ge3C.
\]
By the chain rule \(I(U;Y)=I(X;Y)-I(X;Y\mid U)\le nC-3C\). This also makes clear why the slope may depend on the common channel parameter \(p\), but not on the individual cell. A constant slope given by the leading high-noise statistic need not work: with \(\lambda=1\), the right side at \(p=0\) would exceed \(\ln m=J(A)\) for \(m=5,6,7\).

## Shape reduction

Consider a reflection \(\sigma\) that flips a bit, or swaps two coordinate positions \(i<j\). For each nonfixed orbit \(\{x,\sigma x\}\), designate as preferred the member having 0 in the flipped bit, or having (1,0) in bits \((i,j)\) in the swap case. Sort the two input masses so that the larger goes on the preferred side. For two preferred-side points \(x,y\), \(d(x,y)\le d(\sigma x,y)\), so their BSC kernel weights satisfy \(K(x,y)\ge K(\sigma x,y)\). The two output masses for \(y,\sigma y\) have unchanged sum, and after sorting the absolute value of their difference is
\[
 \sum_{x\text{ preferred}}(K(x,y)-K(\sigma x,y))\,
           |\Pr(X_A=x)-\Pr(X_A=\sigma x)|,
\]
no smaller than before by the triangle inequality. Fixed output masses are unchanged. Thus output entropy cannot increase, and the set's size is unchanged. Applying a nontrivial sort strictly decreases the sum of the binary integer labels of members, so sorts terminate at a stable set. Such a set satisfies the prerequisite relations “remove bit 0 if present” and “move a set bit down one step when the preceding bit is absent.” These necessary relations suffice for exhaustive enumeration of a superset of stable sets. The verifier inserts the members in increasing integer order, beginning with 0. A possible next member has a smaller prerequisite and is therefore discovered as an upward neighbor of at least one present member; the program checks that all prerequisites are present. The finite check is performed in dimension 13. Any smaller-dimensional stable set is among the enumerated representatives after padding with fixed zero coordinates. Fixed-zero coordinates contribute \(h(p)\) each to output entropy and therefore cancel from \(J\).

## Certified cell bounds

For a representative of support dimension \(d\), let \(P\) be the noisy output distribution and \(t\) the coefficient in (1), or the stronger coefficient for \(m=22\). The check is \(H(P)\ge t\ln 2+(d-t)h(p)\). The eight-point 3-face satisfies this identically. All other cases are treated as follows.

**Near complete noise.** For \(\rho=1-2p\), write \(2^dP(y)=1+u_y\). Its Walsh expansion gives \(|u_y|\le(1+\rho)^d-1\) and
\[
 2^{-d}\sum_y u_y^2\le \rho^2 B_A+(2^d/m-1)\rho^4,\qquad
 B_A=\sum_i\bigl(\mathbb{E}_{X_A}(-1)^{X_i}\bigr)^2
\]
by Parseval. The second derivative of \((1+s)\ln(1+s)-s\) is \(1/(1+s)\), so
\[
 D(P\Vert\mathrm{Unif})\le\frac{\rho^2[B_A+(2^d/m-1)\rho^2]}{2[2-(1+\rho)^d]}.
\]
For each shape, the verifier searches downward from \(\rho=2^{-7}\) through powers of two and finds a correlation at which the ratio without \(\rho^2/2\) is less than \(d-t\); the bound also holds at every smaller \(\rho\). Since \(C\ge \rho^2/2\), by the even power series for the binary entropy deficit, this gives the desired cell bound.

**Near zero noise.** The output is a mixture of translates of the uniform input law, so \(H(P)\ge\ln m\). For \(m\ne8\) the script checks that this lower bound already exceeds \(t\ln 2+(d-t)h(2^{-20})\). For noncube shapes with \(m=8\), let \(\beta\) be the number of directed edges out of the cell divided by 8. The chance of leaving the cell via exactly one flipped bit is \(\beta p(1-p)^{d-1}\), and for any output outside the cell its mass \(8P(y)\) is at most \(dp\) by symmetry of the channel and the union bound. All \(8P(y)\le1\) by double stochasticity, so
\[
 H(P)-\ln 8
 = \sum_y P(y)\ln(1/(8P(y)))
 \ge\beta p(1-p)^{d-1}[\ln(1/p)-\ln d].
\]
Use \(c=\beta(1-(d-1)2^{-48})\), put \(L=\ln(1/p)\ge32\), and note that the script checks \(c>d-3\), \(c(32-2)>(d-3)33\), and \(\ln d<2\). This proves \(H(P)-\ln8\ge(d-3)h(p)\), because \(h(p)\le p(L+1)\).

**Remaining compact intervals.** Entropy is monotone in BSC noise on \([0,1/2]\) by the noise semigroup and entropy concavity. For each shape and each of the two slope choices, recursively subdivide the remaining noise interval until the lower bound for \(H(P)\) at the left endpoint exceeds the upper bound for \(t\ln 2+(d-t)h(p)\) at the right. For each dyadic endpoint \(p=a/D\), \(D=2^{60}\), compute exactly the integer
\[
 w_y=\sum_{x\in A}a^{d(x,y)}(D-a)^{d-d(x,y)}.
\]
Then \(mP(y)=w_y/D^d\), so
\[
 H(P)=\ln m+\frac{\sum_y w_y\ln(D^d/w_y)}{mD^d}.
\]
All logarithms are bracketed by binary range reduction and the first 21 terms of \(2\operatorname{atanh} z\) for \(0\le z\le1/3\), with tail at most \(2z^{43}/[43(1-z^2)]\) and fixed-point rounding outwards on scale \(2^{80}\). The noiseless and complete-noise endpoints follow by continuity, or directly.

**Reproduction.** Run **python3 verify-drop3.py** (standard library, do not disable assertions) from this directory. The original run used independent cardinality ranges 3–10, 11–14, 15–18, 19–20, and 21–22 in parallel. All 1,030 compressed candidates passed; including the eight-point face as a candidate, the remaining 1,029 required a total of 152,416 closed dyadic interval tests. See **verify-drop3.log** for the cardinality-by-cardinality output.

## Equality for interior noise

For 0<p<1/2 the kernel difference in a nonfixed output pair is strictly positive for each two preferred-side points (the distances under the bit reflection differ by one, and under the coordinate swap by two). Therefore if input pairs have both positive and negative unsorted mass differences, the triangle inequality in the compression argument is strict, and entropy strictly decreases. If all nonzero differences have the same sign, the compression is either the identity or a global reflection. Consequently an original cell can give equality in (1) in the interior only if its compressed form is the eight-point face and every compression was an isometry; then it too is a three-dimensional coordinate face. For a quantizer, every nontrivial bound is strict unless K=2^(n−3) and all cells are coordinate three-faces. Conversely any such partition has the same conditional output entropy as an (n−3)-coordinate projection; the free coordinates may vary across cells. At p=0 any balanced 2^(n−3)-cell partition attains the bound; at p=1/2 every quantizer has zero information.

## Scope and literature

The result advances the fixed-output threshold question in [Mahdavifar–Beirami, Conjecture 13](https://arxiv.org/abs/2609.26444v2) for the codimension-three output regime up to dimension 13. The earlier [Huleihel–Ordentlich paper](https://arxiv.org/abs/1701.03119) solves the drop-one problem and uses one-coordinate shifting. This document does not assert literature priority. The checks are independently reproducible integer computations, not a theorem-prover formalization or external peer review.
