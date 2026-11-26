# Magnitude is strictly increasing on every four-point metric space

**Theorem.** Let \(X\) be any four-point metric space. Then \(M_X(t)=|tX|\) has \(M_X'(t)>0\) for every \(t>0\). Consequently the least possible cardinality of a negative-type metric space with nonmonotone magnitude belongs to \(\{5,6,7,8,9\}\), in view of the separate nine-point example.

This is a computer-assisted proof by exact nonnegative integer coefficients, not a numerical search over four-point metrics. The certificate simultaneously handles all real distances, including boundary triangles. [Gomi and Tsuji](https://arxiv.org/html/2608.15720v1) explicitly distinguish counterexamples on semimetrics (where four points suffice) from genuine metrics. Their Introduction leaves open whether fewer than the then-known 14 points suffice. The [nine-point example](../NINE_POINTS.md) supplies an upper bound; the theorem below sharpens the lower bound.

## 1. Express any four-point metric by six cut coefficients

For a subset \(S\) of the four labels define \(c_S(i,j)=1\) if exactly one of \(i,j\) belongs to \(S\), and zero otherwise. A four-point metric admits a nonnegative decomposition into four singleton cuts and at most two pair cuts. Here is an elementary proof, included to cover all metrics without assumptions about genericity.

Of the three opposite-edge sums
\(s_1=d_{01}+d_{23},s_2=d_{02}+d_{13},s_3=d_{03}+d_{12}\),
relabel so \(s_1\) is maximal. Give the pair cuts \(01|23,02|13,03|12\) coefficients \(0,(s_1-s_2)/2,(s_1-s_3)/2\), respectively. In the residual symmetric edge array \(d'\), the three opposite sums agree. It follows that \(d'_{ij}=h_i+h_j\) for some \(h_i\) (solve the first three edges for \(h_0,h_1,h_2\), solve one edge to vertex 3 for \(h_3\), then use the equalities of opposite sums for the two remaining edges). For any \(i\) select \(j,k\) in the block opposite \(i\) in the zero cut \(01|23\). Both other pair cuts separate \(j\) from \(k\), so each contributes zero to \(d_{ij}+d_{ik}-d_{jk}\). Hence \(2h_i=d_{ij}+d_{ik}-d_{jk}\ge0\).

This decomposition gives negative type directly: \(z^Tc_S z=-2(\sum_{i\in S}z_i)^2\) for a zero-sum \(z\). For the present calculation \(K(t)\) is strictly positive definite for every \(t>0\): the nonnegative cut representation is squared Euclidean on distinct points and the Gaussian kernel is positive definite there. One direct justification of strictness uses the Fourier representation of the Gaussian: if its quadratic form vanished, the finite exponential sum with the same coefficients would vanish everywhere, and restriction to a line with distinct projections gives an invertible Vandermonde system.

Relabel now so \(h_0\le h_1\le h_2\le h_3\). Put \(a_0=h_0\), \(a_i=h_i-h_{i-1}\) for \(i=1,2,3\), and let \(a_4,a_5\) be the two remaining pair-cut coefficients, in a fixed order. There are just three choices of the pair cuts, as complements describe identical cuts. Then
\[
 d_{ij}=\sum_{\ell=0}^5 m_{ij\ell}a_\ell,\qquad
 m_{ij\ell}=\begin{cases}
 0& i=j,\\
 [i\ge\ell]+[j\ge\ell]& i\ne j,\quad \ell<4,\\
 c_{S_\ell}(i,j)& i\ne j,\quad\ell=4,5.
 \end{cases}
\]
All six coefficients \(a_\ell\) are nonnegative. The individual singleton cuts are not monotone operations in general; sorting them and using differences is essential to this certificate.

## 2. The exact certificate

Treat \(q_\ell=e^{-ta_\ell}\) as independent variables, and put \(K_{ij}=\prod_{\ell=0}^5q_\ell^{m_{ij\ell}}\). Denote \(\det K\) by \(D\), and let \(W_i\) be the determinant of \(K\) with column \(i\) replaced by ones. Cramer's rule gives \(w_i=W_i/D\), where \(w=K^{-1}\mathbf1\). Let
\[
 P_\ell(q)=\sum_{i<j} m_{ij\ell}W_iW_jK_{ij}.
\]
By differentiation of the inverse,
\[
 M'_X(t)=w^T(d\circ K)w
         =\frac{2}{D^2}\sum_{\ell=0}^5 a_\ell P_\ell(q).
\]
The following integer certificate holds for each of the three pair choices and each \(\ell\). Factor out the largest common monomial \(q^\nu\) from \(P_\ell\) and let \(d_i\) be the degree in variable \(i\) of \(q^{-\nu}P_\ell\). Every coefficient of
\[
      Q_\ell(x)=\left[\prod_{i=0}^5(1+x_i)^{d_i}\right]
        (q^{-\nu}P_\ell)(q)\big|_{q_i=(1+x_i)^{-1}}
\]
is nonnegative. To reproduce the certificate, run `python verify_four_point.py` (with NumPy installed). The verifier uses only exact integers: it expands each determinant by its 24 signed monomials, builds \(P_\ell\) by integer additions and convolutions, and substitutes each monomial factor \(q_i^k\) by the binomial coefficients of \((1+x_i)^{d_i-k}\). For its dense arithmetic it proves a per-polynomial bound on absolute partial sums below \(2^{63}\), using the original coefficient \(\ell_1\) norm times \(\prod_i {d_i\choose\lfloor d_i/2\rfloor}\). Thus the hardware integer arithmetic is exact, without overflow or floating point, even during intermediate transforms. The accompanying output records the number of positive entries in each of the 18 coefficient arrays; all remaining entries are zero.

Taking \(x_i=e^{ta_i}-1\ge0\) proves \(M'_X(t)\ge0\). To see that the inequality is strict, set \(x_i=0\) for exactly the indices with \(a_i=0\). For each remaining index \(i\), the corresponding specialized \(Q_i\) is either identically zero or strictly positive whenever all remaining \(x_j>0\). Therefore \(M'_X\) is either identically zero on \(t>0\) or strictly positive throughout. The first possibility is impossible: \(K(t)=I+E(t)\) with zero diagonal in \(E\) and with positive off-diagonal entries, tending to zero at infinity. Write \(b(t)=\max_{i\ne j} E_{ij}(t)\). The Neumann expansion gives \(M_X(t)=4-\mathbf1^T E(t)\mathbf1+O(b(t)^2)\), while \(\mathbf1^TE(t)\mathbf1\ge2b(t)>0\). Thus \(M_X(t)<4\) for all sufficiently large \(t\), and it tends to 4. This proves strict positivity of the derivative.

**Scope.** This does not exclude five- to eight-point metrics with three or more distinct nonzero distances. The finite certificate is generated directly from the formulas above, so no graph classes, stored coefficient arrays, solver output, or discretized distances need to be trusted.

For a fully standard-library reproduction, run `python verify_four_point_pure.py`. It uses unbounded Python integers, constructs \(W_i\) by cofactor row sums, and substitutes \(q_i=(1+x_i)^{-1}\) by sequential Taylor shifts in Horner form. Its output has been independently checked to match `four-point-verification.txt` byte for byte. This second implementation is slower but needs no NumPy and does not use an overflow bound.
