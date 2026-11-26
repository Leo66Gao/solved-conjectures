# Width and free joins of thin lattice simplices

**Status.** The arguments below prove Conjectures 1.5 and 1.6 and answer Question 1.4 in Vadym Kurylenko, [*Thin simplices via modular arithmetic*](https://arxiv.org/html/2404.03975v2#S1.SS4), also appearing as such in the [2026 journal article](https://doi.org/10.5070/C6.68698). The targeted literature search found no earlier proof of these geometric statements; that is not a priority guarantee. The character method and group-covering bounds below have established precedents; the deductions here concern lattice simplices.

**Theorem.** Let \(\Delta\) be a full-dimensional thin lattice simplex of dimension \(d\ge 1\).
1. If \(d\) is odd, an affine integral function takes the values 0 and 1 on the vertices of \(\Delta\), with **an odd number of vertices in each fiber**. In particular, \(\Delta\) has lattice width one.
2. If \(\Delta\) has lattice width at least two, its normalized volume is at most \((d+1)!\). In particular, there are only finitely many such simplices up to affine unimodular equivalence in every fixed dimension.
3. In each fixed dimension, only finitely many spanning thin simplices are not free joins. None exist in odd dimensions.

## Barycentric coordinates modulo 1

Choose coordinates in which the ambient lattice is \(\mathbb Z^d\). Write the vertices as \(v_0,\dots,v_d\), put \(n=d+1\), and let \(A\) be the invertible \(n\times n\) matrix with columns \((v_i,1)\). The finite group
\[
C=A^{-1}\mathbb Z^n/\mathbb Z^n\subset (\mathbb R/\mathbb Z)^n
\]
has order \(|\det A|=\operatorname{Vol}_{\mathbb Z}(\Delta)\), because multiplication by \(A\) identifies it with \(\mathbb Z^n/A\mathbb Z^n\). For each \(c\in C\), the representative in \([0,1)^n\) gives exactly one lattice point of the half-open fundamental parallelepiped, by applying \(A\). The open parallelepiped consists of representatives with every coordinate nonzero. Since the local \(h^*\)-polynomial counts its lattice points by height, thinness is equivalent to saying each \(c\in C\) has at least one zero coordinate.

For \(i\in I=\{0,\dots,d\}\), put \(\chi_i(c)=e^{2\pi i c_i}\) and \(H_i=\ker\chi_i\). For \(S\subseteq I\), put \(\chi_S=\prod_{i\in S}\chi_i\). In particular, \(\chi_I=1\), since the last row of \(A\) is all ones. An affine integral function with values 1 precisely on the vertices indexed by \(S\) exists if and only if \(\chi_S=1\). Indeed, the unique real affine function giving those values is
\[
x\longmapsto \mathbf{1}_S^\mathsf T A^{-1}(x,1),
\]
where \(\mathbf{1}_S\) is the vector of indicators. If \(\chi_S=1\), the row \(\mathbf{1}_S^\mathsf T A^{-1}\) is integral, since its value on each integer \(z\in\mathbb Z^n\) is integral by applying the character condition to \(A^{-1}z+\mathbb Z^n\). Conversely, an affine integral function with the stated vertex values is given by an integral row of this form, which implies \(\chi_S=1\). Thus width one is equivalent to the existence of a nonempty proper such \(S\): the resulting integral affine function is nonconstant and has width one. Conversely, an integral linear form attaining width one can be shifted to give integer vertex values in \(\{0,1\}\).

## The character identity and odd dimension

For any \(J\subseteq I\) such that \(\bigcup_{i\in J}H_i=C\), one factor of \(\prod_{i\in J}(1-\chi_i(c))\) vanishes at every \(c\in C\). Expanding and averaging yields
\[
0=\frac{1}{|C|}\sum_{c\in C}\prod_{i\in J}(1-\chi_i(c))
 =\sum_{\substack{S\subseteq J\\ \chi_S=1}}(-1)^{|S|}. \tag{1}
\]
Here the average of a character is 1 if trivial and 0 otherwise: translating the summation by an element where the character is not 1 multiplies the sum by a scalar different from 1 without changing it.

For a thin simplex \(J=I\) is a cover. When \(d\) is odd, \(n\) is even, so \(S=\varnothing\) and \(S=I\) contribute \(+1\) each in (1). There must therefore be an odd-cardinality \(S\) with \(\chi_S=1\). It is nonempty and proper, and its complement is odd as well. The affine integral function above proves the first assertion.

## Irredundant covers and bounded volume

Suppose the width is at least two. If a proper \(J\subsetneq I\) covered \(C\), the empty subset would contribute \(+1\) to (1), so there would be a nonempty \(S\subseteq J\) with \(\chi_S=1\). This would contradict width at least two. Hence the coordinate-kernel cover is irredundant: no proper subcollection covers. Moreover \(\bigcap_{i\in I}H_i=\{0\}\), because the coordinate characters jointly distinguish every element from zero.

Here is an elementary finite-group bound, the subgroup case of [Tomkinson’s factorial bound](https://doi.org/10.1080/00927878708823445) for irredundant covers by cosets. Suppose a finite group \(G\) has an irredundant cover by \(n\) subgroups. Select the subgroups in a suitable order. If \(j<n\) have already been selected, let \(K\) be their intersection, with \(K=G\) for \(j=0\). By irredundancy there is \(x\) outside their union, and the coset \(xK\) is disjoint from each selected subgroup: \(xk\in H\) with \(k\in K\subseteq H\) would imply \(x\in H\). The remaining \(n-j\) subgroups cover \(xK\), so some remaining \(H\) meets it in at least \(|K|/(n-j)\) elements. If \(y\in H\cap xK\), then \(H\cap xK=y(H\cap K)\); thus \([K:K\cap H]\le n-j\). Select \(H\) next. Multiplying the index bounds along the chain proves that the full intersection has index at most \(n!\).

Applying this bound to \(C\) yields \(\operatorname{Vol}_{\mathbb Z}(\Delta)=|C|\le n!\). To see finiteness, put \(B=n!\). Every coordinate of every group \(C\) of order at most \(B\) is killed by \(\operatorname{lcm}(1,\dots,B)\), so such coordinate groups are subgroups of a single finite group. The ordered coordinate group determines the simplex up to affine unimodular equivalence: if \(A'\) is another lifted vertex matrix with the same \(C\), then equality of the full preimages \(A^{-1}\mathbb Z^n=A'^{-1}\mathbb Z^n\) implies \(A'A^{-1}\in\mathrm{GL}_n(\mathbb Z)\). Its last row is \((0,\ldots,0,1)\), since it sends each lifted vertex to the corresponding lifted vertex and both have last coordinate 1. Thus its action at height one is affine unimodular. This proves the second assertion.

## Spanning simplices and free joins

A lattice simplex is *spanning* if the differences from one lattice point of the simplex to all its lattice points generate the ambient lattice. A *free join* of two lattice polytopes \(P\subset\mathbb{R}^a\), \(Q\subset\mathbb{R}^b\) is
\[
\operatorname{conv}\big((P,0,0)\cup(0,Q,1)\big)\subset\mathbb{R}^{a+b+1}
\]
in the direct-sum product lattice, up to affine unimodular equivalence; point factors are allowed.

Every spanning lattice simplex of width one is a free join. To see this, choose an affine integral form realizing width one and normalized to take vertex values 0 and 1. Its two extremal faces \(F_0,F_1\) contain all the lattice points of the simplex, because the form is integer-valued. Choose vertices \(p_i\in F_i\), and let \(L_i\) be the subgroup generated by differences \(u-p_i\) with \(u\in F_i\cap\mathbb Z^d\). The vertices of a simplex are affinely independent, so the two face directions and the line \(\mathbb R(p_1-p_0)\) form a direct sum of \(\mathbb R^d\): bases are obtained from the edge differences within each vertex block and the one difference between the chosen vertices. Since the simplex is spanning, the same generators from all lattice points give
\[
\mathbb Z^d=L_0\oplus L_1\oplus\mathbb Z(p_1-p_0).
\]
Translate by \(-p_0\) and use bases of the two groups \(L_i\), together with \(p_1-p_0\), as coordinates. The faces then occupy exactly the free-join normal form, proving the claim.

Consequently a spanning thin simplex that is not a free join has width at least two. The volume bound proves finiteness in each fixed dimension, and the odd-dimensional theorem rules out such examples in odd dimensions. These are the two answers to Question 1.4.

## Related work

Kurylenko’s [§2](https://arxiv.org/html/2404.03975v2#S2) supplies the modular barycentric model and its thinness and width criteria. Equation (1) is the identity coefficient of the vanishing group-ring product \(\prod_{i\in J}([1]-[\chi_i])\). The corresponding Fourier-product/cover method for finite-field hyperplanes appears, for instance, in Nagy, Pach and Tomon, [*Additive bases, coset covers, and non-vanishing linear maps*, Lemma 4.2](https://arxiv.org/html/2111.13658v1#S4.Lemlem2). Their Theorem 1.2 also supplies the sharper asymptotic volume bound \(\exp(O(d\log\log d))\) by applying its abelian-group cover bound to the coordinate kernels. Neither of the main arguments above depends on that theorem.

## Scope checks

- The ambient lattice is the one used to define width; the first two assertions do not require spanning. Neither proof assumes prime exponent or a squarefree normalized volume.
- The bound concerns *simplices* of width at least two. It does not assert a bound for width-one thin simplices, or settle analogous questions for arbitrary polytopes.
- Parity is necessary in part 1: for even \(d\ge2\), twice the unimodular \(d\)-simplex is thin and has width 2. For this example the barycentric coordinates are 0 or 1/2 with an even number of half-coordinates, so the all-nonzero vector cannot occur when \(d+1\) is odd. Every nonzero integral form takes values on the vertices that are all even, and a coordinate form attains width 2.
- We do not use the exponential bound claimed in arXiv:2205.03389; that preprint was withdrawn.
