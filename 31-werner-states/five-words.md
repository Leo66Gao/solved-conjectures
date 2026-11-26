# Five-word local filters for Werner states: all-copy near-endpoint bound and 18 endpoint cores

**Research note by Leo Gao, November 26, 2026. Work developed with AI assistance. Not peer reviewed; priority unconfirmed.**

**What is proved.** At every copy number and in every local dimension, the Werner state \(\rho(d,-t)=(I-tF)/(d^2-td)\) admits no distillability witness with one party supported on **at most five strings in an orthonormal product basis** when \(0\le t\le4979/10000\). At \(t=1/2\), the same five-word problem for all copy numbers reduces to 18 explicit four-copy qutrit supports. These 18 endpoint cases are not solved here. Neither are unrestricted four-copy undistillability and NPT bound entanglement: a Schmidt-rank-two witness may be dense on either party.

**External inputs.** The three-copy endpoint in every dimension is [Tomar, Theorem 1.2](https://hexagonmath.org/2611.00464v1). The four-copy qutrit result at \(t=4979/10000\) is [Theorem 1.4 of the same preprint](https://hexagonmath.org/2611.00464v1). The matrix-entry sector representation is also in [Tomar’s endpoint companion, §4.2](https://hexagonmath.org/2611.00466v1). See [Horodecki, Rudnicki, Życzkowski](https://doi.org/10.1103/PRXQuantum.3.010101) on why distillability matters. We restate the needed parity-deletion result from the earlier research notes below.

## 1. Setup and parity deletion

Write \(\Phi=|\Omega\rangle\langle\Omega|\), where \(\Omega=\sum_a|a,a\rangle\), and \(W_n(t)=(I-t\Phi)^{\otimes n}\) on \(A^n:B^n\). For \(S\subseteq[d]^n\), \(W_{n,S}\) denotes its compression on Alice to the span of the words in \(S\). The distillability criterion asks whether \(W_{n,S}\) has negative expectation on a vector of Schmidt rank at most two, i.e. the vectorization of a matrix \(C\) of rank at most two. Absence of such a vector is called 2-block positivity. It is preserved under local filters and a positive sum of such filtered operators. It is also preserved by tensoring with a separable positive operator: decompose the latter into rank-one product projectors and contract the test vector against each product vector.

Label the \(m\) words \(0,\dots,m-1\). Each site gives a partition \(P_i\) of the labels, whose blocks specify equal symbols. Its binary triangle signature \(\beta_i\) has a component for each \(1\le p<q\le m-1\) recording whether \(0,p,q\) have three distinct symbols there. This signature determines all triangle bits: if \(e_{ab}\) records unequal symbols, the triangle bit for \(a,b,c\) is \(e_{ab}+e_{bc}+e_{ca}\) in \(\mathbb F_2\), and is the sum of the three corresponding bits for triangles through \(0\).

**Parity deletion.** A nonempty set of sites \(I\) with \(\sum_{i\in I}\beta_i=0\) can be deleted without losing a possible negative witness. On the projected code on \(I\), write \(r=t/(1-t)\) and \(K_{xz}=(-r)^{h(x,z)}\), where \(h\) is the Hamming distance. When all triangle parities vanish, the signs factor as \(\epsilon_x\epsilon_z\) (fix a base word), and \(r^{h(x,z)}\) is the principal restriction of a tensor product of \((1-r)I+rJ\). Hence \(K\succeq0\) for \(0\le t\le1/2\).

To see why the entire projected tensor is separable, start with the positive product \(K\otimes J_B\), where \(J_B\) is all ones, and twirl by independent diagonal phases per site and symbol on Alice, with conjugate phases on Bob. This leaves exactly the pairs of entries sharing a **mismatch record**: the set \(O\) where the Alice and Bob symbols differ, with their ordered unequal symbols specified at each such site. Indeed, the phase exponent at a site is the difference of vectors \(e_a-e_b\) attached to the two entry positions; distinct ordered unequal pairs have distinct nonzero vectors. Now for each subset \(T\subseteq I\), sum over the filters given by independent product projections specifying unequal Alice/Bob symbols at each site in \(T\), with weight \(r^{|T|}\). A surviving record \(O\) is multiplied by \((1+r)^{|O|}\). Scaling by \((1-t)^{|I|}\) gives \(W_{|I|,S_I}\) exactly: its entries on record \(O\) are \((1-t)^{|I|-|O|}(-r)^{h(x,z)}\), and zero across different records. This is a separable decomposition. The original Alice support is a subspace of the product of the projected supports on \(I\) and its complement. Thus 2-block positivity on the remaining sites suffices. Iterate until the binary signatures are independent. For five words there can be at most six, and no constant/binary sites or repeated partitions remain.

## 2. Direct certificates by singleton charging

Within a mismatch record \(O\), the compatible rows form \(T=\{x\in S:x|_O=a\}\) for its specified Alice symbols \(a\). The column \(y_x\) is \(x\) outside \(O\) and has the specified Bob symbols on \(O\). The contribution is

\[
w\sum_{x,z\in T}(-r)^{h(x,z)}\overline{C_{x,y_x}}C_{z,y_z},
\qquad w=(1-t)^{n-|O|}.
\]

If every triangle of \(T\) has even parity, that sector is positive semidefinite by the sign-times-PSD argument in §1. Otherwise let \(g=\min_{x\ne z\in T}h(x,z)\), \(D=\sum_x|C_{x,y_x}|^2\), and \(B=\sum_{x\ne z}|C_{x,y_z}|^2\). The submatrix \((C_{x,y_z})\) has rank at most two. After a row-phase adjustment, bounding the trace by the nuclear norm and then applying Cauchy–Schwarz to its two singular values gives \((\sum_x|C_{x,y_x}|)^2\le2(D+B)\). Bounding the off-diagonal coefficients by \(r^g\) gives the sector lower bound \(w[(1-r^g)D-2r^gB]\).

For a cross-entry \((x,y_z)\), its mismatch set \(P\) is \(O\cup D_{xz}\), where \(D_{xz}=\{i:x_i\ne z_i\}\) is disjoint from \(O\). If its sector is a singleton, its weight is \(w(1-t)^{-h(x,z)}\); paying the parent's negative bound requires the fraction \(2r^g(1-t)^{h(x,z)}\). It suffices that every charged entry is a singleton and is charged at most its budget.

The exact verification needs no enumeration over Bob labels. For fixed \(x,P\), a candidate center \(z\ne x\) requires \(D_{xz}\subseteq P\), with parent \(O=P\setminus D_{xz}\) and parent row set the rows agreeing with \(x\) on \(O\). Ignore balanced parents. Check that no other row agrees with \(x\) all along \(P\), or the child is not a singleton. For a given child column \(y\), a candidate center wants \(y_i=z_i\) wherever \(z_i\ne x_i\). A collection of centers is compatible exactly if none of these requests conflict; at unspecified sites in \(P\) one may use any symbol other than \(x_i\). Test the budget for every compatible collection.

A *trifferent* code separates every triple of distinct words at some site. It automatically has the stated certificate: a second child row would agree with \(x\) wherever \(x\ne z\), contradicting trifference of the triple, and two parents for the same child would request the same symbol whenever both differed from \(x\), again contradicting trifference. Each single payment is at most \(2^{1-g}\le1\) for \(t\le1/2\), since \(h\ge g\).

## 3. Fusion of a trifferent block to one site

Take a set \(I\) of at least two sites such that its **distinct projected words** are trifferent. Suppose \(\sum_{i\in I}\beta_i\) equals the signature of one partition \(Q\) of the row labels into at least three classes. Then \(Q\) gives a well-defined class function \(f\) of a projected word: two labels having the same projection cannot be in different \(Q\) classes, since using any third class would create a separating triangle at the replacement but not in \(I\).

Write \(h_I(x,z)\) for the distance of projected words and \(h_Q(x,z)=1_{f(x)\ne f(z)}\). At \(t=1/2\) the following condition holds automatically; at the second ratio we verify it exactly:
\[
G_{xz}=r^{h_I(x,z)-h_Q(x,z)}\succeq0.
\]
Exponents are nonnegative. Equal signatures mean \((-1)^{h_I(x,z)}=\epsilon_x\epsilon_z(-1)^{h_Q(x,z)}\) for some signs. We show that **2-block positivity on the code with \(I\) replaced by \(Q\) implies it on the original code**. The implication must use filters, not tensor products of generic 2-block-positive operators.

Let \(V=(I-t\Phi)/(1-t)\) on the new alphabet. In a nonsingleton original sector with row set \(T\), map Alice's class basis vector \(|a\rangle\) to \(\sum_{x\in T:f(x)=a}|x\rangle\), and Bob's analogously to the sum of \(|y_x\rangle\). Diagonal-phase twirling in those labels with conjugate phases on Bob leaves only the matched-sector entries and the cross-pair diagonals \((x,y_z)\). The matched coefficient is \((-r)^{h_Q(x,z)}\), and the cross diagonal is \((1-t)^{-h_Q(x,z)}\). Multiplying by \(G\) on Alice entrywise, which is a sum of diagonal local filters by Gram factorization, and conjugating by the signs \(\epsilon_x\), turns the matched coefficient into \((-r)^{h_I(x,z)}\) and keeps the cross diagonals (the multiplier has unit diagonal). Scale by the sector weight \(w\). Its cross diagonals use no more than the available \(w(1-t)^{-h_I(x,z)}\), and by trifference they draw only on singleton entries, without shared charges.

Summing these local-filter images of \(V\) over the nonsingleton sectors and filling residual singleton diagonals gives the whole compressed block. For each residual diagonal at \((x,y)\) use a filter on the input diagonal pair \((f(x),f(x))\) sending it to \((x,y)\), scaled to give exactly the residual weight. Thus **all** filters send Alice class \(f(x)\) to projected word \(x\), including residual terms. After tensoring with identity filters on the other sites and recompressing Alice to the original support, only the reduced input code \(\{(f(x|_I),x|_{I^c}):x\in S\}\) contributes. This proves fusion. The new site can use more levels than the original sites, at most five; heterogeneous site dimensions can be embedded into a common local dimension in applying an unrestricted theorem. Identical resulting partitions are then deleted in pairs by §1.

## 4. Exact enumeration and result

Run `python verify_five_words.py 5 5` or `python verify_five_words.py 5 5 4979/10000`. The five-symbol input limit is not a restriction on ambient local dimension: five rows use at most five symbols at any site. The proofs and enumerator do not restrict Bob to Alice's symbols. The standard-library code enumerates partitions by restricted growth strings, uses their signatures to generate linearly independent collections, and canonicalizes by all 120 row permutations. No two partitions in such a collection may coincide, so site order is immaterial. Starting from orbit representatives of the smaller independent sets, add each partition whose signature is outside the span and canonicalize again. Every orbit occurs, because row permutations act invertibly on the triangle signature space (the full triangle bits simply permute).

For each orbit, accept at most three sites by the known theorem, or finish by trifference or the charge certificate. Otherwise try every potentially deletable subset and every possible one-site fusion of a trifferent subset, including exact PSD verification of \(G\) by rational Schur complements. All operations reduce the number of sites. The figures are identical at both ratios:

| Sites | Independent partition-set orbits | Not covered by the rules |
|---:|---:|---:|
| 1 | 4 | 0 |
| 2 | 19 | 0 |
| 3 | 109 | 0 |
| 4 | 589 | 18 |
| 5 | 2600 | 0 |
| 6 | 6997 | 0 |

The two output files list identical 18 codes, each using exactly three local symbols at each site. These are residual cases, **not counterexamples**. To reduce a four-site core in arbitrary local dimension to qutrits, isolate each outside symbol on Bob wherever that symbol does not occur on Alice. Such a site has no coupling to any other Bob symbol because the local nondiagonal term requires a match. Inside the fixed outside-symbol block, Alice's symbol is unchanged by the matrix element as well. Product-basis slicing therefore leaves at most three active sites whenever there is an outside symbol, with Schmidt rank still at most two. The remaining block has three symbols at each site on both parties and is a qutrit four-copy check. It is covered at \(t_*=4979/10000\) by Tomar’s four-copy qutrit bound, and remains unproved here at \(t=1/2\). Support sizes below five can be padded; if the full ambient tensor dimension is below five, the code is already covered by the at-most-three-copy theorem.

For \(t<t_*\), expand \(I-t\Phi=(1-t/t_*)I+(t/t_*)(I-t_*\Phi)\) at each site. Identity sites can be sliced in the two parties’ product bases, yielding witnesses of rank at most two and using at most five projected words. Each summand is nonnegative by the result at \(t_*\).

## 5. Remaining obstruction

Each listed core contains \(0000,0011,1100\). For example, the core \(\{0000,0011,1100,0201,2022\}\) has an unbalanced diagonal triangle from \(0000,1100,2022\), but its potential charged entry with row \(0000\), column \(0011\), shares a sector with the entry of row \(1100\), column \(1111\). Its diagonal contribution is not separately available. Any continuation through this certificate must control correlated weights of nonsingleton sectors or find a different reduction. We found no matching fusion or 18-core reduction in the sources examined, but priority is not independently established.
