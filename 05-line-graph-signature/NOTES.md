# A finite reduction for extremal line-graph signature

## Claim and relevance

Let (G) be a finite connected simple graph and (c=|E(G)|-|V(G)|+1). Write (s(G)) for the signature (positive minus negative inertia indices) of the adjacency of the **line graph** (L(G)). [Paone–Paone, *Line-Graph Signature Beyond the 2-Core*, Conjecture 5.4 and §9 item 8](https://aletheia-technologies.it/en/research/line-graph-signature-beyond-the-2-core/reader/) conjecture
(2s(G)≤ c+1), prove the general upper bound (s(G)≤ c) and matching lower examples (f(c)≥⌊(c+1)/2⌋), and explicitly ask for a finite algorithm at fixed (c), despite the infinite rooted-tree state space.

**Finite reduction.** For every (c≥2) and every such (G), a simple connected (G') of the same cyclomatic number exists with (s(G')≥ s(G)) and at most (19(c-1)) vertices. More specifically, after suppressing the degree-two paths of the 2-core, each kernel edge has four sufficient states, and each branch vertex has one optional leaf. This settles the finiteness aspect of §9 item 8 and yields an exact fixed-parameter algorithm (in (c)) for both comparison to the sharp bound and maximization at fixed (c). It is not a proof of Conjecture 5.4 for all (c).

**Low-cycle cases.** The same reduction proves (f(c)=⌊(c+1)/2⌋) for (0≤ c≤5), and improves the general upper bound to (f(c)≤ c-2) for (c≥4). For c=0,1 this just uses the cited upper bound and lower witnesses: the 3-vertex path has line-graph signature zero, and the 5-cycle is its own line graph with signature one. For (c≥2) the lower bound is the authors' Theorem 5.3.

## 1. Tree-state classification

Put (M(H)=Q(H)-2I), where (Q=D+A) is the signless Laplacian. For connected simple (H) with edges, unsigned incidence (B) satisfies (BB^T=Q(H)) and (B^TB=2I + A(L(H))). The two products have the same nonzero eigenvalues, so
$$
s(H)=\operatorname{sig}M(H)-c(H)+1.
$$

Use Paone–Paone's pendant rooted-tree state. Its matrix (C_T=Q(T)-2I+e_re_r^T) includes the endpoint degree increase at its root (r) from a single bridge to a host vertex. Let (σ=\operatorname{sig}C_T) and (ρ=(C_T^{-1})_{rr}). Child states satisfy
$$
a=k-1-\sum_{i=1}^k ρ_i,\quad
 σ=\sum_i σ_i+\operatorname{sign}(a),\quad ρ=1/a.
$$
For the singleton, ((σ,ρ)=(-1,-1)). The pivots (a) are nonzero by induction: all child responses have odd numerator and denominator in lowest terms, so (a) is a rational of odd numerator and denominator as well. These formulas also follow directly by scalar Schur elimination.

Prove simultaneously:
1. (σ≤0);
2. (σ=0) implies (ρ=1);
3. (σ=-1,ρ<0) implies (ρ=-1).

Indeed, if the sum of child signatures is zero, all child responses are 1 and (a=-1); the resulting state is ((-1,-1)). If the sum is negative, (σ≤0); equality is possible only when the sum is −1 and the pivot is positive. Then just one child has signature −1 and the other responses equal 1, giving (a=-ρ_j); positivity and the third induction clause give (ρ_j=-1), whence (ρ=1). Finally, (σ=-1) with a negative pivot forces the child sum to be zero, which is the first case. This proves the statement the authors observed only finitely in Remark 3.9.

A branch attached at (v) contributes additive signature (σ) and a diagonal update ((1-ρ)e_ve_v^T) on the host. Discard (σ=0) branches, since neither term changes. Discard (σ≤−2) branches, since a rank-one update can raise signature by at most two. For (σ=-1), (ρ≥−1); replace it by a single leaf, which has the same signature cost and an update (2e_ve_v^T) at least as large in positive semidefinite order. This can only increase signature. If multiple leaf updates accumulate at a vertex, all can be removed without decreasing total signature, since their common update has rank one and their cost is at least two. Hence it is enough to put at most one leaf at each 2-core vertex.

## 2. Compressing an arbitrarily long decorated kernel path

For (c≥2), the connected 2-core has some degree at least 3. Retain its (k) vertices of degree at least 3 and suppress the degree-two paths between them. The resulting connected multigraph (K), possibly with loops and parallel edges, has (m=k+c-1) edges and (3k≤2m), hence (k≤2(c-1)) and (m≤3(c-1)). A loop contributes two to the degree and represents a path with the same endpoint twice.

Work with quadratic forms: a signed link of sign (s) contributes (2sxy), also when (x=y). Before any algebraic changes each path has links of sign +1. Its internal diagonal entries are 0 (unmarked) or 2 (the leaf gives a mark); the signature score of this matrix subtracts one for every mark. Every branch vertex starts with diagonal (d_K(v)-2), before its optional mark. Signed links are bookkeeping; all normal forms are realized by ordinary simple graphs below.

**Moving marks.** An adjacent (2,0) pair with link (s=±1), exterior links (p,q=±1), and outside coordinates (x,y) has pivot
$$
U=\begin{pmatrix}2&s\\s&0\end{pmatrix},\quad
U^{-1}=\begin{pmatrix}0&s\\s&-2\end{pmatrix}.
$$
It contributes zero signature. Its Schur complement replaces the three links by ( -2psq xy) and adds (2y^2), i.e. moves the mark to the right exterior coordinate. The reversed (0,2) pattern moves the mark left. If two marks land on the same vertex, discard both, by the rank-one argument above. On a given path apply a (2,0) contraction whenever it has a following internal coordinate. Each step strictly shortens, and eventually all internal marks form a single run preceded by zeros and followed by at most one zero. A run with no marks is simply an unmarked path. An adjacent (0,0) pair can be contracted by the same pivot with both diagonal entries zero; this reverses the link product and imposes no diagonal update. Hence leading unmarked runs can be reduced to length at most one.

**Shrinking a run.** A marked run of (r≥1) consecutive internals is a signed version of (2I+A(P_r)), positive definite with signature (r). This cancels its (r) mark costs. Its inverse has endpoint diagonals (r/(r+1)) and corner entry ((-1)^{r-1}/(r+1)) up to edge and boundary signs. These formulas follow from the path determinant recurrence (d_r=2d_{r-1}-d_{r-2}=r+1) and the endpoint cofactors. Consequently its Schur correction on the two exterior ports is the negative of
$$
R_r(s)=\frac{1}{r+1}\begin{pmatrix}r&s\\s&r\end{pmatrix},\qquad s\in\{-1,1\}.
$$
For (r=1) this is the outer product on the one internal vertex coupled to both ports; the formula still holds. Replacing the run by one marked vertex with port sign chosen to keep (s) gives (R_1(s)); (R_r(s)-R_1(s)) is positive semidefinite, with eigenvalues (0,(r-1)/(r+1)). This remains true after identifying the two ports in the loop case. Thus shortening the run does not lower signature score. If the remaining mark is adjacent to an internal zero, contract that (0,2) or (2,0) pair, moving the mark to the nearest branch vertex. This leaves at most one unmarked internal. If the mark is the only internal, its effective quadratic term is (-(x+sy)^2/2), with net additive signature zero after mark cost. Replace it by a signed direct link with term (-2sxy). The difference is ((x-sy)^2/2≥0), again including loops.

Thus each kernel edge can be taken in only four states: a direct signed link (2sxy), or one internal unmarked zero variable (z) coupled by (2z(x+sy)), for (s=±1). All remaining marks lie at branch vertices, with at most one per vertex. These comparisons remain valid throughout because a Schur complement is an exact congruence and each positive semidefinite improvement is an update on the entire remaining matrix, even with other paths still present.

**Return to graphs.** For each compressed edge choose signed external and internal links realizing the state's sign product. Insert two fresh unmarked vertices on a negatively signed link and replace all three new links by +1: eliminating the two inserted vertices yields the negative link and zero signature. A positively signed link can be replaced by length five without effect (two such balanced eliminations). Gauge the signs of any remaining internals so all other links are positive. Lengthen if needed so each physical path has at least three edges, which ensures simplicity even at loops and parallel edges. For a direct state the required length is at most five; for a one-internal state it is at most six, since at most one link need be negative by choice of representation. All new vertices are private to their individual paths. Each branch vertex may acquire its own new leaf. This gives a connected simple graph with at most (2k+5m≤19(c-1)) vertices, unchanged cyclomatic number and the resulting signature score.

## 3. Small exact matrix and (f(c)) through five

Let (P) be the branch-vertex matrix with its degree-minus-two diagonal, the marked (+2) diagonal entries and all direct signed links. A loop is the diagonal increment (2s). Each one-internal state gives a zero block with row of couplings (x_u+sx_v) in a matrix (B). The block matrix is
$$
\begin{pmatrix}P&B^T\\B&0\end{pmatrix}.
$$
Its signature equals that of the restriction of (P) to (\ker B). To verify, split the branch variables into (\ker B) and a complement, and the internal variables into ({\rm im}\,B) and a complement. The full-rank coupling between the two complements of the kernels gives a balanced block (\left(\begin{smallmatrix}P_1&W^T\\W&0\end{smallmatrix}\right)), whose inverse has zero branch-branch block and whose signature is zero. Extra internal directions are null. Eliminating this block leaves the stated restriction. One may take a signed-component basis of (\ker B), since its equations identify pairs of coordinates up to sign or force a component to vanish. Therefore all calculations can use integer matrices and exact congruence. For (l) marks,
$$
s(G')=\operatorname{sig}(P|_{\ker B})-l-c+1≤ k-c+1≤ c-1.
$$
These estimates give the desired maxima at (c=2,3) from the published lower examples.

When (c≥4), equality (s(G')=c-1) above would require all of (k=2c-2) (so the kernel is cubic), (l=0), no nontrivial constraint, and (P) positive definite. We show no such connected kernel exists on more than four vertices. A loop vertex has only one nonloop incidence; an unlooped vertex has diagonal 1. Every nonloop edge must be a direct link, as any one-internal state on different endpoints gives a nontrivial constraint. Between unlooped vertices the offdiagonal is an integer; their (2\times2) principal minor has determinant (1-a^2), requiring (a=0). Thus direct links between them must be oppositely signed parallel pairs. Each unlooped vertex belongs to at most one such pair. An unlooped vertex outside a pair has three loop neighbors of nonloop degree one; connectedness would imply the entire kernel has four vertices. A parallel pair has two remaining exterior ports; neither can lead to a different unlooped vertex (would require another parallel pair, or a nonzero entry). A third direct edge between the pair vertices cannot cancel. Its exterior ports therefore go to loop vertices, making the whole connected graph of size at most four again. A graph consisting only of loop vertices has nonloop degree one everywhere, hence order at most two. This excludes positive definiteness at (k≥6) and gives (f(c)≤ c-2). It is sharp at (c=4,5) by the published lower bound.

## 4. Exact algorithm and limits

For fixed (c≥2), enumerate connected multigraph kernels with (k≤2(c-1)), (m=k+c-1), minimum degree three (loops counted twice). For every kernel enumerate its four states per edge and two states per branch vertex. Compute the integer signature of the matrix compressed to the constraint kernel, subtract mark costs and (c-1), and maximize. Enumeration may be done even on labeled kernels; quotienting by isomorphism is not needed for coverage. There are at most (O(c²))^(3c−3) labeled edge multisets to try, and at most 4^(3c−3) · 2^(2c−2) decorations for each. The signed-component compression has an integer basis with entries in {−1,0,1}; its matrix has order O(c) and entries O(c), and exact inertia takes polynomial bit complexity by fraction-free symmetric elimination or characteristic-polynomial root counting. Thus the maximization takes 2^(O(c log c)) bit operations. For an even simpler finite (but slower) implementation, one can directly test all connected simple graphs through 19(c−1) vertices. The theorem also implies that any counterexample of cyclomatic number (c) has a counterexample of the stated linear order, and that finite testing need not sample large pendant trees.

The separate [exact computation](COMPUTATION.md) verifies the conjecture over every input of cyclomatic number 6 or 7, by an exhaustive check of all relevant normal forms. Thus f(6)=3 and f(7)=4, using the same published lower constructions. The proof and finite computation do not establish the conjecture for c≥8. The general upper bound must still be tightened from c−2 to ⌊(c+1)/2⌋ or a counterexample found. The finite reduction narrows the obstruction to signed kernel inertia rather than arbitrary rooted-tree responses. Nov. 26, 2026 search did not locate previous statements of this finite reduction; the cited source itself poses the finite-state problem, and the August follow-up treats only specific families. This is not a claim of exhaustive novelty review or peer verification.

## Related negative lead

The TxGraffiti annihilation–residue inequality proof was independently rediscovered but is already published by [Gupta](https://arxiv.org/abs/2606.29553), with an independent approach in [Kadrawi–Levit](https://arxiv.org/abs/2607.01438). It is not a result of this investigation.
