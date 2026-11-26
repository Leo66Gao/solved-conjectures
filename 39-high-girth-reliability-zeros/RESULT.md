# Reliability zeros in maximally connected, high-girth regular bipartite graphs

**Theorem.** Each point of the closed complex unit disk is the limit of zeros of all-terminal edge-reliability polynomials of finite simple bipartite graphs whose regular degree and girth both tend to infinity, and whose vertex connectivity and edge connectivity both equal their degree. For every point of the interval [−1,0] the approximating zeros can be taken real. Here the variable is the probability that an edge *fails*. The claim about the complex disk is inclusion, not exclusion of other limit points.

**Stronger root count.** For a fixed target radius r, one graph has a ring of k=d/2 simple innermost zeros, an exponentially accurate regular polygon radially separated from every other zero. See INNER-ZEROS.md or Section 5 of the typeset note for the exact bound and proof.

**Context.** Brown–Colbourn proved density for multigraphs. Brown–McMullin asked for the real analogue for simple graphs. This has already been proved by Omar, and Buys proved both real and complex density for simple graphs. In particular, the conjecture for unrestricted simple graphs is NOT open. Buys uses cycles with a complete two-terminal graph in place of each edge; the resulting graphs have bounded vertex connectivity and triangles. Our graphs are cyclic covers built with many disjoint attachment vertices instead. The proof controls defective component partitions as complex weights, not as positive probabilities. This manuscript's strengthening is not independently refereed; see SOURCES.md. 

## 1. Blocks and covers

Take a sequence of connected, simple, bipartite, d-regular graphs X on n vertices with
(i) d=2 mod 4 tending to infinity; (ii) log n=o(d); (iii) girth tending to infinity; (iv) second-largest adjacency eigenvalue at most 2 sqrt(d−1). Here and below all estimates are for sufficiently large d. Such a sequence follows from Lubotzky–Phillips–Sarnak, Theorems 3.4 and 4.1: let primes p=1 mod 4 tend to infinity and choose a prime Q=1 mod 4 in [exp(sqrt p),2exp(sqrt p)], which exists eventually by the prime number theorem for the fixed progression 1 mod 4. The LPS graph has d=p+1, at most Q³ vertices, and girth at least 2 log_p Q for these sizes. If it is not bipartite, take its bipartite double cover, which is connected, has adjacency eigenvalues ± those of the original, and does not decrease girth. In particular n is much larger than d. The usual spectral bound (apply dI−A to the centered indicator of U) gives at least (d−2 sqrt(d−1)) |U|(1−|U|/n) edges out of U.

Write k=d/2, an odd integer. Choose k edges of a matching of X (a perfect matching exists by Hall's theorem); label them a_i b_i, a_i left, b_i right. Delete these edges to get H, the internal block. Its minimum degree is d−1, and **every set of u≤n/2 vertices has at least du/4 edges to its complement**, since the matching deletion costs at most u edges.

For m≥3, take copies H_j indexed cyclically mod m. Restore the deleted edges with a shift: connect a_i in H_j to b_i in H_(j+1), for every i and j. Denote this graph by G. It is a simple d-regular bipartite graph, and its projection to X is a covering map (locally bijective on incident edges), so its girth is at least that of X. Each vertex belongs to at most one interblock edge in the entire graph.

**Connectivity.** After removal of ≤d−1 vertices in one block, every remaining component T of H having size u≤n/2 is a singleton, if there is any such component. Indeed, its edge boundary lies in the removed set S, so du/4≤d|S| and u≤4d. There are no 4-cycles, so two distinct members of T have at most one common neighbor. With N(T) the open neighborhood union (possibly meeting T), counting incidences and applying Cauchy–Schwarz gives
|N(T)| ≥ (d−1)²u/(d+u−1):
the sum of the neighbor multiplicities is ≥(d−1)u, and the sum of their squares is ≤du+u(u−1). Thus the exterior neighborhood has size ≥f(u)=u[(d−1)²/(d+u−1)−1]. This is concave in u, and f(2), f(4d)>d−1 for all sufficiently large d. Hence 2≤u≤4d is impossible. Any singleton component has degree d−1 in H and uses the whole deletion budget for its neighbors. Two such singleton components would have d−1 common neighbors, again impossible. As n≫d, if disconnection occurs there is one isolated port and one component containing all other surviving vertices.

Now remove fewer than d vertices in the whole G. If all surviving blocks are connected, at most one of the m interfaces can be destroyed: each contains k disjoint edges and distinct interfaces have disjoint endpoints. The cyclic chain remains connected. Otherwise all d−1 deletions occur in one block, isolating a single port x there. The external edge from x survives. All deleted neighbors are in the opposite bipartition class from x. At least one of the other k−1 ports of the same color as x therefore remains in the large component and has an intact external edge. The other m−1 blocks form a connected path. This proves vertex connectivity ≥d, and consequently κ(G)=λ(G)=d.

## 2. A component-partition estimate for a complex failure probability

Write z for the failure variable and R for all-terminal reliability, extended polynomially to complex z. For a set partition π of V(H), let w_π(z) be the sum of edge-configuration weights yielding exactly the component partition π. Let 1 denote the one-block partition, and u(π) the number of vertices outside a largest part. For every fixed L≥1 and 0<ρ<1, we claim that, uniformly for |z|≤ρ,
    
    δ = sum_(π≠1) |w_π(z)| L^u(π) = o(ρ^(3d/4)).                 (1)

For a partition σ let D(σ) count crossing edges. All crossing edges fail exactly when the actual component partition refines σ. Möbius inversion therefore gives w_π=Σ_(σ≤π) μ(σ,π) z^D(σ). For u=u(σ)>0 there are at most n^(2u) choices of σ: choose the exceptional u vertices, then partition them. There are at most (u+1)^(u+1)≤n^(2u) coarsenings π, each with |μ(σ,π)|≤u!≤n^u by the partition-lattice Möbius formula, and u(π)≤u.

Every part except a largest one has size ≤n/2, so summing its boundary gives D(σ)≥du/8. For u≤7, the cut between the exceptional u vertices and the largest part alone has size ≥(d−1)u−u(u−1)=u(d−u), by simplicity. Together these bounds give, for all u≥1 and large d,
    
    D(σ) ≥ 3d/4 + du/32.

Hence δ≤ρ^(3d/4) Σ_(u≥1)(L n^5 ρ^(d/32))^u. Since log n=o(d), the series is o(1). This proves (1). Also, Σ_π w_π=1 implies |w_1−1|≤δ.

## 3. Why exponentially many blocks can still be replaced by single vertices

Condition polynomially on the exact partitions π_j of the m blocks. Here “condition” means first sum edge weights with each prescribed partition, then independently sum the remaining interblock edge weights; no positivity at complex z is assumed. If all π_j=1, the quotient is a cycle, with k parallel edges per interface. Its reliability, with x=z^k, is
    
    Q_m(x)=(1−x)^m+m x(1−x)^(m−1).

This term in the full calculation has coefficient w_1^m. We bound all other terms. Fix a vector of partitions and mark one largest part in each. An interblock edge is called exceptional if it meets a vertex outside these marked parts. There are at most U=Σ_j u(π_j) exceptional edges since interblock edges form a matching. An interface containing at least one exceptional edge is called dirty; there are at most U such interfaces.

Sum each exceptional edge individually in absolute value; this costs at most (|z|+|1−z|)^U≤3^U for |z|≤1. At a dirty interface, the remaining h ordinary edges all join the same pair of marked parts and only the binary status “at least one survives” matters to connectivity. Summing the absolute values of its two weights costs at most |1−z^h|+|z|^h≤3 (also valid if h=0). At every clean interface the corresponding two weights are 1−x and x. No connected configuration can have two distinct clean interfaces with all edges down: cutting the cycle in two places separates whole groups of blocks irrespective of states elsewhere. Consequently for |z|<1 the absolute value of the interblock sum is at most
    
    (1+m|x|) exp(m|x|) 9^U.                                     (2)

Indeed the contributions with zero or one failed clean interface are bounded using |1−x|≤1+|x|. For m|x| bounded write B for a uniform bound on the first two factors of (2). With (1) at L=9, the error made by retaining only the all-connected block partitions satisfies
    
    |R_G(z)−w_1^m Q_m(x)| ≤ B [ (|w_1|+δ)^m−|w_1|^m ].

It tends to zero uniformly whenever mδ→0 and m|z|^k stays bounded. Under the same conditions w_1^m→1 and Q_m(x) stays bounded, so R_G(z)=Q_m(z^k)+o(1).

## 4. Locating complex and real zeros

Fix any target z_* of modulus r∈(0,1). Set m−1 to a nearest integer to r^(−k); choose a k-th root ζ of −1/(m−1) with argument nearest arg z_*. Then ζ→z_*. For a real negative target choose ζ negative, which is possible because k is odd. Put z=ζ exp(w/k) for |w|≤1/2, and fix ρ with r<ρ<r^(2/3). Uniformly there |z|≤ρ eventually, m|z|^k is bounded, and mδ=o(r^(−d/2)ρ^(3d/4))→0. Since (m−1)z^k=−exp(w), Section 3 proves uniform convergence
    
    R_G(ζ exp(w/k)) → exp(exp(w)) [1−exp(w)].

The limiting holomorphic function has exactly one zero, simple and at w=0, in |w|≤1/2. Rouché's theorem therefore supplies exactly one zero inside the circle for all sufficiently large d; its z-value tends to z_*. For a negative target, conjugation preserves the function's zero set in this circle, so uniqueness makes this zero real. Endpoints and the unit circle follow by a diagonal choice of interior targets, increasing degrees and girths at each stage. This proves the theorem. 

The real closure is therefore exactly [−1,0]∪{1}, by the general real-root exclusion of Brown and Colbourn and the trivial root at 1. No assertion of a fixed-degree density theorem is implied. These witness graphs need not be expanders: consecutive large sets of blocks have small edge boundary compared to their volume.

**Probabilistic corollary (same graph sequence).** At a real physical failure rate z=r with m r^k→c in (0,∞), the number of connected components converges in distribution to max(1,Y), where Y is Poisson with mean c. Indeed (1) and a union bound show all internal blocks are connected with probability tending to 1. The number of entirely failed interfaces is exactly Binomial(m,r^k), because their edge sets are disjoint. On the all-internally-connected event the component count of the cyclic quotient is the larger of 1 and this count. In particular connectivity tends to (1+c) exp(−c). Despite full vertex connectivity, it is not isolated vertices that determine this limit. 
