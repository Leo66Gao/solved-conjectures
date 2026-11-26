# The highest 2k+3 connected graphs

The tree theorem extends to a complete ordered list of the first two groups among **all finite connected simple graphs**. Graphs admitting no vertex set with exactly k induced edges are omitted (equivalently assign them mean zero).

For n≥2r+1, let W(n,r,t), 0≤t≤r, have a hub w, m=n−2r−1 pendant leaves adjacent to w, and r disjoint pairs of further vertices, with one edge inside each pair. Join w to **both** ends of t pairs, and to **one** end of each remaining pair. Thus W(n,r,0)=S(n,r).

**Theorem.** For k≥1 and n≥18k+3, the top 2k+3 isomorphism types, in strictly decreasing order of the mean size a_k of a vertex subset inducing exactly k edges, are

    W(n,k,k), W(n,k,k−1), …, W(n,k,0),
    W(n,k+1,k+1), W(n,k+1,k), …, W(n,k+1,0).

Every unlisted graph has mean at most U−1/2 for U=(n+2k−1)/2. The first group converges to U and the second to U−1/3 with the uniform error bound given below. In particular the leading graph consists of k triangles meeting at the hub and n−2k−1 pendant vertices. The restricted tree rankings follow by taking t=0.

**Proof of the two groups.** Equation (1) of [the tree proof](RESULT.md) and its independent-set deficit bounds hold for every connected graph. When the integer term is zero, the support H consists of k distinct pairs, whose only outside neighbor is w. Each pair must attach to w via one or both ends. No vertices of the residual F are adjacent to H. Every component of F must touch w. Thus an edgeless F forces G=W(n,k,t) for some t; an F with just one edge forces G=W(n,k+1,t). All other fibers lose at least 1/2. Consequently graphs outside the first group lose at least 1/3, and outside both groups at least 1/2.

As in the tree case, with w absent there are A=binom(r,k)3^(r−k)2^m configurations of mean L=U−(r−k)/3. With w present use the edge-count polynomials ordinary O(x)=2+x+x² and triangular J(x)=1+2x+x³. The latter counts neither end, either end, or both ends of a triangular pair. The number of such configurations is

    C_t = [x^k] (1+x)^m O(x)^(r−t) J(x)^t.

Both polynomials are less than 9/4 at 1/8, so the same estimate gives

    n C_t/A ≤ n (9/4)18^k(9/16)^m < 1/6.

In particular each member's mean lies within 1/6 of its group limit L, and at or below L by the structural cap. The two groups therefore strictly separate, and strictly precede every excluded graph. Their types are distinct: the hub is the unique vertex of degree greater than two under these parameter restrictions, and deleting it recovers r, while the triangle count recovers t.

**Ordering within a group.** Compare replacing one ordinary pair with a triangular pair. Collect the factors of all other pairs and the leaves into H(x)=(1+x)^m Q(x), with Q having nonnegative coefficients, and write h_j=[x^j]H, h_j=0 for j<0. For 1≤j≤k the binomial ratio bound gives

    h_(j−1) ≤ [j/(m−j+1)] h_j ≤ h_j/15.

Indeed convolve Q with binomial(m,i−1)≤[j/(m−j+1)]binomial(m,i) for 0≤i≤j, setting out-of-range coefficients to zero. Here m≥16k. Consequently

    C_t ≥ 2h_k,
    C_(t+1) = h_k+2h_(k−1)+h_(k−3) ≤ (1+2/15+1/15³)h_k < (8/7)h_k,

so C_t/C_(t+1)>7/4. The mean conditional on w present is B_t≤2k+2: selected neighbors of w contribute at least one edge apiece and hence number at most k; at most r≤k+1 non-neighbors exist, namely the remote ends of ordinary pairs. Also L≥10k. The loss D_t=L−a_k(W(n,r,t)) is (L−B_t)C_t/(A+C_t), strictly positive. From B_t≥0, n≥21 and the bounds just established,

    D_t/D_(t+1)
      ≥ [(L−2k−2)/L] [C_t/C_(t+1)] [A/(A+C_t)]
      > (3/5)(7/4)/(1+1/(6n)) > 1.

This proves strict increase with t and completes the classification.

**Checks.** Run `python3 verify_connected.py` with [verify.py](verify.py) in the same directory. This verifies the connected structural trichotomy on all connected labeled graphs up to six vertices and checks the candidate polynomial and both group orderings independently. The proof, not this sample, covers all n,k. The Dossou-Olory–Andriantiana paper determines the unrestricted graph optimum for k=1, attained by one edge plus isolated vertices; that graph is not connected for n>2. Its tree conjecture is the separate all-orders result in [RESULT.md](RESULT.md).

## The connected maximizer for one edge, with no size restriction

**Corollary.** For every n≥7 the unique connected n-vertex maximizer of a_1 is a star with one extra edge between two leaves, W(n,1,1). For n=4 and 5 the unique maximizer is instead the tree S(n,1); at n=6 the maximizers are the trees S(6,1) and S(6,2). For n=2 the edge is the sole choice, and both connected graphs of order 3 tie.

Put m=n−3. The top structural family has two graphs W(n,1,0) and W(n,1,1). With hub absent both have 2^m configurations of mean U=2+m/2. With hub present the triangular graph has m+2 configurations, all of size 2. In the tree the 2m+1 configurations contribute total size 5m+2. Thus the losses from U in the tree and triangle, respectively, are

    m(2m−1)/[2(2^m+2m+1)] and m(m+2)/[2(2^m+m+2)].

The tree loss is bigger precisely when (m−3)2^m>2m+4 (for m>0), true for every m≥4. The tree already exceeds U−1/3 for n≥10, so the triangle is the unique maximizer there. For n=8,9 the triangle has means 158/39 and 14/3, both above the U−1/2 cap on graphs outside the two structural families. Directly comparing the five candidates at those orders gives strict victory; the five respective values in order (r,t)=(1,0),(1,1),(2,0),(2,1),(2,2) are

    n=8: 171/43, 158/39, 123/32, 227/59, 214/55;
    n=9: 32/7, 14/3, 253/58, 480/109, 58/13.

For n≤7, the small finite check in [connected_small.py](connected_small.py) enumerates 1,2,6,21,112,853 connected graph types for n=2,…,7. It starts with a single vertex and adds a vertex with each possible nonempty neighborhood. This reaches every connected graph because a leaf of any spanning tree can be deleted without disconnecting it. The isomorphism code refines degree classes by neighbor-color multisets, orders the classes canonically by their signatures, and minimizes an adjacency bit string over all permutations within final classes. Isomorphic graphs have the same code; conversely an equal bit string gives an isomorphism. The program counts subsets directly; [full output](connected-small-checks.txt) gives the maximizing adjacency lists. In particular at n=7 the unique maximum is 38/11, achieved by W(7,1,1). This proves the corollary.
