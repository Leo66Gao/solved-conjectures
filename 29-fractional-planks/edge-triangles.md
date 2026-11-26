# The sharp fractional plank inequality for every packed triangle in three coordinates
**Leo Gao · AI-assisted research note.** Partial result on Aharoni–Holzman–Krivelevich–Meshulam Conjecture 3.4. Priority has not been independently established. The proof applies to every packed triangle, not to every packed planar or spatial convex set.

**Main theorem.** Every triangle in the unit three-cube meeting the six facets has fractional plank covering number at least 2/3. The constant is sharp on the coordinate simplex.

**Inscribed-triangle lemma.** Write the three coordinates of each vertex of a triangle in the unit cube. Suppose each coordinate attains both 0 and 1, and that the median vertex in each coordinate can be assigned so that the three assigned vertices are distinct. Then the triangle contains a (possibly degenerate) subtriangle supporting a probability uniform on an interval of length at least 2/3 in each coordinate. Consequently every fractional plank cover has cost at least 2/3. The constant is sharp on the coordinate simplex. With no tied vertex coordinates the constructed common width is strictly greater than 2/3.

**Proof.** Label the vertices so that vertex i is a median for coordinate i; reflect each coordinate independently to write the vertices as (a,0,1), (1,b,0), (0,1,c), respectively, with parameters in [0,1]. Use barycentric coordinates in the abstract parameter simplex; its affine map to the physical triangle is denoted L. First take the parameters in (0,1). Introduce
$$
 \alpha=1-b+bc,\qquad \beta=1-a+ab,\qquad \gamma=1-c+ca.
$$
Within the barycentric sum-zero plane choose directions
$$
 d_1=(1,-a,-(1-a)),\quad d_2=(-(1-b),1,-b),\quad d_3=(-c,-(1-c),1).
$$
The columns of the matrix of their physical coordinate increments under L are
$$
 \begin{pmatrix}0&\beta&-\gamma\\-\beta&0&\alpha\\\gamma&-\alpha&0\end{pmatrix}.
$$
In particular the columns have positive dependence with coefficients (alpha,gamma,beta). The parameter directions also satisfy the same dependence, by direct multiplication (or injectivity of L on the barycentric plane; the displayed matrix has rank two).

Set
$$
 u=(\beta+\gamma-\alpha)/(2\beta\gamma),\quad
 v=(\alpha+\beta-\gamma)/(2\alpha\beta),\quad
 w=(\alpha+\gamma-\beta)/(2\alpha\gamma).
$$
These are positive. Moreover
$$
 M=\max((1-b)v,cw)+\max(au,(1-c)w)+\max((1-a)u,bv)<3/2.\tag{1}
$$
A reproducible exact polynomial proof is given below. Choose t=1/M (>2/3) and choose a barycentric point m whose three coordinates are t times the three maxima in (1), respectively. These numbers are nonnegative and sum to 1. The three parameter points
$$
 s_1=m+tu d_1,\qquad s_2=m+tv d_2,\qquad s_3=m+tw d_3
$$
have nonnegative barycentric coordinates by construction, and their coordinates sum to 1. Their convex hull contains m since the scaled directions have a positive dependence. In coordinate j, L(s_j) has value L(m)_j and the other two vertices lie on opposite sides. All three projection lengths are t: one checks beta v+gamma w=beta u+alpha w=gamma u+alpha v=1.

Let q_i be the barycentric coefficients of m relative to the s_i. Put mass q_i uniformly on the edge opposite L(s_i). To see uniformity, in a single projection normalize the vertex values to 0,h,1. Denote the corresponding weights q_0,q_h,q_1. Since m is the median level, q_1+h q_h=h. The projected density below h is q_h+q_1/h=1 and above h is q_h+q_0/(1-h)=1. Thus this probability has marginal densities at most 3/2 in original coordinates. The claimed covering result follows by integrating the cover. At boundary parameters approximate by interior triples. Extract convergent subsequences of the three vertices, their weights, interval endpoints, and lengths (all bounded). Their weighted edge laws converge weakly: each edge is the image of [0,1] by a linear interpolation of its ends, even when they coincide. The limit is supported on the limiting subtriangle and each marginal remains uniform on a limiting interval of length at least 2/3. On the standard simplex the cover f_j(x)=(2/3-x)_+ costs 2/3, proving sharpness.

**Exact check of (1).** In the accompanying short program distinct_verify.py, the aliases A,B,C mean alpha,gamma,beta. Multiplication by the positive factor 2 alpha beta gamma clears denominators, and (U,V,W) represent (u,v,w) times this factor. The three numerator polynomials and the eight strict inequalities obtained by independently selecting a summand in each maximum have the following certificates. For a polynomial P with coordinate degrees (d,e,f), form its pullback by (a,b,c)=(x/(1+x),y/(1+y),z/(1+z)), then multiply by (1+x)^d(1+y)^e(1+z)^f. The program expands this in the monomial basis by integer arithmetic. Every listed polynomial is nonzero with only nonnegative coefficients (smallest nonzero coefficient 1; respectively 10,10,10,17,17,14,17,17,14,17,17 monomials). It is strictly positive for x,y,z>0, proving exactly the domain needed. No numeric solver or sampling enters this proof.

**Completion for all triangles.** Assign an arbitrary median vertex to each coordinate, breaking ties arbitrarily. When the assignments are a permutation of the three vertices, the lemma applies. Otherwise at least one vertex was never assigned a median. Its value in each coordinate must be 0 or 1: an unassigned strictly intermediate value would be the unique median there, as the projection includes both 0 and 1. Thus the triangle contains a cube vertex. After independent reflections suppose that vertex is 0. The following positive-chord argument, a special case of the prior signed-chord criterion, completes the proof. Notably, a previous two-coincident-median example rules out using a single triangle supporting full uniform projections of width ≥2/3 in that entire case; this second argument is needed.

**Positive-chord lemma.** If K is convex, contains 0, and meets the x_i=1 facets, then every ordinary measurable coordinate-plank cover of K has cost at least one. Fix p_i in K with coordinate i equal to 1 and all coordinates nonnegative. We may reason on the compact hull of 0 and all p_i. Were the total cost less than 1, take open supersets of the forbidden coordinate sets with total lengths still less than 1. Express these as disjoint open intervals per coordinate and take a finite subcover by compactness. Intervals may be taken in the real line with total length <1, by outer regularity before restricting to the cube.

Write these intervals (a_k,b_k) in coordinates i(k), choose L_k>b_k-a_k with sum L_k<1, and for a binary vector s set x(s)=sum_k L_k s_k p_{i(k)}. This point lies in K by convexity, with remaining weight at 0. Define an update T_k(s)=1 if the i(k)th coordinate of sum_{l≠k} L_l s_l p_{i(l)} is ≥a_k and T_k(s)=0 otherwise. The map T is order preserving since every entry of p_j is nonnegative. Iterating T from the all-zero vector produces a nondecreasing sequence stabilizing at a fixed point s. When s_k=0 the corresponding coordinate of x(s) is <a_k, and when s_k=1 it is ≥a_k+L_k>b_k. This point evades every interval, a contradiction.

Finally, in three coordinates let U be uniform on [0,1], V=(U+1/2) mod 1, and W=3/2-U-V. W is uniform on [0,1], mapping each half interval linearly onto the full interval. Thus Y=(2/3)(U,V,W) sums to one and has each marginal uniform on [0,2/3]. For any fractional cover f_i and any such Y, the sets {t:f_i(t)≥Y_i} are an ordinary coordinate cover, hence have total length at least 1. Averaging gives 1≤(3/2) sum_i int min(f_i,2/3)≤(3/2) sum_i int f_i. This is the standard AHKM rounding, included for completeness. In addition to the triangles in the theorem, monotonicity gives the same bound for any packed K containing a packed triangle.

**Sources and status.** See [Aharoni–Holzman–Krivelevich–Meshulam, Fractional Planks (2002), Conjecture 3.4](https://doi.org/10.1007/s00454-001-0088-x) and [Brass–Moser–Pach, Research Problems in Discrete Geometry, §3.4](https://doi.org/10.1007/0-387-29929-7). This theorem concerns measurable fractional coordinate planks, not the ordinary affine plank theorem for three strips. It neither proves the fractional conjecture for all planar bodies nor follows from the earlier cyclic planar special case. Any three-dimensional counterexample would have to contain no packed triangle. Through the preceding project’s block-averaging result, one such packed triangle in a triple projection also establishes the sharp bound for that body in all odd dimensions (pair up the remaining coordinates). This last implication uses an existing project result, not a new odd-dimensional general theorem.
