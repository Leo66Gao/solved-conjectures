# A strict gap on the central equal-normal plane, stable under perturbation
**Leo Gao · AI-assisted · private supplementary research note.**

**Theorem.** There exist \(\varepsilon>0\) and \(\eta>0\) with the following property. Let \(K\subseteq[0,1]^3\) be any packed convex set in an affine plane \(a_1x_1+a_2x_2+a_3x_3=t\), normalized by \(\sum a_i=3\). If
\[
\max_i |a_i-1|+|t-3/2|<\varepsilon,
\]
then \(\tau^*(K)\ge 2/3+\eta\). No symmetry or Hausdorff-nearness of \(K\) to the *complete* section is assumed. The constants here are nonexplicit. In particular this extends the bound to an open neighborhood of the central equal-normal plane in both normal and offset, not just to one affine plane.

The proof refines the geometry in [the central-hexagon note](central-hexagon.md), then uses a compactness argument with a density regularization that controls perturbations of the projection directions.

## 1. Pointwise strictness for central contact hulls

Use the notation \(v_i,p_i,s_i,h_i\) from the central-hexagon proof. Let \(H\) be the convex hull of the six chosen contacts. The radial points \((1-h_i)v_i\in H\) have positive radii, in all six directions, so the origin belongs to the interior of \(H\) (for instance, \(H\) contains the hull of the points \(v_i/2\)). Call a corner *strictly bad* if \(h_i>1/3\) and *tight* if \(h_i=1/3\). A radially good corner with \(h_i<1/3\) has \((2/3)v_i\) in the interior of \(H\): it belongs to the open segment from the interior origin to \((1-h_i)v_i\).

**Case A: there are strictly bad corners of both parities.** There is exactly one of each, opposite, relabeled \(0,3\) with \(0<\delta=h_0-1/3\le\eta_0=h_3-1/3\le1/6\). The shifted even triangle from the central proof has vertices \((2/3)v_i-\delta v_0\) for \(i=0,2,4\). If \(\delta<1/6\), the side vertices \(i=2,4\) in that proof are interior: the horizontal section has a point strictly on either side of the proposed coordinate. Indeed, the left bound \(-1/2\) in the first case is strictly below \(-1/3-\delta\), and in the second case
\[
\frac{1-2s}{3s}>\frac{1-2s}{3(2-s)}\ge\eta_0\ge\delta
\quad (1/3<s<1/2).
\]
The right bounds are strictly positive relative to the target. The horizontal heights \(\pm2/3\) lie between the hull's extremes \(-1,1\), attained on the top and bottom edges. Thus a point strictly inside such a horizontal section is interior in the plane: a supporting line through it would have to contain that section and be horizontal. The third target \((1-h_0)v_0\) becomes interior if we translate a little farther along \(-v_0\), staying on the open radial segment. Both side vertices remain interior for a sufficiently small additional translation. Then enlarge the triangle a little to obtain common coordinate width strictly above \(2/3\).

If \(\delta=1/6\), then \(h_0=h_3=1/2\). Equality in \(ab/(a+b)\le1/2\) for \(a,b\in[0,1]\) requires \(a=b=1\). Hence the hull contains the four vertices \(v_1,v_2,v_4,v_5\). In true cube coordinates centered at \((1/2,1/2,1/2)\), after relabeling or global reflection, \(v_1=(1/2,0,-1/2)\), \(v_2=(0,1/2,-1/2)\), \(v_4=-v_1\), \(v_5=-v_2\). Put equal probability on the uniform laws of \([v_1,-v_2]\) and \([-v_1,v_2]\). Each of the first two coordinates is uniform on one half-interval in each law and gets the two opposite halves in the mixture. Each law already has third coordinate uniform on \([-1/2,1/2]\). Thus the fractional capacity is 1 in this case.

**Case B: strictly bad corners occur in at most one parity.** A tight corner must have \(a_i,b_i\ge1/2\). If any corner is strictly bad, each adjacent corner has either \(a\) or \(b\) strictly below \(1/2\), so is not tight. Choose the other parity, with no strictly bad corners and at most one tight one (the possible opposite corner). If there are no strictly bad corners, choose a parity with at most two tight ones; otherwise all six would be tight, forcing every \(s_i=1/2\) by the inequalities \(s_i\ge1/2\) and \(s_{i-1}\le1/2\) at every corner. At \(s_i=1/2\) all \(h_i=1/4\), a contradiction.

For each tight vertex \(i\), the target \((2/3)v_i\) lies strictly between \(p_{i-1}\) and \(p_i\); the points are distinct because both \(a_i,b_i\ge1/2\). In local display coordinates with \(v_i=(1,0)\), the line through the two endpoints has equation
\[
 x=2/3+\kappa y,\qquad\kappa=1/(3b_i)-1/2,\quad |\kappa|\le1/6.
\]
This follows by substitution of \(p_i=(1-b_i/2,b_i)\). The origin is strictly to the left. In the regular Euclidean metric, with height coordinate \(\sqrt3\,y/2\), the line's outward unit normal makes angle at most \(\arctan(1/(3\sqrt3))<30^\circ\) with the radial direction \(v_i\). Two vertices of one parity are separated by \(120^\circ\), so the corresponding two outward normals, if needed, are not antiparallel. One can choose a common strict inward displacement \(w\): with one tight vertex use minus its normal, and with two use minus the sum of their unit normals. For each tight vertex the displacement moves the point into the interior of the triangle \(\operatorname{conv}\{0,p_{i-1},p_i\}\) for sufficiently small positive multiples of \(w\), since it starts in the relative interior of the edge and crosses strictly inward. The other vertices, already interior to \(H\), remain there. Enlarge slightly after this translation.

Thus for every central contact configuration, a Lebesgue-dominated measure of mass strictly greater than \(2/3\) is available, either from the edge law on an enlarged motif or from the explicit parallelogram law.

## 2. Stability under varying the affine plane

Suppose no uniform constants existed. For each \(k\) choose packed \(K_k\) in a plane whose normalized coefficients and offset differ from the central ones by less than \(1/k\) in the displayed quantity, and whose covering number is less than \(2/3+1/k\). Choose six facet contacts from each \(K_k\); their compact hull is \(H_k\subseteq K_k\). Pass to a subsequence on which the six contacts converge. Their limits are the corresponding central hexagon contacts. Let \(H\) be their hull. By Part 1, it is full-dimensional in its plane and supports a Lebesgue-dominated measure \(\mu\) of mass \(m>2/3\).

Identify the central plane with coordinates \((x_1,x_2)\). The perturbed plane maps from this display space by
\[
 \Phi_k(u,v)=(u,v,b_k-c_k u-d_k v),\qquad b_k\to3/2,\quad c_k,d_k\to1.
\]
The pullbacks of \(H_k\) converge in planar Hausdorff distance to the display hull of \(H\), by convergence of the six generators. First contract \(\mu\) toward an interior point of \(H\) by a factor \(s<1\) chosen close enough to one that \(sm>2/3\), and multiply its mass by \(s\). All marginal density bounds remain one. Then convolve in the plane with a nonnegative smooth probability kernel supported in a sufficiently small Euclidean disk. This keeps all three marginal density bounds one: projecting a convolution is a one-dimensional convolution by a probability, which preserves the bound. The resulting measure has mass \(m'=sm>2/3\) and smooth compactly supported planar density \(g\), with support a positive distance inside \(H\). The existence of that margin follows from convexity: if \(c+RB\subset H\) is an interior ball and \(s<1\), the contracted hull plus \((1-s)RB\) is still contained in \(H\).

A fixed compact subset of the interior of a convex hull remains in all sufficiently Hausdorff-close convex hulls: use support functions and the positive ball margin. Thus for large \(k\) the support of \(g\) maps under \(\Phi_k\) inside \(H_k\). The first two projected densities are unchanged. The third is
\[
 h_k(z)=\frac1{c_k}\int_{\mathbb R}g\!\left(\frac{b_k-z-d_k v}{c_k},v\right)\,dv,
\]
with \(c_k>0\) eventually. These densities converge uniformly to the central density, since \(g\) is uniformly continuous with compact support, \(v\) can be restricted to a fixed compact interval, and all \(h_k\) vanish outside a fixed bounded interval. Hence all three marginal densities have sup norm at most \(1+o(1)\). Rescale the mass by \(1/(1+o(1))\) using a nonnegative error bound to produce a Lebesgue-dominated matching on \(H_k\) of mass tending to \(m'>2/3\). This contradicts the claimed covering numbers and proves the uniform theorem.

This compactness transfer covers genuinely unequal normal coefficients and offsets near the middle of the cube. It does not establish a quantitative size for the neighborhood or give the sharp bound for all planar packed bodies.
