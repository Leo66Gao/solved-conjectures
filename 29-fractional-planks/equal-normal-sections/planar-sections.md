# Fractional plank estimates for planar sections and nearby bodies
**Leo Gao · AI-assisted · private research note.**

A complete packed plane section of the unit cube has an exact fractional plank capacity determined solely by the location of its plane. A quantitative containment argument then gives the sharp conjectured bound for an open class of arbitrary packed planar bodies near complete, nonsimplex sections; the class includes bodies with no packed triangle. A separate single-chord estimate handles planes with nearly dominant normal coefficient. For completely general planar packed bodies, recent ordinary affine plank bounds yield a universal fractional lower bound above 0.55, but not the conjectured 2/3. The complete-section formula uses a standard joint-mixability construction and is not asserted to be a priority claim.

## Setup

Write P = [0,1]^3 ∩ {a ⋅ x = t}, after reflecting axes to make all coefficients a_i nonnegative. Write A = Σa_i > 0 and M = max a_i. Suppose a convex K ⊂ P meets all six cube facets (is *packed*). Any fractional plank cover of K consists of nonnegative measurable f_i on [0,1] with Σ f_i(x_i) ≥ 1 throughout K, at cost Σ∫ f_i. Its infimum is τ*(K). A measure on K of mass m, each coordinate marginal dominated by Lebesgue measure, certifies τ*(K) ≥ m by integrating the cover. The conventions agree with [Aharoni–Holzman–Krivelevich–Meshulam, Conjecture 3.4](https://doi.org/10.1007/s00454-001-0088-x). In the cube [−1,1]^3 with cost computed by integrating over [−1,1], all capacity values below double, while relative bounds are unchanged.

## 1. Exact capacity of complete sections

**Theorem.** P is packed if and only if M ≤ t ≤ A−M. When it is packed,
[
	au^*(P)=r:=2min(t,A-t)/Age 2/3.
]
Equality occurs only when P, up to coordinate reflections used to sign the normal, is the coordinate simplex Σx_i=1 or its reflection.

**Proof.** For a contact with x_i=1 one necessarily has t≥a_i; for x_i=0 one necessarily has t≤A−a_i, and these conditions are sufficient by filling the remaining coordinates along a diagonal. For any packed plane M≤A/2, so choose planar vectors v_i of lengths a_i summing to zero by making the sides of a (possibly degenerate) triangle. When a_i=0 use any unit vector e_i; otherwise set e_i=v_i/a_i. Regard all e_i as vectors in three-space. If U is uniform on the unit two-sphere, each e_i⋅U is uniform on [−1,1] (sphere strip area is proportional to its height). Thus
[
X_i=t/A+(r/2)e_icdot U
]
lies in the cube and Σ a_i X_i=t. Its marginals are uniform on the same interval of width r, so the law multiplied by r is a matching of mass r.

For the reverse bound, assume t≤A/2 by reflecting all coordinates if needed. The functions f_i(x)=a_i(r−x)_+/t cover P since Σ a_i(r−x_i)_+ ≥ rA−t=t. Their cost is Ar²/(2t)=r. Finally t and A−t are each at least M≥A/3, and equality r=2/3 forces M=A/3, hence all a_i equal, and t=A/3 or 2A/3. The argument also works in [0,1]^n by using a closed planar polygon of side lengths a_i when max a_i≤(Σa_i)/2. Compare [Côté and Wang, The upper copula capacity, §4.4](https://arxiv.org/abs/2611.25237) for related halfspace formulas; the proof here is self-contained.

More generally, a complete box section P∩∏[L_i,R_i] supports a probability with *exact* uniform marginal on every specified interval if and only if the interval midpoints satisfy the plane equation and 2 max a_i(R_i−L_i)≤Σ a_i(R_i−L_i). Necessity follows by taking expectations and then letting a maximal-weight centered coordinate approach its upper essential endpoint while the others are bounded below by their lower endpoints. Sufficiency uses the same sphere construction with weighted side lengths a_i(R_i−L_i), which works also for zero lengths.

## 2. Beyond complete sections: a Hausdorff-stability theorem

**Theorem.** Suppose K is compact, convex, packed, and contained in P. Let ε = d_H(K,P) in the ambient sup norm, measuring distance between points in the common plane. Then
[
	au^*(K)ge r-2arepsilon.
]
In particular τ*(K)≥2/3 when ε≤min(t,A−t)/A−1/3. This is strictly positive tolerance at every complete nonsimplex section.

**Proof.** Put c=(t/A,t/A,t/A) and d=min(t,A−t)/A=r/2. The norm ball c+dB in the common affine plane lies inside P; B is the unit sup-norm ball of its linear direction space. Work in the translated plane with origin c. The Hausdorff bound implies h_K(u)≥h_P(u)−εh_B(u) in every direction, where h denotes the support function (the sets here translated by −c). Also h_P(u)≥d h_B(u). When ε<d,
[
 h_K(u)ge (1-arepsilon/d)h_P(u).
]
By the separation characterization of containment, K contains c+(1−ε/d)(P−c). Contract the matching from the preceding theorem by the same factor; multiplying its mass by that factor preserves marginal domination. The resulting mass is r(1−ε/d)=r−2ε. When ε≥d the asserted lower bound is nonpositive and trivial. For noncompact K, the same sharp conclusion holds with strict ε<d−1/3 by passing to the compact convex hull of a sufficiently dense finite subset of K, together with its facet contacts.

**Explicit packed bodies with no packed triangle.** Consider P={Σx_i=3/2}∩[0,1]^3, take 0<δ≤1/4, and set K=P∩{x_i−x_j≤1−δ for all ordered i,j}. The six cyclic/coordinate permutations of (0,3/4,3/4) and (1,1/4,1/4) witness packing for δ≤1/4. Every point of K lies on at most one cube facet: the only possible two-facet contacts in P have one 0 and one 1, excluded by the inequality. Thus three points cannot yield a packed triangle in K. Yet K contains c+(1−δ)(P−c), c=(1/2,1/2,1/2), and consequently τ*(K)≥1−δ≥3/4 in the packed range. To obtain noncyclic bodies one may use distinct positive truncation depths δ_ij≤1/4; the same argument uses max δ_ij. For a sharp-bound example rather than an equality assertion, this explicitly demonstrates scope beyond the preceding round.

## 3. Near-dominant normals: a one-chord sufficient condition

**Proposition.** Let a_1≥a_2,a_3>0. For every packed convex K ⊂ P,
[
	au^*(K)gemax(0,1-(a_2+a_3-a_1)/min(a_2,a_3)).
]
In particular the sharp conjectured bound holds for every such K whenever a_2+a_3−a_1≤(1/3)min(a_2,a_3). No Hausdorff or symmetry condition is involved.

**Proof.** Choose p,q∈K with p_1=0 and q_1=1. Subtract the plane equations to get a_2(p_2−q_2)+a_3(p_3−q_3)=a_1. Since each difference is ≤1, each satisfies p_j−q_j≥1−(a_2+a_3−a_1)/a_j. Uniform probability on [p,q] has all marginal densities bounded by the reciprocal of the smallest positive projected width if this bound is positive. Multiply by the bound to get a matching. If a_3=0, packedness forces a_1=a_2 and x_1+x_2=1. The x_1,x_3 planar matching theorem of [Gardner, 1988, Theorem 1](https://msp.org/pjm/1988/135-2/pjm-v135-n2-p06-s.pdf) then yields mass 1 on a compact packed subhull; x_2 has the same uniform marginal as 1−x_1.

## 4. General planar lower bound and the one-window obstruction

The ordinary affine plank bound of [Bakaev and Yehudayoff, Theorem 8](https://arxiv.org/html/2602.20290v2) gives total relative width ≥2/(1+√2) for any finite family of planks covering a plane convex body. It also applies when the three coordinate plank sets are arbitrary measurable sets: if a compact packed subhull had a smaller sum of widths, outer regularity gives open supersets with smaller sum, and compactness reduces their disjoint interval components to a finite cover. The coordinate projection widths are one, so interval lengths are precisely relative widths. Consequently the standard AHKM rounding proves for all packed planar K
[
 	au^*(K)ge 4/[3(1+sqrt2)]approx0.5523.
]
The v2 remark of Bakaev and Yehudayoff states a slightly stronger ordinary planar value about 0.836, translating to a fractional value about 0.557; we give the exact simpler constant above to avoid inferring precision from an approximate source. For affine dimension one, the segment between simultaneous coordinate extrema is packed and has mass 1; alternatively select the finite contact hull first as above.

For the rounding, let U be uniform on [0,1], V=(U+1/2) mod 1, W=3/2−U−V. All are uniform, because W maps each half of the U interval linearly onto [0,1]. Then Y=(2/3)(U,V,W) has uniform marginals on [0,2/3] and sums to 1. If f is a fractional cover, the coordinate sets {s:f_i(s)≥Y_i} cover K for every Y. The expected sum of their widths is (3/2)Σ∫min(f_i,2/3), so any ordinary-plank lower bound β for these sets gives τ*≥2β/3.

A complementary sharp special case now follows from [Brown's 2026 theorem for three planks in the plane](https://zazbrown.com/research/paper/affine-plank/three-planks-in-the-plane/), whose accompanying formalization is linked there. If each f_i is quasiconcave, every nonempty superlevel set is one interval, up to endpoint conventions. Close the intervals without changing length and use Brown's ordinary bound β=1. Thus in any planar counterexample to the fractional 2/3 conjecture, the cover must have a disconnected superlevel set in at least one coordinate. Brown's theorem is for three actual intervals, not for three families of intervals. This leaves the general conjecture open; the preceding sections do not bypass that obstruction.
