# Strictness away from the simplex offsets
**Leo Gao · AI-assisted · private supplement to the all-offset proof.**

**Theorem.** If $1<t<2$, every packed convex subset of $[0,1]^3\cap\{x_1+x_2+x_3=t\}$ has fractional plank covering number strictly greater than $2/3$. For each compact interval $I\subset(1,2)$ the improvement is uniform over all such sets and all $t\in I$, although no explicit uniform constant is asserted here. Thus the only equality cases among all equal-normal planes are the two simplex sections, including their coordinate reflections.

We retain the notation and labeled cuts from [the all-offset manuscript](all-equal-offsets.md). By reflection take $0<\delta=t-1\le1/2$, $D=1-\delta$.

## Endpoint contacts do not create extra support conditions

We can use the six cut inequalities directly, including at endpoint contacts. Each contact meets at most two ambient edges, since the ambient section has six distinct corners. Coincident neighbors can be collapsed in the cyclic ordering. A line cannot contain contacts on all six ambient edges: unless the line is an ambient edge, its intersection endpoints each touch at most two facets, while a line containing one ambient edge intersects only that edge and the incident edges at its two endpoints. Hence the contact hull has interior in the plane. Every edge in its boundary ordering is obtained from a noncoincident consecutive pair of original contacts (consecutive collinear spans just repeat the support line). Such a pair has either $a,b>0$ and the usual corner cut, or exactly one zero entry and the ambient edge itself as cut. When $a=b=0$ the pair coincides, and the cut is vacuous. Thus making all nonvacuous cuts strict puts the template's vertices in the interior of the contact hull.

## Nonopposite or merely tight cuts

Call an aligned cut tight at the center if it is nonvacuous and $g_{ij}=0$. At a tight cut both entries are positive, and $A=a_{ij}/D$, $B=b_{ij}/\delta$ are each at least $1/2$; this follows from $AB/(A+B)=1/3$ and $A,B\le1$. Every unaligned nonvacuous cut is strictly valid at the center: the two estimates in Part 1 of the main proof are strict for positive $a,b$ when $0<\delta\le1/2$, and if exactly one is zero the condition is an ambient bound which is strict.

If there is no strictly bad cut, choose an orientation with at most two tight cuts. Otherwise all six would be tight, forcing both entries in each normalized row of $a$ and column of $b$ to be $1/2$, for which $AB/(A+B)=1/4$, not $1/3$. If there are strictly bad cuts in one orientation only, choose the opposite orientation. Each neighbor of a strictly bad cut cannot be tight, since its normalized entry in the common row or column is strictly below $1/2$. Thus the opposite orientation has at most one tight cut.

With one or two tight cuts, translate slightly to make them both strict. For two, after cyclic relabeling they are $(1,2),(2,3)$; the shift $(w,0,-w)$ with sufficiently small $w>0$ strictly increases both slacks since the relevant $a,b$ are positive. For one, the same reasoning increases that slack. The already strict cuts and cube bounds persist, so the resulting interior template can be enlarged slightly and its edge law has mass strictly above $2/3$.

## Strictly bad opposite cuts

Use the construction in Part 2 of the main proof, with $d\le d'$ and template aligned on $(1,2),(2,3),(3,1)$. Except for one explicit case below, the constructed shifts have $u<\delta/3$. Indeed $u\le g/a\le(2b-\delta)/3\le\delta/3$, with equality possible only if $a=D$ and $b=\delta$. If so, $d=D\delta/3$ is already the largest possible value of either deficit ratio. To verify this, $d/\delta=[AB-(A+B)/3]/(A+rB)$, $r=\delta/D$. On $A,B\ge1/2$ the numerator in its $A$ derivative is $rB(B-1/3)+B/3>0$, and in its $B$ derivative is $A(A-1/3)+rA/3>0$. Thus equality of $d$ at the maximum is possible only at $A=B=1$; $d'\ge d$ forces both primed entries to be maximal as well.

Now assume we are not in this case, so $\ell_i>0$ and $\ell_i<1/3$ for each minimum in (3). In addition to $(1,2)$, only $(3,1)$ may be tight in the constructed template:

* **$(1,3)$:** an unaligned cut with strict centered slack if nonvacuous; the shift only increases it.
* **$(2,3)$:** at $v=0$ the aligned cut is strictly valid if nonvacuous, since $a_{23}<D/2$ (the adjacent opposite bad cut has $a'>D/2$) and the shift can only help. At $v=d$ its bound from Part 2 is strict if $1/2<A'<2/3$ by $(2A'-1)^2>0$. If $A'\ge2/3$, the required lower bound on $\ell_2$ is nonpositive whereas $\ell_2>0$. If a cut entry is zero the nonvacuous condition is an ambient bound, already strict. Affinity gives strictness throughout.
* **$(3,2)$:** at $v=d$ the unaligned cut gains slack relative to the already strict centered placement. At $v=0$, when $a_{32},b_{32}>0$, the minimum-coordinate condition is strict since $\ell_3\ge2b_{32}/3>b_{32}/3$; the other condition is strict since $b_{32}=\delta-b<\delta/2$ and its required lower bound on $\ell_3+1/3$ is at most $2b_{32}/3<1/3$. Zero entries again reduce to strict ambient bounds or vacuity.
* **$(2,1)$:** if the chosen $v=0$ then $u<\delta/3\le S/b'$ gives strictness. If $v>0$, then $A',B'$ cannot both be 1: in that case $\delta-b'=0$ and (4) already holds at $v=0$. Both certificate polynomials in Part 3 are strictly positive for $0<r\le1$ and $1/2<A',B'\le1$ with $A',B'$ not both 1. To see it use the independent tensor Bernstein coefficients on normalized coordinates $(r,2A'-1,2B'-1)$, of coordinate degrees $(4,2,3)$, all nonnegative by the Bernstein verifier. The coefficients at $(4,1,3)$ are $(9/2,3/2)$ for the two polynomials; those at $(4,2,2)$ are $(2,4)$. If $A'<1$ the first indexed basis term is strictly positive, including when $B'=1$; otherwise $B'<1$ and the second is strictly positive. Hence (6), then (5), are strict.

A small additional translation in direction $(0,-1,1)$ strictly increases the slack of $(1,2)$ by a positive multiple of $b$ and that of $(3,1)$ by the same multiple of $a_{31}$. If $a_{31}=0$ the latter is already strict when nonvacuous. All other nonvacuous cuts and cube bounds stay strict. As before enlarge slightly and use the edge law.

## Saturated kite

The exceptional case $a=a'=D$, $b=b'=\delta$ forces the contact hull to contain the kite
$$
 H_0=\operatorname{conv}\{(0,\delta,1),(\delta,0,1),(1,\delta,0),(\delta,1,0)\}.
$$
It contains the template aligned on $(1,2),(2,3),(3,1)$ with $\ell=(2\delta/3,\delta/3,0)$. Indeed its $z$ values are $1/3,2/3,0$; the first vertex is on the edge from $(0,\delta,1)$ to $(\delta,1,0)$ (where $x=\delta(1-z)$), the second on the analogous edge with $y=\delta(1-z)$, and the third on the bottom segment $z=0$. The last inclusion follows from $0<\delta\le1/2$. Swap $x,y$ to get a second template. Averaging their two Lebesgue-dominated edge matchings of mass $2/3$ leaves marginal densities at most $1/2$ in each of $x,y$ on $(\delta/2,2\delta/3)$, because only the template with smaller minimum contributes there. In $z$ the average has zero density above $2/3$.

The segment of the line $x=y$ from $x=y=\delta/2$ to $x=y=2\delta/3$ lies in the kite, being part of the segment joining the two midpoints at $z=1$ and $z=0$. Its $z$ values are in $[1-\delta/3,1]$, strictly above $2/3$. Put extra measure of mass $\delta/12$ uniformly on this segment: its projected densities in $x,y$ are $1/2$ and in $z$ are $1/4$. Adding it to the averaged measure respects all marginal caps. This gives the explicit bound $2/3+\delta/12$ for the exceptional case.

## Compactness away from the endpoints

If a compact interval $I\subset(1,2)$ had no uniform improvement, choose a sequence of packed bodies with offsets in $I$ and capacities tending to $2/3$. Choose six contacts in each; pass to a subsequence where their offsets and all six contacts converge. The limiting contact hull has interior and, by the strict result just proved, supports a dominated matching of mass $m>2/3$. Translate the nearby hulls by suitable multiples of $(1,1,1)$ into the limiting plane. They converge there in Hausdorff distance. For any fixed $s<1$, the limiting hull contracted by $s$ about an interior point lies in all sufficiently close hulls, by the positive ball margin and the support-function characterization of convex containment. Contract the matching by $s$, multiply its mass by $s$, and translate it back into the appropriate plane. All marginal bounds remain one, and with fixed $s$ sufficiently close to 1 its mass $sm$ still exceeds $2/3$. This is a contradiction.
