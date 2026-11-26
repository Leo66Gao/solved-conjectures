# A path-variation bound for fractional planks with two equal normal coefficients
**Leo Gao · AI-assisted research note.**

**Theorem.** Let $K$ be a convex subset of the unit three-cube meeting all six facets, and suppose $K$ lies in $x+y+az=t$ with $a\ge0$. Then its fractional plank covering number satisfies
$$
\tau^*(K)\ge \max\{1-a,0\}.
$$
In particular the conjectured threshold $2/3$ holds for **all offsets when $0\le a\le1/3$**. The previous convolution bound proved it only for $a\le5-2\sqrt6\approx0.10102$. The construction below uses no convolution and does not require a single inscribed triangle. This does not resolve the whole two-equal-normal problem.

A fractional cover consists of nonnegative measurable profiles $f_i$ of the three coordinates with $\sum_i f_i(x_i)\ge1$ on $K$; the cost is $\sum_i\int_0^1 f_i$. A finite nonnegative measure on $K$ with each marginal dominated by Lebesgue measure certifies cost at least its mass. This is the dual viewpoint of [Aharoni–Holzman–Krivelevich–Meshulam, Fractional Planks (2002)](https://doi.org/10.1007/s00454-001-0088-x).

## 1. Trimming a shear by downward path variation

For a continuous piecewise affine function $g:[0,1]\to[0,1]$, let $V_-(g)=\int_0^1(-g'(s))_+\,ds$, the sum of the decreases along its affine pieces. Let $\nu$ denote the distribution of
$$
F(s)=s+a g(s)+b
$$
for uniform $s\in[0,1]$, with $a\ge0$ and any real $b$. For every Borel set $E\subseteq\mathbb R$ of finite length,
$$
\nu(E)-|E|\le aV_-(g). \tag{1}
$$
To see this, take $H(u)=\int_0^u\mathbf 1_E(v)\,dv$, interpreted as a signed integral for $u<0$. Direct substitution on each affine piece of $F$ gives
$$
\int_0^1 F'(s)\mathbf 1_E(F(s))\,ds
 =H(F(1))-H(F(0))\le |E|.
$$
The identity also holds on a constant piece, where both sides of that piece's identity are zero. Since $1=F'(s)-ag'(s)$ almost everywhere, (1) follows. This argument handles folds and atoms without treating them separately.

The same bound holds for a mixture of such paths, with its right-hand side averaged over the path weights. In particular, if each path has $V_-(g)\le1$, the projected shear law $\nu$ has nonnegative excess over Lebesgue measure of total mass at most $a$. Explicitly, its decomposition $\nu=q\,dv+\nu_s$ gives
$$
\sup_E(\nu(E)-|E|)=\int(q-1)_+\,dv+\nu_s(\mathbb R).
$$
Here the laws in use have compact support, so the supremum can be taken over finite-length sets. To trim a measure with this shear marginal, discard its singular shear part and on the absolutely continuous part keep the fraction $\min(1,1/q(v))$ at shear value $v$ (take the fraction one when $q(v)=0$). The shear marginal becomes $\min(q,1)\,dv$. The retained mass is at least $1-a$ for an original probability, and no other marginal has increased.

## 2. An ordered square contact hull supports bounded-variation paths

Let a convex set in the $(s,z)$ unit square contain four contacts
$$
L=(0,C),\quad R=(1,D),\quad P=(A,0),\quad Q=(B,1),
\qquad A\ge B,\quad C\ge D.
$$
There is a probability in their hull with both $s,z$ uniform, which can be built from paths of downward $z$-variation at most one. First assume $0<B<A<1$ and $0<D<C<1$. Consider the following four piecewise affine paths, each parameterized by its first coordinate from zero to one:
$$
\begin{array}{c|c|c}
\text{path}&\text{vertices in order}& V_-\text{ in }z\\ \hline
\mathrm{lo}& L,P,R & C\\
\mathrm{up}& L,Q,R & 1-D\\
\mathrm{vert}& L,Q,P,R & 1\\
\mathrm{diag}& L,R & C-D
\end{array}
$$
Every edge stays in the hull by convexity. Give each path the law of uniform $s$; all four first marginals are automatically uniform. Their $z$ densities are constant on the three open intervals $(0,D),(D,C),(C,1)$. To find a mixture with uniform $z$, associate to a path the vector
$$
(\text{density on }(0,D)-\text{density on }(D,C),\
 \text{density on }(C,1)-\text{density on }(D,C)).
$$
From the elementary density formula for a segment, the respective four vectors are
$$
\begin{array}{c|cc}
\mathrm{lo} & (1-A)/D &-A/C\\
\mathrm{up} & -(1-B)/(1-D)& B/(1-C)\\
\mathrm{vert}&(1-A)/D & B/(1-C)\\
\mathrm{diag}&-1/(C-D)&-1/(C-D).
\end{array}
$$
For example, the middle edge $QP$ contributes the same density $A-B$ on the three intervals of the vertical path, and cancels from its two differences.

There is one vector in each open quadrant, so the origin belongs to their convex hull. One direct check is that for every nonzero linear functional, choose the displayed vector whose coordinate signs oppose its nonzero coefficients: its value is negative, contradicting any separating functional. A mixture giving the zero vector has equal density on the three intervals, hence density one since it has total mass one. Each of its paths has downward variation at most one, as required. This uses the same kinds of boundary segments and diagonals as [Gardner's Theorem 1, case (ii)](https://msp.org/pjm/1988/135-2/pjm-v135-n2-p06-s.pdf); the routing into full-width paths and the shear estimate are the additional steps.

For degenerate ordered contacts, replace each of $A,B,C,D$ by its convex interpolation with fixed strictly ordered interior values. The convex hulls of the adjusted contacts converge to the original hull. Apply the preceding construction, then trim as in Section 1 for any fixed $a,b$. The measures are supported in a fixed compact set in the $(s,z)$ plane, so a subsequence converges weakly. Its limit is supported on the actual contact hull. All three marginal dominations, including the shear marginal, survive the limit by testing with nonnegative continuous functions; their masses converge and each is at least $1-a$. This form of the conclusion is all that is needed; no claim about the piecewise-path form of the limiting untrimmed measure is necessary.

## 3. Apply the ordering to the two equal coefficients

We may restrict to the compact convex hull of finitely many facet contacts. When $a=0$, the plane is $x+y=1$, and Gardner's two-coordinate theorem applied to $(x,z)$ gives full uniform marginals in all three coordinates after lifting. Now let $a>0$. Packedness implies $1\le t\le1+a$ (the stronger feasible inequalities are unnecessary here). Choose one point of $K$ on each of $z=0,1$. If their respective $(x,y)$ coordinates are $(A_x,A_y)$ and $(B_x,B_y)$, then
$$
 (A_x-B_x)+(A_y-B_y)=a>0.
$$
At least one of the two horizontal coordinates, call it $s$, satisfies $A_s\ge B_s$. In the $(s,z)$ projection choose contacts $(0,C),(1,D)$. The unselected horizontal coordinate lies in $[0,1]$, so
$$
 C\ge (t-1)/a\ge D.
$$
Indeed at $s=0$ the other value is $t-aC\le1$, and at $s=1$ the other value is $t-1-aD\ge0$. Thus the four chosen contacts satisfy Section 2.

Lift the paths back to the plane. The remaining horizontal coordinate is $t-s-az$, whose reflection is
$$
1-t+s+az .
$$
This is exactly the shear of Section 1 with $b=1-t$. After trimming, the projected $s,z$ marginals and the reflected remaining marginal are all dominated by Lebesgue measure. Reflection preserves this domination for the original coordinate, so the measure is a matching in $K$ of mass at least $1-a$. The degenerate-case limiting argument applies even if the auxiliary strict-order hulls are not contained in the original plane section of the cube: they are used only in the projection before taking the limit back to the exact contacts.

The resulting bound proves the new all-offset range. The argument does not by itself establish the sharp threshold for $a>1/3$; its loss bound is an upper bound on the mass discarded, not a counterexample in the remaining parameter range.
