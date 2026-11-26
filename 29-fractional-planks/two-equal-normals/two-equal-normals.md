# Fractional planks for two ranges of two-equal normals
**Leo Gao · AI-assisted research note.**

Let $K\subseteq[0,1]^3$ be convex, meeting all six facets, and contained in the plane $x+y+az=t$ with $a\ge0$. The sharp conjectured lower bound $2/3$ for the cost of a fractional coordinate plank cover is established here for **every possible offset** if
$$
 0\le a\le 5-2\sqrt6\quad\text{or}\quad \frac{11}{7}\le a\le2 .
$$
For $a\ge3/2$ an additional sharp region near the extreme offsets is $\min(t-a,2-t)\le2a-3$. The preceding equal-normal theorem handles $a=1$ at every offset. The other parameters and offsets are not completely resolved. A separate exact example in Section 4 shows why the preceding equal-width triangular construction cannot prove the remaining cases.

A fractional coordinate plank cover means nonnegative measurable profiles $f_i:[0,1]\to[0,\infty]$ with $\sum_i f_i(x_i)\ge1$ on $K$. Its cost is $\sum_i\int f_i$. A measure of mass $m$ on $K$ whose three marginals are each bounded above by Lebesgue measure certifies a cost of at least $m$. By taking a convex hull of six facet contacts we may work with compact sets. The possible offsets satisfy $\max(1,a)\le t\le\min(2,1+a)$, since after fixing a coordinate at zero or one the other coordinates have their designated ranges. In particular no packed set exists for $a>2$. Reflecting all coordinates changes $t$ to $2+a-t$ and preserves the covering number.

## 1. Small third coefficient: two averaged convolutions

The [planar matching theorem of Gardner](https://msp.org/pjm/1988/135-2/pjm-v135-n2-p06-s.pdf) asserts that a compact convex set packed in the unit square supports a probability with both coordinate marginals uniform. Apply it to the projections of $K$ on $(x,z)$ and $(y,z)$, and lift these probabilities back to $K$ using the affine plane equations. Let $X$ and $Y$ be independent vectors with these laws, respectively. Thus $X_x,X_z,Y_y,Y_z$ are uniform, and for every interval $I$ the plane relation gives
$$
 \Pr\{X_y\in I\}\le |I|+a,\qquad \Pr\{Y_x\in I\}\le |I|+a.
$$
For example, if $X_y\in[\ell,\ell+w]$ then $X_x=t-X_y-aX_z\in[t-\ell-w-a,t-\ell]$, an interval of length $w+a$.

For $0<\alpha<1$, put $\beta=1-\alpha$. Both $\alpha X+\beta Y$ and $\beta X+\alpha Y$ are in $K$. For the first, its $x,z$ densities are at most $1/\alpha$, by convolution with the scaled uniform marginals from $X$. Its $y$ density is at most $1/\alpha+a/\beta$: convolving by $\beta Y_y$ averages the marginal law of $\alpha X_y$ over a translating interval of length $\beta$, and the preceding concentration bound gives its mass at most $\beta/\alpha+a$. The reversed weighted vector has the same bounds with $x,y$ swapped. Therefore the equal mixture has all marginal densities at most
$$
 \frac1\alpha+\frac{a}{2(1-\alpha)}.
$$
For $a>0$ this is minimized at $\alpha=1/(1+\sqrt{a/2})$. It yields a dominated matching of mass $(1+\sqrt{a/2})^{-2}$, at least $2/3$ precisely when $a\le5-2\sqrt6$. At $a=0$, packedness forces $x+y=1$, so the first planar law already has all three marginals uniform.

## 2. A concordant chord, and its exact threshold

Let $P$ denote the $(x,y)$ projection of $K$. Its difference body $B=P-P$ lies in $[-1,1]^2$, attains both extremes of each coordinate, and contains a point with coordinate sum $a$ from two opposite $z$ contacts. If $B$ meets $[2/3,\infty)^2$, the corresponding segment in $K$ has both $x,y$ projection widths at least $2/3$. The $z$ width is their sum divided by $a$ and is also at least $2/3$ since $a\le2$. A uniformly weighted segment furnishes the matching.

Otherwise strict separation from the closed upper quadrant gives a linear functional with nonnegative coefficients. Normalize them to $\lambda,1-\lambda$ and swap $x,y$ so that $\lambda\ge1/2$. Its support value $h$ on $B$ satisfies
$$
 h<2/3,\qquad h\ge 2\lambda-1,\qquad h\ge 1-\lambda(2-a).
$$
The first lower bound uses a point with $x=1$ and $y\ge-1$; the second minimizes the functional on $x+y=a$ inside the difference square. Consequently $\lambda<5/6$ and $\lambda>1/[3(2-a)]$. This is impossible for $a\ge8/5$ (at $a=2$, the second lower bound is already one).

This one-segment threshold is sharp in the interval $1/2<a<8/5$. For central offset $t=1+a/2$ take $P=(1/2,1/2)+\tfrac12\operatorname{conv}\{\pm(1,-1),\pm(a-1,1)\}$ and lift it to the plane. It is packed. With $\lambda=2/(4-a)$ the support of its difference body is $a/(4-a)<2/3$, excluding the concordant chord. No chord can instead have $x,y$ widths at least $2/3$ with opposite signs and $z$ width at least $2/3$, because opposite signs force $|\Delta x+\Delta y|\le1/3<2a/3$. This obstruction is to a single chord, not to the fractional inequality.

For a further offset bound, suppose $a\ge3/2$ and reflect so $t=a+u$, where $0\le u\le(2-a)/2$. Let $Q$ be the projection of a $z=1$ contact, and $R$ a contact with $x=1$. Write $L(x,y)=\lambda x+(1-\lambda)y$ with the separating $\lambda$ above. Then $L(R)\ge\lambda$ and $L(Q)\le\lambda u$, as $Q_x+Q_y=u$ and $\lambda\ge1/2$. Hence $h\ge\lambda(1-u)$ and, by the strict bounds on $h,\lambda$, we have $u>1-2/(3\lambda)>2a-3$. Thus $u\le2a-3$ suffices for the chord, as claimed.

## 3. A tilted ellipsoid below the one-chord threshold

Assume $11/7\le a<8/5$ and no suitable concordant chord exists. Set $e=8/5-a\in(0,1/35]$ and keep $t=a+u\le1+a/2$. Write the four projected contacts
$$
 R=(1,r),\quad S=(0,1-s),\quad
 Q=(u-q,q),\quad P_0=(a+u-1+p,1-p),
$$
where $Q,P_0$ come from $z=1,0$, respectively, and $r,s,p,q\ge0$. The separating direction satisfies $7/9\le\lambda<5/6$. Comparing $L(R)-L(S)$ with $2/3$ gives
$$
 r+s\le\frac{5/3-2\lambda}{1-\lambda}
 \le\frac{25e}{1+15e}\le\frac1{2}.
$$
Comparing $L(P_0)-L(Q)$ gives
$$
 1-\lambda(2-a)+(2\lambda-1)(p+q)<2/3,
 \qquad p+q\le(3/2)e<3/70 .
$$
Here the available slack in the first display's lower expression for $h$ is at most $(5/6)e$ and $2\lambda-1\ge5/9$. The offset estimate in Section 2 also gives $1/5-2e\le u\le1/5+e/2$.

Use affine coordinates $(U,V)=((5x+y-1)/4,y)$. Put $\gamma=3/70$ and $c=4/35$. The contact bounds imply
$$
 \begin{array}{c|cc}
 & U & V\\ \hline
 R & \ge1 & r\\
 S & \le0 &1-s\\
 Q & [-c,\,(5u-1)/4] & \le\gamma\\
 P_0 & [5(a+u-1)/4,\,1+c] & \ge1-\gamma.
 \end{array}
$$
For instance $U_Q=(5u-1)/4-q$ and $U_{P_0}=5(a+u-1)/4+p$; substituting the bounds for $u,p,q$ gives the stated intervals.

Let $L_0=\max(0,(5u-1)/4)$ and $H_0=5(a+u-1)/4\le1$, and put $r'=(r-\gamma)_+/(1+c)$ and $s'=(s-\gamma)_+/(1+c)$. For each $U\in[L_0,H_0]$ the segment $QR$ crosses the vertical line at a point of height at most $\gamma+r'(U+c)$. In fact its fraction from $Q$ towards $R$ is at most $(U+c)/(1+c)$, by $U_Q\ge-c$ and $U_R\ge1$. The analogous segment $SP_0$ crosses at height at least $1-\gamma-s'(1+c-U)$: its fraction toward $S$ is at most $(1+c-U)/(1+c)$. Thus the hull contains all points in
$$
 L_0\le U\le H_0,\qquad \gamma+r'(U+c)\le V\le1-\gamma-s'(1+c-U).
$$
The assertion follows by taking the segment between these two points at each $U$.

Put $\alpha=H_0-L_0$, $\beta=2/3$, $\rho=13/30$, and $m_U=(L_0+H_0)/2$. From $1/5-2e\le u\le1/5+e/2$ we have
$$
 \alpha\ge1-15e/4\ge25/28,\qquad 25/56\le m_U\le1/2.
$$
When $u\le1/5$ these follow from $L_0=0$; otherwise $\alpha=1-5e/4$ and $L_0+H_0\le1$. For a slope $k$ the support radius of an ellipse with these $U,V$ widths and correlation $\rho$, along $V-kU$, is
$$
 R_\alpha(k)=\frac12\sqrt{k^2\alpha^2+\beta^2-2\rho k\alpha\beta}.
$$
Thus we can choose its vertical center $m_V$ to fit both height bounds if
$$
 R_\alpha(r')+R_\alpha(s')+(m_U+c)r'+(1+c-m_U)s'\le1-2\gamma.
 \tag{*}
$$
The left side is convex as a function of $(r',s')$, since each radius is the Euclidean norm of a vector affine in the slope. Also $r'+s'\le\Lambda:=(1/2-\gamma)/(1+c)=16/39$. Hence its maximum is bounded by its largest value at the three vertices $(0,0),(\Lambda,0),(0,\Lambda)$ of that slope simplex. At the zero vertex its value is $\beta$. At the other two it is at most $\beta/2+R_1(\Lambda)+\Lambda(1+c-25/56)$; indeed $R_\alpha(\Lambda)\le R_1(\Lambda)$ since $\Lambda(25/28)>\rho\beta$ and the square of the radius increases with $\alpha$ on that interval. The last bound is strictly below $1-2\gamma$: the exact rational margins are
$$
 D_0=1-2\gamma-\beta/2-\Lambda(1+c-25/56)=419/1365>0,
 \quad D_0^2-R_1(\Lambda)^2=1648/5589675>0.
$$
Thus (*) holds. Choose $m_V$ between the lower height bound at $m_U$ plus $R_\alpha(r')$, and the upper height bound there minus $R_\alpha(s')$. The ellipse
$$
 (U,V)=(m_U,m_V)+\frac12\bigl(\alpha S,\ \beta(\rho S+\sqrt{1-\rho^2}T)\bigr),
 \qquad S^2+T^2\le1
$$
is contained in the hull region, since its supports satisfy both sloped height inequalities and its horizontal width fits $[L_0,H_0]$.

Lift this ellipse to $K$ through the affine plane. Its $y$ width is $\beta=2/3$. Using $x=(1+4U-V)/5$, and $x+y=(1+4U+4V)/5$, its squared widths in $x,z$ are
$$
 W_x^2=(4\alpha/5)^2+(\beta/5)^2-2\rho(4\alpha/5)(\beta/5),\qquad
 W_z^2=\left(\frac{4}{5a}\right)^2(\alpha^2+\beta^2+2\rho\alpha\beta).
$$
Both bounds increase with $\alpha\ge25/28$, so substitute $\alpha_0=1-15e/4$. The resulting $x$ bound decreases with $e$. For $z$, the derivative of $\sqrt{\alpha_0^2+\beta^2+2\rho\alpha_0\beta}/a$ with respect to $e$ has the sign of $\alpha_0^2+\beta^2+2\rho\alpha_0\beta-(15/4)a(\alpha_0+\rho\beta)$. It is negative because the first three terms are at most $(1+\beta)^2=25/9$ and the last product is at least $(15/4)(11/7)(25/28)>25/9$. Thus substitute $e=1/35$ in both lower bounds. The respective squared widths exceed $4/9$ by the exact margins $11/11025$ and $301/27225$.

Finally let $(S,T)$ be the first two coordinates of a uniform point on the unit two-sphere. Every linear functional of $(S,T)$ has uniform law on its entire projection interval, by rotational invariance and the sphere-strip area formula. The image probability on the ellipse has its physical coordinate densities at most $3/2$. Multiplying it by $2/3$ gives the required matching. This covers all $a\ge11/7$ by combination with the chord argument.

## 4. Exact failure of the equal-width triangle strategy at every unequal coefficient

Assume $0<a<2$ and work at central offset $t=1+a/2$. Suppose a nondegenerate inscribed triangle has a law uniform in all three coordinate projections, each of the same length $w>0$. Subtract the coordinate minima and divide by $w$, and use the weighted coordinates $(x,y,az)$ in that normalization. Taking expectations shows the triangle lies at normalized coordinate sum $1+a/2$. Each normalized coordinate has extrema $0$ and one of $1,1,a$. Because the three weights satisfy strict triangle inequalities, any vertex having two coordinate minima would have sum strictly below $1+a/2$, and any vertex having two maxima strictly above it. Thus the minima and maxima are each on distinct vertices. Their disjoint assignments must be one of the two cyclic orientations. The plane equation fixes the other entry at each vertex. In $(x,y)$ the two possible templates are translates or central reflections of the template with vertices $(0,1),(1-a/2,0),(1,a/2)$, multiplied by the common width $w$. A segment with all three projection widths equal and positive is impossible for $0<a<2$: its increments would satisfy $\pm1\pm1+a(\pm1)=0$.

* For $0<a<1$, take the packed parallelogram with projected vertices $(1-a/2,0),(1,0),(a/2,1),(0,1)$ and lift to the central plane. The linear coordinate $x+(1-a/2)y$ has width $a/2$ in it, while the unit template has width $a(1-a/4)$ in that same direction. Hence every equal-width template inside has $w\le2/(4-a)<2/3$.
* For $1<a<2$, take the packed parallelogram with projected vertices $(0,1-a/2),(1-a/2,0),(1,a/2),(a/2,1)$. The width of $x-y$ is $2-a$, whereas the unit template has width $2-a/2$. Thus $w\le2(2-a)/(4-a)<2/3$.

Each lifted example meets both $z$ facets at its extreme sums $x+y=1\pm a/2$, and both other coordinate ranges are one. They are centrally symmetric, so they are not obstructions to the fractional inequality (Ball's ordinary plank theorem and the Aharoni–Holzman–Krivelevich–Meshulam rounding already imply it for centrally symmetric bodies). They obstruct only a triangle with *equal* uniform marginal interval lengths; mixtures, laws merely bounded in density, or triangles with unequal marginal lengths are not excluded.

The underlying conjecture is [Aharoni–Holzman–Krivelevich–Meshulam, Fractional Planks, Conjecture 3.4](https://doi.org/10.1007/s00454-001-0088-x). No assertion of publication priority is made. The sharp fractional bound for all remaining two-equal normal parameters has not been proved here.

## 5. Endpoint slices and a local consequence of the equal-normal result

The extreme offsets themselves satisfy the sharp bound for all feasible coefficients. For $a=0$ this is already covered. If $a>0$ and $t=\max(1,a)$, packedness forces a cube vertex in $K$: choose a contact $x_i=1$ in a coordinate with maximal coefficient, and its two other coordinates must be zero. The opposite offset follows by reflection. A convex packed body containing a cube vertex attains the lower bound via the previously proved positive-chord argument. Briefly, reflect the vertex to the origin and let $p_i$ be opposite-facet contacts. If finitely many open interval planks $(a_k,b_k)$ in coordinates $i(k)$ have total width below one, choose $L_k>b_k-a_k$ with $\sum L_k<1$. On binary variables $s$, the update sets $s_k$ to one if the $i(k)$ component of $\sum_{l\neq k}L_ls_lp_{i(l)}$ is at least $a_k$, and zero otherwise. The map is monotone, so iteration from zero gives a fixed point. Then $\sum_k L_ks_kp_{i(k)}$ lies in $K$ and avoids every plank. A measurable family with total width below one would give a finite open-interval cover of the compact contact hull by outer regularity and compactness, so the ordinary lower bound is one. The AHKM rounding draws nonnegative thresholds summing to one with each marginal uniform on $[0,2/3]$; the coordinate superlevel sets then cover for every threshold triple. Averaging their ordinary lower bound gives the desired fractional $2/3$.

Another consequence of the preceding equal-normal work is qualitative. For each compact offset interval $I\subset(1,2)$ there exist $\epsilon,\eta>0$ such that if $|a-1|<\epsilon$ and $t\in I$, all packed sets in these planes have capacity at least $2/3+\eta$. Indeed, from a contradicting sequence choose six facet contacts and take a convergent subsequence. The equal-normal limit hull has a dominated matching of mass strictly above $2/3$ by the previous strictness theorem. Contract slightly toward its interior, rescaling the mass by the contraction factor, and convolve with a small smooth probability kernel in the plane. The matching is then supported a positive distance inside that hull, still of mass above $2/3$, and its marginal density caps remain one. Identify all planes via common coordinates $(x,y)$: the projected contact hulls converge in Hausdorff distance, so the smooth density's compact support lies inside all sufficiently nearby hulls. The third projection is $z=(t-x-y)/a$; its density varies uniformly with $a,t$ by the integral formula for projecting a compactly supported smooth planar density. The first two densities are unchanged. Rescaling by $1+o(1)$ restores all caps and contradicts the purported sequence. This gives no uniform neighborhood extending to the simplex offsets themselves.
