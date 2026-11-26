# A sharp disk-content pullback inequality and rotational cases of Erdős #509

**Status.** The general conjecture remains open. The following is an unconditional theorem for arbitrary compact planar sets, with an optimal constant. It implies a strict improvement over the target constant 2 for all polynomial lemniscates with rotational symmetry of order at least three. No independent peer review or exhaustive priority claim is implied.

For compact $E\subset\mathbb C$, let $h(E)$ denote the infimum of the sums of radii over finite covers by closed disks. For a compact set this equals the analogous infimum using countably many closed disks: enlarge a countable cover by summably small positive radii and extract a finite subcover of the resulting open cover. The cost of an actual finite cover is asserted explicitly when needed.

## The sharp power-pullback theorem

If $k\ge2$ is an integer and $E^{[1/k]}=\{z:z^k\in E\}$, then
$$
 h(E^{[1/k]})^k\le k\,h(E).
$$
Indeed, any finite cover of $E$ of positive cost $s$ yields a finite cover of its pullback of cost at most $(ks)^{1/k}$. No smaller factor than $k$ works, even for finite unions of closed intervals of the positive real axis.

### 1. Pulling back one disk

If $0<u<v$, the principal $k$-th root takes the closed disk with diameter $[u,v]$ into the closed disk with diameter $[u^{1/k},v^{1/k}]$. To see it, put $p=1/k$. For $t>0$, the real Möbius map $w\mapsto w/(w+t)$ takes the first disk onto the disk with diameter $[u/(u+t),v/(v+t)]$: it preserves circles, maps the real endpoints to the stated endpoints, respects conjugation, and has its pole outside the disk. Use
$$
 w^p=c_p\int_0^\infty {w\over w+t}t^{p-1}\,dt,\qquad
 c_p=\left(\int_0^\infty {s^{p-1}\over1+s}\,ds\right)^{-1}.
$$
This follows by substitution for positive $w$, and analytic continuation on the right half-plane (the integral converges locally uniformly). Subtract the integral of the pointwise disk centers and apply the triangle inequality. The integrated center and radius are exactly $(u^p+v^p)/2$ and $(v^p-u^p)/2$. A disk of zero radius is a point and its pullback is finite.

Given a disk of center $c_i$ and radius $s_i$, set
$$
 a_i=((|c_i|-s_i)_+)^{1/k},\qquad b_i=(|c_i|+s_i)^{1/k}.
$$
Its entire pullback is in the central disk of radius $b_i$. If $a_i>0$, rotating the preceding lemma gives a second choice: $k$ disks of total cost $(k/2)(b_i-a_i)$, one along each of the $k$ root directions. In all cases $b_i^k-a_i^k\le2s_i$.

### 2. Sharing the center across the whole cover

For $R>0$, use one central disk of radius $B=\max(\{R\}\cup\{b_i:a_i\le R\})$ and the $k$-disk covers for all $a_i>R$. The extra cost $B-R$ is at most $\sum_{a_i\le R}(b_i-R)_+$. Since $k/2\ge1$, the total cost does not exceed
$$
 F(R)=R+{k\over2}\sum_i\int_{a_i}^{b_i}\mathbf1_{\{t>R\}}\,dt.
$$
This is important: the argument does **not** try to cut a crescent out of an outer disk. One shared central disk absorbs every whole interval that crosses the cutoff.

Set $T=(ks)^{1/k}$ and average over $0<R<T$ with distribution function $(R/T)^{k-1}$. Then
$$
 \mathbb EF(R)\le {k-1\over k}T+
 {1\over2T^{k-1}}\sum_i(b_i^k-a_i^k)
 \le {k-1\over k}T+{s\over T^{k-1}}=T.
$$
Some actual finite cover therefore has cost at most $T$. Taking infima proves the inequality; a base cover of zero cost consists of finitely many points and can be handled directly.

### 3. Why the constant cannot be improved

Fix $k$, write $d=2/k$, let $M\to\infty$, $\delta=1/M$, $\rho=M^{-1/2}$. On each cell $[j\delta,(j+1)\delta]$, $0\le j<M$, retain the closed left subinterval of length $d\delta$; let $A_M$ be their union intersected with $[\rho,1]$. Let
$$
 E_M=\{r^k:r\in A_M\},\quad S_M=E_M^{[1/k]}=\bigcup_{j=0}^{k-1}e^{2\pi i j/k}A_M .
$$
Because $E_M$ is a finite union of real intervals, projection onto the real line and diameter disks give
$$
 h(E_M)=\tfrac12|E_M|=\tfrac12\int_{A_M}kr^{k-1}dr\longrightarrow d/2=1/k .
$$
The convergence follows from uniform continuity on the mesh, and the removed initial interval has vanishing length.

For the matching lower bound let $\nu_M$ be half arclength on the $k$ retained spokes. Its mass tends to $kd/2=1$. We claim $\nu_M(D)\le(1+o_k(1))s$ for every disk $D$ of radius $s$, uniformly over disks. If $s<\rho\sin(\pi/k)$, the disk meets at most one retained spoke, by their separation; its mass is at most $s$.

For the other disks we need an elementary ray estimate: the sum of lengths intercepted by a disk of radius $s$ on the $k$ full half-rays $e_j\mathbb R_{\ge0}$ is at most $ks$, where $e_j=e^{2\pi i j/k}$. If the center $c$ satisfies $|c|\le s$, the intercept on ray $j$ has length
$$
 c\mathbin{\cdot}e_j+\sqrt{s^2-|c|^2+(c\mathbin{\cdot}e_j)^2}\;\le\; c\mathbin{\cdot}e_j+s .
$$
Sum and use $\sum_j e_j=0$. If $|c|>s$, put $u_j=(c/|c|)\mathbin{\cdot}e_j$. Only rays with $u_j>0$ can contribute positive length. Whenever the ray hits the disk, its chord has length $2\sqrt{s^2-|c|^2(1-u_j^2)}\le2s u_j$. Hence the sum is at most $2s\sum_j(u_j)_+=s\sum_j|u_j|\le ks$.

On any interval $I\subset[0,1]$, the retained length is at most $d|I|+2\delta$, by deleting at most two partial mesh cells. Apply this on each ray and the preceding ray estimate to get $\nu_M(D)\le (d/2)ks+k\delta=s+k\delta$. Since now $s\ge\rho\sin(\pi/k)$, the desired relative error is at most $k\delta/(\rho\sin(\pi/k))=o_k(1)$. Summing this uniform inequality over any disk cover gives $h(S_M)\ge\nu_M(S_M)/(1+o_k(1))\to1$. The unit disk gives $h(S_M)\le1$. Thus $h(S_M)^k/h(E_M)\to k$.

### 4. Exact formula for one disk, including disconnected pullbacks

For a disk of positive radius with radial endpoint data $0\le a<b$ as in §1, the exact cost of covering its entire pullback is
$$
 h(D^{[1/k]})=\min\{b,\ k(b-a)/2\}.
$$
When $a=0$ only the central disk is needed, and $k(b-a)/2\ge b$; otherwise both upper bounds are §1. The disk contains its radial segment from $a^k$ to $b^k$ (in the direction of the center, with any direction when the center is zero). It suffices to bound the cost of covering the $k$ inverse segments joining radii $a$ and $b$ along a rotated regular $k$-star. Scale to $b=1$.

Given any finite disk cover of those segments, form the intersection graph of all its disks. Each connected component can be covered by a single disk of radius at most the sum of its radii: repeatedly merge intersecting disks, using the elementary two-disk bound. Each original segment belongs to the union of one such component, as it is connected and the unions from different components are disjoint compact sets. Assign the whole segment to that component. A merged disk assigned one segment has radius at least $(1-a)/2$. If assigned $m\ge2$ segments it contains $m$ vertices of a regular $k$-gon on the unit circle and has radius at least $m/k$. Indeed, when those tips are not in any open semicircle their convex hull contains the origin, and no disk of radius less than 1 can contain them; this follows, for instance, from a convex combination of the tips summing to zero and averaging their squared distances from the disk center. Otherwise, their shortest enclosing arc has angular width between $2\pi(m-1)/k$ and $\pi$. The separation of its endpoints gives radius at least $\sin(\pi(m-1)/k)\ge2(m-1)/k\ge m/k$. Each merged disk therefore pays at least $m\min\{(1-a)/2,1/k\}$, including the singleton case. Sum over the $k$ assigned tips to obtain the matching lower bound. The same formula holds for the pullback of the radial segment alone.

For the monic binomial $z^k-c$ the maximum over all $c$ of its actual disk-cover cost consequently equals
$$
 \left(\frac{2}{1-(1-2/k)^k}\right)^{1/k}.
$$
For $|c|\le1$ the central bound increases with $|c|$. Above 1 the central choice increases and the branchwise choice decreases by concavity of the root, so their crossing gives the maximum (at the threshold $|c|=1$ when $k=2$).

## Consequence for the original open problem

Erdős asked whether $K_P=\{|P|\le1\}$ for every nonconstant monic polynomial $P$ has a disk cover of total radius at most 2. Pommerenke proved a finite-cover bound less than $2.59$ for these sets (1960, Satz 3; these sets have capacity 1).

Suppose $P(z)=z^j q(z^k)$ with monic $q$, $0\le j<k$, $P$ nonconstant; rotations and translations of the variable do not affect the conclusion. Put $Q(w)=w^j q(w)^k$. It is monic and $P(z)^k=Q(z^k)$, so $K_P=(K_Q)^{[1/k]}$. The theorem gives an actual cover of cost less than $(2.59 k)^{1/k}$. At $k=3$ this is $7.77^{1/3}<2$, and for every $k\ge3$ we have $2.59k<2^k$. No restrictions on $q$, separation, multiplicities, degree, or connectedness are required.

This covers all monic polynomials whose zero multiset is invariant under a $k$-fold rotation about some point: in centered coordinates $P(\zeta z)=\zeta^{\deg P}P(z)$, forcing the displayed exponents. It also covers all $k$-fold invariant filled polynomial lemniscates themselves: the compact set equals the pullback of its image, and its image has capacity the $k$-th power of its capacity, by the standard monic polynomial preimage formula for logarithmic capacity. Alternatively, use the exterior maximum principle on $P(\zeta z)/P(z)$: on the boundary of $K_P$ its modulus is 1, it has no zeros or poles on the complement, and its value at infinity has modulus 1. Its log modulus vanishes throughout the unbounded component by the maximum principle there, so the rational function is constant by the open mapping theorem. This forces the same displayed form.

More generally, combining the sharp theorem with Satz 3 gives $h(K)<(2.59k)^{1/k}\operatorname{cap}(K)$ for compact $k$-fold invariant $K$ of positive capacity. A bound of $2\operatorname{cap}(K)$ thus holds for every such compact set when $k\ge3$. The strict statement uses the finite cover in Satz 3.

## A square-pullback corollary and its sharpness

The power inequality also propagates every known base cover of cost 2 through a square: if $K_q$ has such a cover, so does $K_{q(z^2)}$. In particular, a quantitative degree-sharp special case holds for monic real-rooted $q$ of degree $m$: $K_{q(z^2)}$ has a cover of cost at most $2^{1-1/(2m)}$. The roots of the composed polynomial may occupy both perpendicular axes and need not be bounded.

To see the base bound, let $S=\{x\in\mathbb R:|q(x)|\le1\}$. On a component interval $[a,b]$ take the disk with that diameter. For $x=(1-u)a+ub$, the upper and lower semicircle points $z$ satisfy $|z-r|^2=(1-u)|a-r|^2+u|b-r|^2$ for every real zero $r$. Weighted AM–GM and multiplication give $|q(z)|\ge1$, since $|q(a)|=|q(b)|=1$. Moving vertically farther away strictly increases every factor, and projection of $K_q$ lies in $S$. These diameter disks therefore cover $K_q$ with cost $|S|/2$, which is optimal by projection.

For completeness, $|S|=L\le 2^{2-1/m}$. Take the $m+1$ Chebyshev extrema $y_i$ in $[0,L]$ in increasing order and spread them to points $x_i\in S$ with the same quantiles of length; then $x_j-x_i\ge y_j-y_i$ for $j>i$. The divided-difference formula for the leading coefficient gives
$$
 1\le \sum_i\prod_{j\ne i}|x_i-x_j|^{-1}
 \le \sum_i\prod_{j\ne i}|y_i-y_j|^{-1}=2^{2m-1}/L^m.
$$
The last equality uses the alternating signs of $T_m(2y/L-1)$ at its extrema and its leading coefficient. Thus $h(K_q)\le 2^{1-1/m}$, and the constructive square-pullback theorem yields the claimed bound. Sharpness in degree $2m$ follows from the monic normalization $P(z)=T_{2m}(z/A)$, $A=2^{1-1/(2m)}$, whose filled lemniscate contains $[-A,A]$. It is of the form $q(z^2)$ with real-rooted monic $q$. This does not assert that the strictly non-collinear members alone attain equality.

## A lower bound for the best rotational covering constant

The sharp constant $k$ above refers to content relative to **content**, not to capacity. For comparison, put $t=(1-2/k)^k$ and $L_m=2^{2-1/m}$. Choose $B=L_m/(1-t)$, $A=tB$, and
$$
 q_m(w)=T_m\!\left(\frac{2w-A-B}{B-A}\right),\qquad P_m(z)=q_m(z^k).
$$
These are monic: the leading coefficient of $q_m$ is $2^{2m-1}/L_m^m=1$. Its real unit sublevel set is exactly $[A,B]$, and the real-root proof above places its complex unit sublevel set in the disk with this diameter. The inverse segment and inverse disk have the very same content by §4. At the chosen ratio, $k(B^{1/k}-A^{1/k})/2=B^{1/k}$. Hence
$$
 h(K_{P_m})=B^{1/k}
 =\left(\frac{2^{2-1/m}}{1-(1-2/k)^k}\right)^{1/k}.
$$
In particular if $C_k$ is the supremal disk-cover content of a monic polynomial lemniscate with $k$-fold rotational symmetry, then
$$
 \left(\frac{4}{1-(1-2/k)^k}\right)^{1/k}
 \le C_k\le(2.59k)^{1/k}.
$$
The lower bound is not claimed optimal. For $k=3$ it is $(54/13)^{1/3}$ against an upper bound $7.77^{1/3}$. For $k=2$ it approaches $2$, so no uniform strict improvement over 2 is possible for this symmetry.

## Sources, priority, residual obstruction

* P. Erdős, *Some unsolved problems*, 1961, p. 246, IV.1: [original paper](https://renyi.hu/~p_erdos/1961-22.pdf).
* Ch. Pommerenke, *Einige Sätze über die Kapazität ebener Mengen*, Math. Ann. 141 (1960), 143–152, Satz 3, p. 149: [publisher record](https://doi.org/10.1007/BF01360168).
* Ch. Pommerenke, *On metric properties of complex polynomials*, Michigan Math. J. 8 (1961), 97–115: [publisher record](https://doi.org/10.1307/mmj/1028998561). This is not the primary source for the 2.59 bound.
* Thomas Bloom, [problem 509](https://www.erdosproblems.com/509). The [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/509.lean) labels the general problem open. The [secondary claim index](https://erdosproblems.ai/wiki/problems/polynomials/E0509) records no accepted general proof and a July 2026 unreviewed degree-2-to-4 claim.
* Targeted searches for power-map disk-content distortion, rotational variants, and complex lemniscate-cover results did not locate this sharp inequality or the arbitrary-degree order-three corollary. This is not proof of bibliographic novelty. The root-of-one-disk step is standard fractional-power geometry; the global cutoff and the matching comb are the substantive steps.

The sharp factor 2 for a square pullback permits only the universal bound $\sqrt{2\cdot2.59}>2$. Improving a universal power-content inequality cannot remove that obstacle. More information about the quotient lemniscate, or an argument using capacity rather than its disk content, is needed for arbitrary twofold symmetry. No part of the proof establishes the conjecture for a general nonsymmetric polynomial.
