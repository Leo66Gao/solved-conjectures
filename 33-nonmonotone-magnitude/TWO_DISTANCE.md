# All two-distance negative-type metrics on at most eight points are monotone

**Theorem.** Suppose a nonempty metric space $X$ has at most eight points, is of negative type, and takes at most two distinct nonzero distances. Then $t\mapsto |tX|$ is strictly increasing for $t>0$ unless $X$ is a singleton, in which case it is constant 1. In particular, any four- through eight-point counterexample to dilation monotonicity must have **at least three distinct nonzero distances**. This is not a proof of unrestricted nine-point minimality.

We prove a more general degree-variance criterion, valid at any cardinality. Here and below $n$ denotes the number of points, not their magnitude. An equidistant space with common distance $d$ has magnitude $n/(1+(n-1)e^{-td})$, so assume there are two distances, normalized by dilation to $1<r$ and $1$. Let $A$ be the adjacency matrix of the short-distance graph: an edge is a pair at distance 1. Let $d$ be its mean vertex degree and $V$ the variance of its vertex degrees, with the uniform distribution on the $n$ vertices.

**Criterion.** If $1<r\le2$ and $X$ is of negative type, its magnitude is strictly increasing whenever
$$
                 V<n-1-d(1-1/r).
$$
In particular $V<n-1-d/2$ suffices independent of $r$ in this range.

**Proof.** Write $q=e^{-t}$, $p=e^{-rt}$, $u=q-p$, $x=(1-p)/u$, $\kappa=r/(r-1)$, $C=\kappa I+A$, $z=x-\kappa$ and $e=\mathbf1/\sqrt n$. We have
$$
   K(t)=pJ+u(zI+C),\qquad D=r(J-I)-(r-1)A.
$$
The compression $C_\perp$ of $C$ to $e^\perp$ is positive semidefinite by negative type of $D$. Also $z(0+)=0$ and $z'(t)>0$: the nonconstant part $x-1=(e^t-1)/(1-e^{-(r-1)t})$ is the product of the positive strictly increasing functions $(e^t-1)/t$ and $t/(1-e^{-(r-1)t})$.

Put $b=(I-ee^T)Ce$ and expand $b$ in an orthonormal eigenbasis of $C_\perp$, with coordinates $b_i$ and eigenvalues $\lambda_i\ge0$. We have $e^TCe=\kappa+d$ and $\sum b_i^2=\|b\|^2=V$. For the positive definite kernel, $E(t)=1/|tX|$ is the minimum of $w^TK(t)w$ over real $w$ of mass one; this follows by the weighted Cauchy–Schwarz inequality or Lagrange multipliers. Writing $w=e/\sqrt n+v$ with $v\perp e$ and completing squares in each eigendirection gives
$$
 nE(t)=1+dq+(n-1-d)p-\sum_i b_i^2 g_{\lambda_i}(t),
 \qquad g_\lambda(t)=\frac{u}{z+\lambda}. \tag{1}
$$
In particular no sign is assumed for the weighting.

We claim $-g'_\lambda(t)\le r p$ for all $\lambda\ge0$. Put $y=1/(z+\lambda)$, so $0\le y\le1/z$. Then $-g'_\lambda=-u'y+u z'y^2$ is convex as a function of $y$, and hence is bounded by $\max(0,-g'_0)$. It suffices to prove $-g_0'\le rp$.

For this scalar estimate set $a=r-1\in(0,1]$, $b_0=1-a$, and
$$
 F_{\rm slow}(t)=(1-e^{-at})^2,\quad
 F_{\rm fast}(t)=1-\frac{1+a}{a}e^{-t}+\frac1a e^{-(1+a)t}.
$$
Since $g_0=u^2/(1-p-\kappa u)$, direct algebra gives
$$                       g_0=e^{-2t}F_{\rm slow}/F_{\rm fast}. \tag{2} $$
Both $F$'s are distribution functions of sums of independent exponential variables: their rate pairs are $(2a,a)$ and $(1+a,1)$, respectively (integrate the product densities on $x,y\ge0,\ x+y\le t$). At each pair $(x,y)$ the slow joint density divided by the fast joint density is $c_0 e^{b_0(x+y)}$, with $c_0=2a^2/(1+a)$. Consequently $F_{\rm slow}/F_{\rm fast}=c_0\,\mathbb E_{\rm fast}[e^{b_0T}\mid T\le t]$ for the fast sum $T$. This is nondecreasing in $t$, and is at most $c_0e^{b_0t}$. By (2), $-g'_0\le2g_0\le 2c_0 e^{-(2-b_0)t}\le rp$. The last inequality is $4a^2\le(1+a)^2$, true for $a\le1$. This proves the claim, including at $a=1$.

Differentiating (1) now gives
$$
  -nE'(t)\ \ge\ d q+r(n-1-d)p-rpV
  \ \ge\ rp\big(n-1-d(1-1/r)-V\big)
$$
since $q\ge p$. Strict positivity proves the criterion.

If $r>2$, two length-one edges sharing a middle vertex must have their other endpoints at distance one (else the triangle fails). Thus the short-edge graph is a union of cliques. Write $K=T+pJ$, where $T$ is block diagonal with clique blocks $(1-q)I+(q-p)J$. On a clique of size $k$ the entries of $T^{-1}\mathbf1$ are all $1/[1-q+k(q-p)]>0$. Normalizing that vector by $1+p\,\mathbf1^TT^{-1}\mathbf1$ gives the full weighting $w$, hence all entries of $w$ are positive. The derivative of magnitude is $w^T(D\circ K)w>0$ for a nonsingleton. This also works at any $r>1$ for a union of cliques.

## Checking the size bound without enumerating metrics

For $2\le n\le8$, a short exact integer/rational check proves that **every** simple graph satisfies $n-1-d/2-V>0$. Sort its degree sequence $d_1\ge\cdots\ge d_n$. All degrees are in $\{0,\ldots,n-1\}$ and have even total sum. For every $k$,
$$
 \sum_{i\le k}d_i\le k(k-1)+\sum_{i>k}\min(k,d_i).
$$
This follows by counting contributions from edges inside and outside the first $k$ vertices. Enumerate the degree multisets and discard only those failing these necessary conditions; there is no need to assume sufficiency. Among the retained multisets the exact minima of $n-1-d/2-V$, in order $n=2$ through $8$, are
$$
    \frac12,\quad 1,\quad \frac32,\quad \frac{34}{25},\quad
    \frac{10}{9},\quad\frac{39}{49},\quad\frac7{16}.
$$
The 15-line standard-library program `verify_degree_bound.py` reproduces these rational bounds. This completes the proof for all real distance ratios, not just numerical samples or rational exponents.

### Independent integer-ratio and deletion checks

For comparison, `enumerate_graphs.cpp` and `verify_two_distance.py` independently verify the ratio $1:2$ by exhaustive graph enumeration and an entirely different polynomial test. For a graph $A$ put $P(z)=\det(zI+2I+A)$ and $H(z)=\mathbf1^T\operatorname{adj}(zI+2I+A)\mathbf1$. Then $H/n$ is the characteristic polynomial $\det(zI+C_\perp)$ with $C=2I+A$; its roots are real, so negative type is equivalent to all coefficients of $H$ being nonnegative. At $z=e^t-1$, direct rank-one update gives $|tX|=(1+z)^2 H(z)/(zP(z)+H(z))$. The quotient holds by polynomial continuation even where $P(z)=0$. The two characteristic/cofactor polynomials are calculated using integer powers, Newton identities and the adjugate expansion at infinity. The derivative numerators in $z$ all have nonnegative coefficients and a positive coefficient for nonsingletons. There are 2,390 negative-type graphs out of the 12,346 isomorphism classes on eight vertices. The graph generator extends each class on $n-1$ vertices by all new incident edge subsets. It computes canonical colored vertex orders by stable neighbor refinement and tries *every* permutation within the stable cells; thus it neither loses classes nor identifies nonisomorphic ones.

A third exact check, `verify_cube_deletions.py`, shows that all 501 proper nonsingleton induced subspaces of the *unperturbed* nine-point split cube in `NINE_POINTS.md` are strictly increasing at every scale. Each similarity determinant is a polynomial in $q=e^{-t}$; so is minus the determinant bordered by ones and a zero corner, giving the numerator. The verifier expands determinants by the exact subset recurrence and shows positivity of minus the quotient derivative by substituting $q=z/(1+z)$: all coefficients after clearing the positive denominator are nonnegative, with at least one positive. This is a lower bound *inside this witness*, not an unrestricted minimality proof.

Reproduce with `python verify_degree_bound.py` and `python verify_cube_deletions.py`. The optional graph-by-graph independent check uses `c++ -O2 -std=c++17 enumerate_graphs.cpp -o enum && ./enum | python verify_two_distance.py`.
