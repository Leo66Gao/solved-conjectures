# Why the cubic interpolation mechanism starts with eight cube vertices

This observation concerns the specific mechanism behind the split-corner construction. It does **not** assert that every metric with fewer than nine points has increasing magnitude.

**Proposition.** Let $F$ be a finite negative-type metric space, realized by squared distances on distinct vectors $p_i$ (Schoenberg). If $|F|\le7$, no nonzero signed combination of its points annihilates all polynomials of degree at most two in the $p_i$. If $|F|=8$, the only exception, up to isometry of the affine span, is the set of vertices of a rectangular three-dimensional box. Consequently, unless this box exception occurs, for every such $F$ with at most eight points its similarity kernel obeys $\lambda_{\min}(K(t))\ge c_F t^2$ for all sufficiently small $t>0$. At a box the least eigenvalue really has cubic order.

**Proof.** Suppose $w\ne0$ annihilates constants, linear polynomials and quadratics. Separately normalize the positive and negative parts to probability vectors. Their mean $m$ and covariance matrix $\Sigma$ coincide by moment matching. The range of a finite mixture's covariance is exactly the linear span of its support translated by $-m$: this follows by testing a vector against its variance. Hence both affine support spans are the same $r$-plane. Each side needs at least $r+1$ points there, so $2r+2\le\#\operatorname{supp}w\le8$. The number $r$ is positive as supports are disjoint and points are distinct. The triangle inequalities for squared distances say that every triangle is nonobtuse. By the [Danzer–Grünbaum theorem](https://doi.org/10.1007/BF01193107) a nonobtuse set in $r$-space has at most $2^r$ points, with equality only for a rectangular parallelotope. In dimensions one and two this contradicts $2r+2\le 2^r$. Thus $r=3$, the support has eight points, and the equality classification forces a rectangular box. Conversely the alternating parity weights on its corners annihilate every polynomial of degree at most two.

For the eigenvalue estimate, the no-stress condition says the linear map
$$
 (c_i)_i\longmapsto(\sum c_i,\ \sum c_i p_i,\ \sum c_i p_i^{\otimes2})
$$
has positive least singular value. Write $v_i=c_i e^{-t\|p_i\|^2}$. Expanding $e^{2t\langle p_i,p_j\rangle}$ in tensor powers and retaining only degrees zero through two gives
$$
 c^TK(t)c\ge \left|\sum v_i\right|^2+
      2t\left\|\sum v_i p_i\right\|^2+
      2t^2\left\|\sum v_i p_i^{\otimes2}\right\|^2 .
$$
For $0<t\le1$, the right-hand side is at least a fixed positive constant times $t^2\|c\|^2$, as the diagonal factors taking $c$ to $v$ are bounded below. For a box with squared edge lengths $L_1,L_2,L_3>0$, $K(t)$ is a tensor product of three two-point kernels. Its least eigenvalue is $\prod_{j=1}^3(1-e^{-tL_j})\sim t^3\prod_jL_j$, proving sharpness.

In the corner-splitting proof the crucial residual for a base site $o$ is $h=1/(K(t)^{-1})_{oo}$, the Schur complement after the other sites are eliminated. It is at least $\lambda_{\min}(K(t))$. Thus the order-$t^3$ residual used in that construction cannot occur for any negative-type base on at most seven points. A base of order eight can achieve it only on a rectangular box. Replacing one of its corners by two points then produces nine points, as in the explicit counterexample. Different mechanisms at smaller orders are not excluded.
