# A finiteness threshold for magnitude under pure dilation

**Theorem.** There is a *single* countably infinite compact metric space $X$ of strong negative type and box dimension zero such that
$$
 |tX|=\infty\quad(0<t\le1),\qquad |tX|<\infty\quad(t>1),\qquad
 |tX|\sim\frac{\log 2}{2\log t}\quad(t\downarrow1,\ t>1).
$$
There is also a space with the same metric-geometric properties whose finite scales form the **closed** ray $[1,\infty)$. In this case extended-valued magnitude is discontinuous at the finite scale 1. Every prescribed positive threshold in place of 1 is obtained by rescaling a single metric. The constructions are different spaces, and at no point is the distance perturbed as a function of the observation scale $t$.

This addresses a different issue from a failure of monotonicity on a finite space. [Leinster and Meckes](https://doi.org/10.1090/proc/16433) established the existence of compact negative-type spaces of infinite magnitude (in their examples at every positive scale). [Pendyala, Theorems 4.1 and 5.8](https://arxiv.org/html/2610.13958v1) gives a finite decrease and constructs a compact space of finite magnitude at all scales with anomalous magnitude dimension. Neither description is a positive-scale finiteness threshold of one fixed metric. A targeted literature search found no earlier mixed-finiteness theorem of the form above; do not represent that search as a complete priority determination.

## 1. A tunable finite branch

For $k\ge3$ take $2^k-1$ nonzero binary cube vertices and two apices. With a parameter $0<s\le1$, the distances are Hamming distances between cube vertices, $|v|+s$ between $v$ and either apex, and $4s$ between the apices. These are squared Euclidean distances on $(v,0)$ and $(0,\ldots,0,\pm\sqrt{s})$. All triangles hold: the only extra bound beyond the Hamming triangle and $||v|-|w||\le h(v,w)\le |v|+|w|$ is $4s\le2+2s$. Thus these are genuine negative-type metrics.

The exact magnitude at scale $\tau>0$ is
$$
\begin{aligned}
 q&=e^{-\tau},\quad \alpha=e^{-s\tau},\quad
 h=(1-q^2)^k,\quad \ell=(1-q)^k,\\
 M_{k,s}(\tau)&=\left(\frac2{1+q}\right)^k-\frac{\ell^2}{h}
 +\frac{2(1-\alpha+\alpha\ell)^2}{(1-\alpha^2)^2+2\alpha^2h}. \tag{1}
\end{aligned}
$$
For completeness let $A$ be the similarity matrix of the punctured cube and $u$ its column from the deleted origin, so $u_v=q^{|v|}$. In the full cube similarity matrix, which is the $k$-fold tensor power of the binary similarity matrix, the origin's inverse diagonal is $(1-q^2)^{-k}$, and its weight is $(1+q)^{-k}$. Block inversion therefore gives $1-u^TA^{-1}u=h$, $1-u^TA^{-1}\mathbf1=\ell$ and $M_A=(2/(1+q))^k-\ell^2/h$. In the new space both apex columns on the old block are $\alpha u$. After eliminating $A$, the symmetric eigenvalue of the two-apex Schur complement is $1+\alpha^4-2\alpha^2(1-h)$. The two coordinates of its residual right-hand side are each $1-\alpha+\alpha\ell$. The Schur magnitude identity gives (1).

For fixed $k\ge3$ and $b>0$, take a scale factor $r\downarrow0$ for the branch and couple the geometric parameter by
$$s^2=\frac{2^{k-1}}b\,r^{\,k-2}.$$
Eventually $s\le1$. For every compact interval $I\subset(0,\infty)$, uniformly for $t\in I$,
$$
       M_{k,s}(rt)\longrightarrow 1+\frac1{2(1+b t^{k-2})}. \tag{2}
$$
Indeed the first term in (1) tends to one and $\ell^2/h=((1-q)/(1+q))^k\to0$. Moreover $1-\alpha\sim srt$, $\ell=O(r^k)=o(srt)$, and $h\sim(2rt)^k$. Dividing the excess fraction by $4s^2r^2t^2$ in numerator and denominator gives numerator tending to $1/2$ and denominator tending to $1+b t^{k-2}$. These asymptotics are uniform on $I$ since $k$ is fixed and $t$ stays bounded above and away from zero. Uniformity in $k$ is neither asserted nor needed.

## 2. Assemble a single compact metric

Choose numbers $b_k>0$. For each integer $k\ge3$, choose $r_k>0$ so small that the scaled branch has diameter at most $e^{-k^3}/2$ and the absolute error in (2) on $[1/k,k]$ is at most $2^{-k-1}$. This is possible by the preceding fixed-$k$ limit. To every nonzero distance of this already-scaled branch add a single $\eta_k>0$. The kernel on the finite branch at scale $t$ becomes $e^{-t\eta_k} K(t)+(1-e^{-t\eta_k})I$ and stays positive definite. On the compact interval $[1/k,k]$, continuous matrix inversion (the minimum eigenvalue there is positive for this fixed finite branch) lets us make the additional magnitude error at most $2^{-k-1}$ by choosing $\eta_k$ sufficiently small. Take also $\eta_k\le e^{-k^3}/2$. The resulting branch $B_k$ has diameter at most $e^{-k^3}$ and is of strict negative type: the discrete perturbation subtracts $\eta_k\|z\|^2$ on zero-sum coefficients. Writing $m_k(t)=|tB_k|$, we now have
$$
 \left|m_k(t)-1-\frac1{2(1+b_k t^{k-2})}\right|\le 2^{-k}
                         \quad(1/k\le t\le k). \tag{3}
$$
No explicit lower bound on the very small $\eta_k$ is needed in this existence proof.

Identify one chosen point from each $B_k$ to a common root $o$ and use the sum of distances to $o$ between distinct branches. This countable metric wedge is compact since the branch diameters shrink to zero. Choosing each branch's squared-Hilbert realization with $o$ at the origin of a separate orthogonal summand realizes the full wedge by squared Hilbert distances. For a nonzero signed difference $\mu$ of probability measures, the distance energy is minus twice the squared norm of its barycenter; absolute convergence follows from compactness and finite total variation. If that barycenter vanishes, projecting to each summand forces all nonroot masses there to vanish by linear independence of the nonroot vectors, which is equivalent to strict negative type in that finite branch. The remaining root mass is zero. This proves **strong** negative type.

If $e^{-(j+1)^3}\le \rho<e^{-j^3}$, the root ball of radius $\rho$ covers all branches $k\ge j+1$. The earlier branches have at most $\sum_{k=3}^j(2^k+1)$ points. The logarithm of the covering number is therefore $O(j)$, while $\log(1/\rho)\ge j^3$; the box dimension is zero.

For a finite wedge the magnitude equals one plus the sum of the branch excesses: combine weightings at the root, subtracting one common weight at each successive identification. This works since cross-branch similarities factor via the root. Every finite subset is contained in finitely many branches, so taking finite-subset suprema (the definition of compact negative-type magnitude) and using inclusion monotonicity gives the exact extended-valued identity
$$
                  |tX|=1+\sum_{k\ge3}(m_k(t)-1). \tag{4}
$$
All summands are nonnegative, since each contains a singleton. In particular for each fixed $t>0$, (3) shows that (4) converges **if and only if**
$$
               \sum_{k\ge3}\frac1{1+b_k t^{k-2}}<\infty. \tag{5}
$$
Only finitely many $k$ fail $1/k\le t\le k$, and all finite-branch magnitudes are finite.

## 3. Read off the transition

Set $b_k=1$. For $0<t\le1$ each model summand in (5) is at least $1/2$; for $t>1$ geometric comparison gives convergence. On $1<t\le2$, (3) holds for every $k\ge3$, so
$$
 |tX|=\frac12\sum_{n=1}^\infty \frac1{1+e^{n\log t}}+O(1)
$$
with an error uniformly bounded even as $t\downarrow1$. By the left and right integral estimates for the positive decreasing integrable function $(1+e^x)^{-1}$, the sum times $\log t$ tends to $\int_0^\infty(1+e^x)^{-1}\,dx=\log 2$. This proves the sharp asymptotic.

Instead choose $b_k=k^2$. For $t<1$, $k^2t^{k-2}\to0$ and the series diverges. For $t\ge1$, comparison with $\sum k^{-2}$ gives convergence even at the endpoint. The two alternatives prove the theorem.

**Scope.** The half-ray result respects submultiplicativity $|(s+t)X|\le |sX||tX|$; finiteness must be closed under addition. This theorem does not classify all possible additive sets of finite scales. No claim is made about realizations in finite-dimensional Euclidean normed spaces.
