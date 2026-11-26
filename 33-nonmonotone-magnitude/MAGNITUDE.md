# How violently can magnitude fall when spatial resolution increases?

## Two results

Write $M_X(t)=|tX|$ for the magnitude of a metric space rescaled by $t>0$.

**Theorem A $one strongly negative-type space, unbounded drops$.** There is a countably infinite compact metric space $X$ of strong negative type, with finite, continuous magnitude at all positive scales, such that its box dimension and its magnitude dimension both exist and equal zero. Nevertheless, for some $t_j\to\infty$ and $c_j\downarrow1$,
$$
                 M_X(t_j)/M_X(c_jt_j)\longrightarrow\infty .
$$
The factors $c_j>1$ may be prescribed if they tend to 1; the lower bounds on the ratios may be any prescribed finite numbers tending to infinity (after discarding a finite prefix). Indeed $M_X(t)\to\infty$, so this is a fall between two growing values, not a vanishing or singular denominator.

**Theorem B $regular Cantor spaces$.** For every $s>0$, $L>1$ and $\delta>0$ there exist an Ahlfors $s$-regular compact metric space $Y$ of negative type, $1<c<1+\delta$, $a>0$, and $R>1$, for which
$$
     M_Y(aR^k)>L M_Y(caR^k) \qquad (k=0,1,2,\ldots).
$$
Both dimensions of this space equal $s$. The space depends on $s,L,\delta$. In particular, B does **not** assert unbounded drop ratios on one fixed Ahlfors-regular space. These theorems are about changing all distances by the same factor, not changing the space by an arbitrary small distortion.

### Context and verification

One decrease already refuted the original monotonicity question: this is due to V. S. Pendyala, [Thirteen Results in Magnitude Theory](https://arxiv.org/html/2610.13958v1), Theorem 4.1. Theorem 5.8 of that preprint also combines powers and wedges to separate growth dimensions; Theorem 5.7 obtains instability under nonuniform metric perturbations across different spaces. Neither result is claimed here. Gomi and Tsuji [discuss the preceding monotonicity problem](https://arxiv.org/html/2608.15720v1) and distinguish semimetrics from genuine metrics. The finite product rule and large-scale limit are classical; see [Leinster](https://ems.press/journals/dm/articles/8965346) and [Leinster–Meckes](https://arxiv.org/abs/1606.00095). Matsuda and Yukita [give log-periodic asymptotics](https://arxiv.org/abs/2607.26948) for self-similar ultrametric Moran sets; log periodicity alone does not imply a decrease in magnitude. Searches for oscillations, magnitude scale instability, and nonmonotone metric magnitude located no preceding assertion of A or B, but cannot establish priority. These are strengthenings using known ingredients, not a first disproof of the historical conjecture.

For a finite set $F$, $K(t)_{xy}=e^{-t d(x,y)}$ and $M_F(t)=\mathbf1^T K(t)^{-1}\mathbf1$. A metric is of negative type if $u^TDu\le0$ for all finitely supported zero-sum vectors; strict negative type means strict inequality for nonzero such vectors. For a negative-type metric on distinct points the finite kernels are positive definite for every $t>0$ (Schoenberg). For compact spaces of negative type take the supremum of the finite-subset magnitudes. Finite-subset monotonicity follows from the variational identity $M_F=\sup_{u\ne0}(\sum u)^2/(u^TKu)$. This inclusion monotonicity is not dilation monotonicity. Strong negative type means the strict energy inequality also holds for each nonzero difference of two probability measures.

## The finite seed and elementary facts

Let $F$ be the explicit nine-point strict-negative-type metric in [Nine points suffice](NINE_POINTS.md), and write $f(t)=M_F(t)$. It has $f(t_1)>f(2t_1)$ by exact rational calculations. The mean-value theorem and real analyticity between these positive scales give some $a>0$ with $f'(a)<0$. As any two distinct points already have magnitude $2/(1+e^{-td})>1$, inclusion monotonicity gives $f(a)>f(ca)>1$ for every $c>1$ sufficiently close to 1. Alternatively the 14-point seed of Pendyala with the rational perturbation tested in verify.py also suffices.

For any finite strict-negative-type $B$, $g(t)=M_B(t)=1+O(t)$ at zero and tends to $\#B$ at infinity. For the former, in the decomposition along $e=\mathbf1/\sqrt n$ and $e^\perp$, $K(t)=J-tD+O(t^2)$ has scalar top block $n+O(t)$, off-diagonal block $O(t)$, and bottom block $t(H+O(t))$ for positive definite $H=-D|_{e^\perp}$ as a quadratic form. Its scalar Schur complement is $n+O(t)$; $g(t)$ is $n$ divided by this scalar. At infinity $K(t)=I+O(e^{-\ell t})$ for minimum separation $\ell>0$. In particular $g$ is bounded, continuous, and $0\le g(t)-1\le H_B\min(1,t)$ with a finite $H_B$.

**Amplification.** The $m$-fold Cartesian power with sum distance has kernel $K(t)^{\otimes m}$ and magnitude $f(t)^m$; its metric is of negative type by taking zero-sum marginals in each coordinate. It is generally *not* of strict negative type. Adding $\eta>0$ to each nonzero distance adds $-\eta\sum_x w_x^2$ to the distance quadratic form on zero-sum vectors, making it strict. Magnitude at each fixed positive scale is continuous in $\eta$ at zero by finite matrix inversion.

## Proof of A

Fix large desired ratios $h_j\to\infty$ and $c_j\to1$ in the seed's decreasing range; put $b_j=c_ja$. Inductively maintain $S_0=0$, $S_j=\sum_{i\le j}H_i$. Knowing $S_{j-1}$, take a large power $m_j$ satisfying
$$
 f(a)^{m_j}> 2h_j\big(f(b_j)^{m_j}+S_{j-1}+1\big).
$$
This is possible because $f(a)/f(b_j)>1$ and $f(a)>1$. Perturb off-diagonal distances by a sufficiently small positive number as above, obtaining a finite strict-negative-type $B_j$ with magnitude $g_j$ satisfying the same inequality with factor $h_j$ in place of $2h_j$. Pick $H_j\ge1$ bounding its cardinality, diameter, and $(g_j(u)-1)/\min(1,u)$ at every $u>0$. Having selected $B_j,H_j$, choose an increasing threshold $T_j\ge(2+S_j)^j$ so large that $T_j>c_{j-1}t_{j-1}+1$ for $j>1$, then choose $s_j>0$ with $s_jH_j\le 2^{-j}/T_j$ and $t_j=a/s_j>T_j$. This ordering removes any circular dependency.

Wedge the pointed spaces $s_jB_j$ at one point $o$, retaining within-branch distances and adding distances to $o$ for distinct branches. Diameters tend to zero, so the countable space is compact. The wedge embeds by squared Hilbert distances: take each pointed Schoenberg realization at the origin of a separate orthogonal summand and use their union. For a bounded, countably supported signed measure of mass zero the distance energy equals minus twice the squared norm of its barycenter in this Hilbert space, by expansion and absolute convergence. A zero barycenter forces each branch's nonroot coefficients to vanish: strict negative type in that finite branch says the vectors at those points, relative to the root, are linearly independent. The root mass then vanishes too. This proves strong negative type.

For two branches, combining their weightings and subtracting one unit of weight at $o$ solves the weighting equation because $e^{-td(x,y)}=e^{-td(x,o)}e^{-td(o,y)}$ across branches. Thus the finite wedge magnitudes add with one subtracted per identification. Every finite subset lies in finitely many whole branches, so inclusion monotonicity gives exactly
$$
              M_X(t)=1+\sum_{j\ge1}\big(g_j(s_jt)-1\big).
$$
Each summand is nonnegative and bounded by $2^{-j}t/T_j$; the series converges uniformly on compact scale intervals. In particular $M_X(t)=1+O(t)$ at zero. For $T_j\le t<T_{j+1}$ the tail after branch $j$ is at most $2^{-j}$; hence $M_X(t)\le 2+S_j\le t^{1/j}$. Each of those tail branches also fits inside the *one* radius-$1/t$ ball at $o$, giving $N_X(1/t)\le 1+S_j$. These estimates prove both zero dimensions. The lower bound on the magnitude comes from arbitrarily large finite subsets and their finite-space limits at infinity.

Both endpoint scales $t_j,c_jt_j$ belong to $[T_j,T_{j+1})$. At the smaller one $M_X(t_j)\ge g_j(a)$. At the larger one $M_X(c_jt_j)\le g_j(b_j)+S_{j-1}+1$. This proves the stated ratio.

## Proof of B

Choose $c\in(1,1+\delta)$ as above, set $b=ca$, and $n=9$. For a positive integer $m$ let $E=F^m$ have sum metric, $q=n^m$ points, and $R=q^{1/s}$. On $Y=E^{\mathbb N_0}$ put $d(x,y)=\sum_{j\ge0}R^{-j}d_E(x_j,y_j)$. Total diameter is finite. The weighted sum has negative type by taking limits of the finite-coordinate quadratic forms. Distinct points have positive distance. If the first differing index is $j$, distance lies between $\ell_E R^{-j}$ and $(\operatorname{diam}E)/(1-R^{-1})\,R^{-j}$. Thus the metric is bi-Lipschitz to the first-difference ultrametric. A length-$j$ cylinder has uniform product mass $q^{-j}=R^{-sj}$, proving compactness and Ahlfors $s$-regularity (ball masses trapped between adjacent cylinder masses at scales differing by fixed factors).

Pin all but the first $N$ coordinates to one letter. The union of the resulting increasing finite prefix spaces is dense. To see that their magnitudes exhaust $M_Y(t)$, approximate each member of any finite subset by truncations; they are eventually distinct and entrywise convergence to its invertible Gram matrix gives convergence of its magnitude. By taking finite products,
$$
             M_Y(t)=\prod_{j\ge0} f(tR^{-j})^m .
$$
The product is finite and continuous on positive compact scale intervals since $\log f(u)=O(u)$ at zero. Now put $D(u)=\log f(au)-\log f(bu)$. Then $D(1)>0$, $D(u)=O(u)$ at zero, and $D(u)=O(e^{-\gamma u})$ at infinity for some $\gamma>0$, by the finite seed estimates above. At $aR^k,bR^k$, the logarithmic drop is $m\sum_{i=-\infty}^{k}D(R^i)$. For $R\to\infty$, the sum of the absolute values of the terms at $i\ne0$ tends to zero, uniformly in $k\ge0$: the negative indices have geometric sum $O(1/(R-1))$; the positive ones are dominated by a constant times $\sum_{i\ge1} e^{-\gamma R^i}$. Since $R=n^{m/s}\to\infty$, choose $m$ so that this error is below $D(1)/2$ and $mD(1)/2>\log L$. This proves every claimed drop. Finally, for $t=uR^k,\ 1\le u\le R$,
$$
      M_Y(t)=M_Y(u)q^k\prod_{i=1}^k [f(uR^i)/n]^m.
$$
The last product is bounded above and away from zero uniformly in $k,u$, by exponential convergence to $n$ and positivity of the finitely many early terms. Thus $M_Y(t)\asymp t^s$. This proves the magnitude-dimension assertion and finishes the proof.

**Limits of the results.** The constructions need not embed isometrically into a finite-dimensional Euclidean normed space. The fixed-space unbounded instability in A does not settle whether one fixed Ahlfors-regular space can have such drops, nor does either amplification identify the smallest metric seed. Finiteness and continuity at every positive scale in A are proved, so its drops are not finite-scale discontinuities.
