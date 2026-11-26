# The partition law uniquely maximizes late discrete coupon coverage

**Theorem.** Write $n=qs$, $q\ge2, s\ge1$. Independently draw $m$ random subsets of $[n]$ with common law $\mu$, each of cardinality at most $s$ (the empty set is allowed). If
$$
m\ge256n\log(2n),
$$
the probability of covering $[n]$ is uniquely maximized, up to relabeling, by drawing uniformly from $q$ disjoint $s$-sets. The maximum is $q!\left\{\genfrac{}{}{0pt}{}{m}{q}\right\}/q^m$. The logarithm is natural. For $q=1$, the unique maximizing law for finite $m\ge1$ puts all mass on $[n]$: repeating any supported proper set would fail.

The quantifiers are uniform: the competing law can change with the deadline. This is a partial answer to Long's Conjecture 8.1, not a proof at all deadlines. No computational assumption enters the proof.

### 1. A candidate maximizer has well-separated incidence clusters

Let $p=1/q, a=1-p$; $E_i$ is the event coupon $i$ is missing after $m$ draws, $H=\Pr(\bigcup_i E_i)$, and $p_i=\Pr(i\in A)$ for one draw. For the partition law $D$, $H_D\le qa^m$ by the union bound. Assume $H\le H_D$; we prove $\mu=D$ up to labels. Put
$$
h_i=(1-p_i)/a,\qquad z_i=h_i^m.
$$
Then $z_i\le q$ and $\sum_i h_i\ge n$, since $\sum p_i\le s$. Also $p_i\ge1-aq^{1/m}\ge p-2\log(q)/m\ge p/2$: use $e^u-1\le2u$ for $0\le u\le1$, and the stipulated bound on $m$.

Join two coupons if the probability $d_{ij}$ that **exactly one** belongs to a draw is less than $\delta=1/(4n)$. Every component has at most $s$ vertices. Otherwise take a connected tree on $s+1$ of them (grow a tree by one vertex at a time). With probability at least $p/2-s\delta>0$, its root is drawn and none of its $s$ edges disagrees; this would put $s+1$ coupons in a package.

For coupons in different components, $d_{ij}\ge\delta$. The probability a draw misses both is
$$
1-(p_i+p_j+d_{ij})/2\le a q^{1/m}-\delta/2.
$$
Using $a q^{1/m}\le2$ and $1-u\le e^{-u}$ gives
$$
\Pr(E_i\cap E_j)/a^m\le q\exp[-m/(16n)].
$$
Let $U_C=\bigcup_{i\in C}E_i$, and $R=n^2q\exp[-m/(16n)]\le n^3(2n)^{-16}$. Bonferroni on the components, followed by the union bound for their pair intersections, gives
$$
q\le s^{-1}\sum_i z_i\le\sum_C\Pr(U_C)/a^m\le H/a^m+R\le q+R. \tag{1}
$$
The first step is Jensen and $\sum h_i\ge n$; the second uses $|C|\le s$. Both the accumulated Jensen excess and the accumulated within-component loss are therefore small.

In fact $z_i>1/4$ for all $i$. For $u\ge0$, $g(u)=u^m-1-m(u-1)\ge0$; by (1), $\sum_i g(h_i)\le sR<1/4$. On $0\le u\le4^{-1/m}$, $g$ is decreasing and $g(4^{-1/m})=-3/4+m(1-4^{-1/m})\ge1/4$ for $m\ge2$. The last bound follows because $v(1-e^{-b/v})$ is increasing for $v>0, b=\log 4$, and equality in this numerical bound holds at $v=2$.

Each component has size exactly $s$: otherwise its contribution $\Pr(U_C)/a^m-s^{-1}\sum_{i\in C}z_i$ exceeds $1/(4s)>R$, using the largest $z_i$ in the component. Thus the components themselves give a partition into $q$ blocks.

### 2. Almost every package must be a whole block

From (1) and nonnegativity of all component losses, for $i,j\in C$
$$
\Pr(E_i\setminus E_j)/a^m\le [\Pr(U_C)-\Pr(E_j)]/a^m\le sR.
$$
Write $b=\Pr(j\in A,\ i\notin A)$. Independence gives
$$
\Pr(E_i\setminus E_j)/a^m
=z_i\left[1-\left(1-\frac b{1-p_i}\right)^m\right]
\ge\tfrac14(1-e^{-mb}).
$$
Thus $mb\le-\log(1-4sR)\le8sR$ since $4sR<1/2$. This bounds *each directed* within-block disagreement. The size deficiency also satisfies
$$
m(s-\sum p_i)/a\le \sum_i(z_i-1)\le sR
$$
by the tangent inequality $h_i^m\ge1+m(h_i-1)$.

Write $\varepsilon$ for the probability of a package not equal to one of the blocks. Such a package either has size less than $s$, or splits at least one block. Since $s-|A|$ is integer, a union bound over directed pairs yields
$$
m\varepsilon\le asR+8n^2sR\le9 n^3R<1/(64q^2). \tag{2}
$$
For the final numerical inequality use $R\le2^{-16}n^{-13}$ and $2\le q\le n$.

### 3. A single defective draw is strictly costly

Conditioning on drawing a whole block gives a $q$-label law $\nu=(r_1,\ldots,r_q)$. Its least weight $r=\min_j r_j$ is at least $1/(4q)$: a coupon in a block has $p_i\le(1-\varepsilon)r_j+\varepsilon$, whereas $p_i\ge1/(2q)$ and $\varepsilon<1/(64q^2)$. Write $F(t)$ for the completion CDF of this single-label law, $H_\nu(t)=1-F(t)$, and $D_m=F(m)-F(m-1)$. By insisting that a least-weight label be the last to arrive and subtracting the chance of any other missing label,
$$
D_m\ge r(1-r)^{m-1}
[1-(q-1)e^{-r(m-1)}]\ge(r/2)(1-r)^{m-1}.
$$
Indeed, conditional on avoiding that label, each other label has weight at least $r/(1-r)\ge r$; $m\ge256n\log(2n)$ ensures the bracket is at least $1/2$. As $H_\nu(m)\le q(1-r)^m$, we obtain $D_m\ge H_\nu(m)/(8q^2)>0$.

Let $K\sim\mathrm{Bin}(m,\varepsilon)$ count defective draws. Given $K=0$, completion has probability $F(m)$. Given $K=1$, it has probability exactly $F(m-1)$: no single defective package contains a whole block, while good draws either cover an entire block or miss it entirely. Given $K\ge2$, even crediting the process certain success only gains $H_\nu(m)$ over the baseline $F(m)$. If $\varepsilon>0$, then
$$
\frac{\Pr(K\ge2)}{\Pr(K=1)}
\le \frac{\binom m2\varepsilon^2}{m\varepsilon(1-\varepsilon)^{m-1}}
\le\frac{m\varepsilon}{2(1-m\varepsilon)}
<1/(8q^2)
$$
by (2). Mixing the three cases shows $1-H<F(m)$.

Finally $F(m)\le1-H_D$, strictly unless all positive block probabilities equal $1/q$. For completeness, average any two unequal positive block weights while preserving their sum. Conditional on the positions drawn from this pair and on the other labels, the probability of seeing both in $k\ge2$ pair positions is $1-x^k-(1-x)^k$, uniquely maximized at the equal split. For $m\ge q$ and positive weights, the case where every other label is present and $k\ge2$ has positive probability. The continuous function on the probability simplex achieves a maximum; its boundary gives zero, and unequal interior weights can be strictly improved, proving the assertion. Thus positive $\varepsilon$ contradicts $H\le H_D$; at $\varepsilon=0$ the same strictness forces uniform block weights. This proves the theorem.

### Source, scope, obstruction

Christopher D. Long, [*Optimal coupon packages and stochastic improvement of uniform group drawings*](https://hexagonmath.org/2611.00814v1), Hexagon preprint v1, Nov 21 2026, [Conjecture 8.1 and Proposition 3.4](https://hexagonmath.org/pdf/2611.00814v1). Long explicitly asks for every discrete deadline, proves the first feasible one $m=q$, and obtains stochastic optimality after Poissonization. His incidence-class argument for equality of the continuous-time optimum is relevant prior work. Neither a transform inequality nor dominance for each fixed rival beyond a rival-dependent time implies the uniform theorem here. Fang and Chang's [2014 paper](https://doi.org/10.1016/j.ipl.2014.06.012) already treats $q=2$. Berend and Sher's [2026 paper](https://doi.org/10.1080/15326349.2026.2671340) concerns Schilling's different question about uniformity over *all* packages. A targeted search for fixed-draw, eventual, and uniform late-deadline results found no matching theorem; **this is not a priority assessment or peer review**.

For fixed $q,s$, only finitely many horizons remain between $q+1$ and $256n\log(2n)$; this is not a finite reduction over all $q,s$. The bottleneck is the additive cross-cluster intersection loss $R$, unusable at short times where collisions occur frequently. The numerical constant has not been optimized.
