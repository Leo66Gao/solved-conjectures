# Fixed-deadline coupon coverage for all balanced package laws

**Theorem.** Let $n=qs$, with positive integers $q,s$. At each draw choose a package of at most $s$ coupons. Suppose, conditional on every past history, each coupon has inclusion probability $1/q$. Then at every integer deadline $m$, the probability of full coverage is at most $q!{m\brace q}/q^m$. The iid uniform law on the blocks of an $s$-set partition attains the bound. Among iid balanced laws it is the unique maximizer up to relabeling at each feasible deadline $m\ge q$. For iid draws this proves the full *balanced-marginal case* of [Long's Conjecture 8.1](https://hexagonmath.org/pdf/2611.00814v1). Unequal marginals are not treated here. Each draw necessarily has size $s$ since its expected size meets the cap.

**Proof strategy.** The normalized count $Y$ of covered coupons increases by at most one with conditional mean increment $(q-Y)/q$. The partition law has the same drift but integer jumps. We construct a family of convex functions for a one-step comparison. Linear interpolation at integer states does not suffice. The functions below interpolate hypergeometric probabilities by starting a without-replacement recurrence from a fractional first step.

Write $(v)_r=v(v-1)\cdots(v-r+1)$, $(v)_0=1$. Put $b_0=1$ and, on integers $0\le j\le q$, put $b_r(j)=(j)_r/(q)_r$ for $1\le r\le q$. On $y=j+u$, $0<u<1$, $0\le j\le q-1$, set
$$
 b_r(j+u)=\frac{(j)_{r-1}}{(q-u)_r}
      \left[j-r+1+\frac{ru}{q}(q-u-j)\right].                 \tag{1}
$$
In particular $b_1(y)=y/q$. For $j<r-1$, the expression is zero. For $j\ge r-1$, it is nonnegative. At $u=0$ the integer value is immediate. If $r<q$, at $u=1$ the bracket becomes $(j+1)(q-r)/q$, giving the next integer value; for $r=q$ expression (1) vanishes up to $j=q-1$ and subsequently reduces to a positive constant times $u/(q-u)_{q-1}$, tending to one at $y=q$.

### The recurrence before the last unit interval

For $0\le y\le q-1$,
$$
 (q-y)\{b_r(y+1)-b_r(y)\}=r\{b_{r-1}(y)-b_r(y)\}.           \tag{2}
$$
Here is a derivation that explains (1). For fixed $u\in[0,1)$ define
$$
 c_i(j)=(1-iu/q)\,(q-u-i)_j/(q-u)_j,\qquad
 B_r(j)=\sum_{i=0}^{r}(-1)^i {r\choose i}c_i(j).
$$
These $c_i$ satisfy $(q-u-j)[c_i(j+1)-c_i(j)]=-i c_i(j)$, and $i{r\choose i}=r({r\choose i}-{r-1\choose i})$, with zero-extended binomial coefficients. This gives (2) for the $B_r$'s. To see $B_r(j)=b_r(j+u)$ (at the stated arguments), write $Q=q-u$. The identity
$$
 \sum_{i=0}^r(-1)^i{r\choose i}\frac{(Q-i)_j}{(Q)_j}
  =\frac{(j)_r}{(Q)_r}
$$
is inclusion-exclusion for hitting $r$ specified points in a $j$-element sample without replacement when $Q$ is a large integer; it continues as a rational function. The $i$-weighted sum divided by $r$ is the difference of the unweighted sums for $r$ and $r-1$. Hence $B_r=(1-ru/q)(j)_r/(Q)_r+(ru/q)(j)_{r-1}/(Q)_{r-1}$, exactly (1). The integer endpoint $y=q-1$ follows directly from the integer values.

### Convexity

We prove $b_r$ is convex. Only $r\ge2$ needs attention. Within a unit interval with $j\ge r-1$, drop the positive factor $(j)_{r-1}$ in (1). The resulting expression is affine in the integer parameter $j$, so it is enough to prove interval convexity at $j=r-1$ and $j=q-1$. For $j=r-1$ it is $(ru/q)/(q-u)_{r-1}$, a product of nonnegative, nondecreasing, convex functions. This also covers $r=q$.

For $j=q-1$, set $t=q-r\ge1$ and $D=\prod_{v=t+1}^{q}(v-u)^{-1}$. The remaining function is $ND$, $N=t+(r/q)u(1-u)$. Write $S_k=\sum_{v=t+1}^q(v-u)^{-k}$. Differentiation gives
$$
 (ND)''/D=N(S_1^2+S_2)+2(r/q)(1-2u)S_1-2r/q.              \tag{3}
$$
For $t\ge2$, set $z=t+(r+1)/2-u$, the arithmetic mean of the $v-u$. Then $S_1\ge r/z$ and $S_2\ge S_1^2/r$. In the resulting lower bound $(1+1/r)NS_1^2+2(r/q)(1-2u)S_1-2r/q$, the quadratic is increasing for $S_1\ge r/q$: indeed $N\ge t\ge1$. Substituting $r/z$ and multiplying by $qz^2/r>0$ leaves
$$
 G(u)=(r+1)[qt+ru(1-u)]+2r(1-2u)z-2z^2.
$$
Its quadratic coefficient is $-(r-1)(r-2)\le0$. Its endpoint values, after dividing by $(r-1)/2$, are $2rt+r+2t^2+4t+1$ and $2rt-3r+2t^2-4t+1$, both positive at $t\ge2$. This proves (3) there.

For $t=1$, multiply (3) by $q/r$. Write $d=\min(r,5)$, $L_k=\sum_{v=2}^{d+1}(v-u)^{-k}$, and let $c=1+1/r$ for $r<5$, $c=1$ otherwise. A lower bound is
$$
 [c+u(1-u)](L_1^2+L_2)+2(1-2u)L_1-2.                       \tag{3a}
$$
This is equality for $r<5$. For $r\ge5$, first reduce the coefficient to $c+u(1-u)$, then replace $S_2$ by $L_2$ and $S_1$ by $L_1$; the latter decreases the expression since $L_1\ge\sum_{v=2}^6 1/v>1$.

For completeness, (3a) is positive by the following explicit polynomial certificate. Substitute $u=x/(1+x)$, $x\ge0$, and multiply by $a_d\prod_{i=1}^d(ix+i+1)^2$, where $(a_2,a_3,a_4,a_5)=(1,3,2,1)$. In increasing degree the resulting coefficients are:

- $d=2$: 45, 99, 72, 19, 1.
- $d=3$: 3968, 14880, 22200, 16702, 6540, 1200, 68.
- $d=4$: 92300, 497350, 1143965, 1462904, 1131922, 537956, 150953, 22138, 1196.
- $d=5$: 1811232, 12643200, 38944680, 69530280, 79352100, 60087366, 30229390, 9768970, 1853430, 162620, 1592.

All are positive; the case $u=1$ also follows by continuity. They can be reproduced without symbolic algebra by multiplying the denominators, or by the independent exact-evaluation verifier. The larger 15,232-cell rational enclosure in the supplement is an additional check, not required by the proof.

At an integer $j$ with $r\le j\le q-1$ ($r<q$), direct differentiation of (1) at its two ends gives the slope jump
$$
 b_r'(j+)-b_r'(j-)= b_r(j)\,
 \frac{r(q-j)(r-1)(q-j-1)}{q(q-r)j(j-r+1)}\ \ge0.
$$
For example, dividing the jump by $r b_r(j)$ gives
$-1/[q(q-r)]+(q-j)/[q(j-r+1)]-(q-j-1)/[j(q-r)]$, yielding the displayed factor. At $j=r-1$ the left slope is zero and the right slope is nonnegative; earlier intervals are zero. This completes global convexity.

### The shortened last jump

When $q-1<y<q$, the largest possible increment is $q-y$, not one. We need
$$
 1+(r-1)b_r(y)\ \le\ r b_{r-1}(y).                           \tag{4}
$$
For $r=1$ this is equality. Otherwise set $j=q-1$, $w=1-u$, $t=q-r$, and $P(w)=(t+w)\prod_{v=t+1}^{q-1}(1+w/v)$. Using (1), multiplying (4) by $P(w)>0$ and collecting terms gives
$$
 P(w)\ \le\ t+rw-\frac{r(r-1)}{q(t+1)}w(1-w)^2.
$$
Indeed $P(w)b_r=t+(r/q)w(1-w)$ and $P(w)b_{r-1}=(t+w)[t+1+((r-1)/q)w(1-w)]/(t+1)$.
The polynomial $P$ has nonnegative coefficients, $P(0)=t,\ P(1)=q$. Its deficit below this endpoint chord is at least $w(1-w)$ times the sum of its coefficients of degrees at least two, since $w-w^k\ge w(1-w)$ for $k\ge2$. The coefficient sum is
$$
 r-P'(0)=\sum_{i=1}^{r-1} i/(t+i).
$$
If $t=0$ this is $r-1=r(r-1)/[q(t+1)]$. If $t\ge1$ it is at least $r(r-1)/[2(q-1)]\ge r(r-1)/[q(t+1)]$. This proves (4).

### Applying the kernel

For $0\le Y=y\le q-1$, convexity bounds $b_r(Y')$ above by its chord on $[y,y+1]$, where $Y'$ is the state after one more draw. Taking conditional expectation and applying (2) yields
$$
 \mathbb E[b_r(Y')\mid\text{history}]
 \le (1-r/q)b_r(y)+(r/q)b_{r-1}(y).                         \tag{5}
$$
For $q-1<y<q$ use the chord on $[y,q]$ with interpolation weight $(\mathbb E Y'-y)/(q-y)=1/q$, and then (4); at $y=q$ both sides are one. The required mean increment follows by summing the inclusion probabilities over missing coupons. No Markov or independence assumption is needed beyond the stated conditional marginals.

Start at $Y_0=0$. For $r\ge1$, $b_r(0)=0$. The probability $v_r(m)$ that $r$ specified labels have all appeared in $m$ ordinary iid uniform draws from $q$ labels has these same initial values and obeys (5) with equality: condition on whether the last draw is one of the specified labels. Induction gives $\mathbb E b_r(Y_m)\le v_r(m)$ for every $r$. Since $b_q\ge0$ and $b_q(q)=1$, the success indicator is bounded by $b_q(Y_m)$. Taking $r=q$ proves the theorem. The ordinary surjection count gives the stated value. For $q=1$ full coverage is forced on the first draw.

### Strictness for iid laws

Suppose $q\ge3$. For the first two packages $A,B$, put $\xi=1-|A\cap B|/s$, so $Y_2=1+\xi$. On that unit interval, $b_2(1+\xi)=2\xi/[q(q-\xi)]$. The chord gap in (5) at step two is therefore
$$
 \Delta=\frac{2}{q(q-1)}\,\mathbb E\!\left[\frac{\xi(1-\xi)}{q-\xi}\right].
$$
If $A,B$ can partially overlap, then $\Delta>0$. Propagating this deficit through (5) implies
$$
 v_q(m)-\Pr(T\le m)\ \ge\ \Delta\Pr(\text{exactly two labels missing after }m-2
             \text{ ordinary uniform draws}).
$$
Indeed the coefficient on the step-two deficit at $r=2$ in the iterated recursion is the transition probability of the chain $r\mapsto r-1$ with probability $r/q$ (otherwise $r\mapsto r$), started at $q$ and run for $m-2$ steps. It is positive for every $m\ge q$ since $q-2\ge1$. If $q=2$, any two supported partially overlapping packages $A,B$ give a strict final chord loss instead: with positive probability the first $m-1$ draws all equal $A$ and the final draw is $B$; the last state is strictly inside $[1,2]$, where $b_2$ is strictly convex. Thus at every feasible $m\ge2$, partial overlaps are again impossible at equality. If no two supported packages partially overlap, the support is a disjoint partition and balance forces all its block probabilities to be $1/q$. Conversely those probabilities attain equality.

**Scope and verification.** This balanced result has no restriction on the deadline and strengthens the class of processes to allow conditional balance. It does *not* say that an arbitrary optimizer over unequal marginals must be balanced. For those iid laws see the distinct large-deadline theorem in this bundle. The shorter three-block proof gives a separate, elementary strictness term. Primary problem statement: C. D. Long, [*Optimal coupon packages and stochastic improvement of uniform group drawings*](https://hexagonmath.org/2611.00814v1), Conjecture 8.1; targeted searches found no prior all-deadline balanced theorem, but no claim of priority or independent peer review is made.
