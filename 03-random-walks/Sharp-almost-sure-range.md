# The sharp almost-sure lower order of the range under vertex expansion

Let `R_t = |{X_0,...,X_t}|` and let `T_j = inf{t>=0:R_t=j}`. Time is a nonnegative integer and all unspecified logarithms are natural.

**Theorem.** For a discrete-time homogeneous Markov chain on a countable space, suppose `q = inf_x P_x(T_x^+ = infinity)>0`, where `T_x^+` denotes the first strictly positive return time to x. Then from every start, almost surely
$$
\liminf_{t\to\infty}\frac{R_t\log\log t}{t}\ge -\log(1-q).
$$
In particular this holds for simple random walk on every infinite, connected, locally finite simple graph with positive outer vertex expansion. The order is sharp: an explicit simple graph of vertex expansion 1 satisfies almost surely
$$
0<\liminf_{t\to\infty}\frac{R_t\log\log t}{t}\le 6.
$$
In particular its expected range is linear, but `liminf R_t/t = 0` almost surely. It lacks even a high-probability linear lower bound: for every c>0, `liminf_t P(R_t<ct)>0` from the root.

## 1. Uniform escape gives a geometric exponential-moment bound

Assume first 0<q<1. From the strong Markov property at successive visits, the number of lifetime visits from a start x is geometric on {1,2,...}, with success parameter `P_x(T_x^+=infinity) >= q`. Thus each fixed state is visited only finitely often almost surely, also from any start by stopping at its first visit. Taking the countable intersection, all discovery times are finite, since an infinite path confined to finitely many states would revisit at least one infinitely often.

Put `Y_j=X_{T_j}` and let `L_j` be its number of lifetime visits, including discovery. Conditional on the history at `T_j`, the strong Markov property bounds the moment of `L_j` by that of `Geom(q)`. In particular if `0<theta<alpha=-log(1-q)`, then
$$
\mathbb E e^{\theta L_j}\le C_\theta:=\frac{q e^\theta}{1-(1-q)e^\theta}.
$$
The first `T_{m+1}` time slots, time 0 through `T_{m+1}-1`, visit only `Y_1,...,Y_m`. Consequently `T_{m+1} <= L_1+...+L_m`. Convexity of the exponential and the marginal bounds give, without independence,
$$
\mathbb E e^{\theta T_{m+1}/m}
\le \frac{1}{m}\sum_{j=1}^m\mathbb E e^{\theta L_j}\le C_\theta.
$$
As a finite-time consequence, `P(R_t<=m) <= C_theta exp(-theta t/m)` for every positive m.

Fix b>1 and K>1/theta. Set `m_n=floor(b^n)`, `s_n=K m_n log n` for n>=2. Markov's inequality and Borel–Cantelli give `T_{m_n+1}<=s_n` eventually almost surely, because the failure probability is at most `C_theta n^(-theta K)`. For large t take n with `s_n<=t<s_(n+1)`. Then
$$
\frac{R_t\log\log t}{t}\ge
\frac{m_n\log\log s_n}{K m_{n+1}\log(n+1)}
\longrightarrow\frac{1}{K b},
$$
since `log(log s_n)=log n+O(1)`. Along countably many choices let K decrease to `1/theta`, b decrease to 1, and theta increase to alpha. This proves the bound. If q=1 then there are almost surely no repeated visits, so the liminf is infinite.

## 2. Binary tree with complete levels

Take the infinite rooted binary tree and add every edge between distinct vertices at the same depth. Level i contains `m_i=2^i` vertices. For any nonempty finite set S there are `2|S|` distinct tree children of its vertices, of which at most `|S|` lie in S. Hence `|partial_V S|>=|S|`; initial balls show that the infimum of the ratio is 1.

Let `tau_i` be first entrance into level i from the root. This is almost surely finite: the walk cannot remain forever in the finite set of levels below i. Indeed, from every point of this finite set there is a positive probability of reaching level i in at most i steps by choosing children, and the minimum of these finitely many positive probabilities is positive. Define `W_i = inf{k>=1:level(X_(tau_i+k)) != i}`. For i>=1 the degree is `m_i+2`, with exactly three interlevel neighbors. Thus
$$
\mathbb P(W_i>k\mid\mathcal F_{\tau_i})=
\left(\frac{m_i-1}{m_i+2}\right)^k,\qquad k\in\mathbb Z_{\ge0}.
$$
Since `tau_i+W_i<=tau_(i+1)`, the earlier W's are measurable with respect to the history at `tau_i`. The displayed conditional distribution is deterministic, so the `W_i` are independent.

Fix `0<a<1/3` and put `k_i=floor(a m_i log i)` for i>=2. Expanding the logarithm gives `P(W_i>k_i)=i^(-3a)(1+o(1))` (the logarithmic error is `O(log i/m_i)`). These independent events occur infinitely often by Borel–Cantelli. At the corresponding time `t_i=tau_i+k_i`, no level above i has been visited, so `R_(t_i)<=2m_i-1`. Because `t_i>=k_i` and `(log log t)/t` is decreasing for all sufficiently large t,
$$
\frac{R_{t_i}\log\log t_i}{t_i}\le
\frac{(2m_i-1)\log\log k_i}{k_i}\longrightarrow 2/a.
$$
Here `log(log k_i)=log i+O(1)`. Let a increase to 1/3 along a countable sequence to obtain upper bound 6. The positive lower bound follows from Section 3 and Section 1.

In fact the graph has no linear lower bound holding with probability tending to 1. The level chain moves up or down, conditional on changing levels, with probabilities 2/3 and 1/3 respectively at levels j>=1. Let `h_j` be the mean time to first reach level j+1 from level j. Each h_j is finite by the finite-domain block-escape argument above. First-step analysis at the first *level change* gives `h_0=1` and
$$
h_j=(m_j+2)/3+(h_{j-1}+h_j)/3,
\qquad\text{so}\qquad h_j=(m_j+2+h_{j-1})/2.
$$
Thus `h_j<=2m_j`, by induction, and `E_o tau_i=sum_{j<i}h_j<2m_i`. Fix A>2 and choose `i=floor(log_2(t/A))` for all large integers t. Then `A<=t/m_i<2A` and `P(tau_i<=t)>=1-2/A`. Given `F_(tau_i)`, `P(W_i>t)>=exp(-6A)+o(1)`, uniformly over this sequence t. On both events, `R_t<=2m_i-1<2t/A`. Taking A>2/c proves `liminf_t P_o(R_t<ct)>0`.

## 3. Vertex expansion implies uniform escape

Here is a quantitative refinement of the Dirichlet/capacity argument of Benjamini–Salez. Put `h=inf_{0<|S|<infinity}|partial_V S|/|S|` and write `E(f)=sum_{unordered edges uv}(f(u)-f(v))^2`, with f finitely supported. We can replace f by |f| to prove an energy lower bound. For nonnegative f, let `d(x)=max(0,max_{y~x}f(y)-f(x))`. Integrate the outer boundary inequality for `{x:f(x)^2>s}` over s>=0 to obtain
$$
h\|f\|_2^2\le 2\sum_x f(x)d(x)+\sum_x d(x)^2.
$$
For each x with d(x)>0 choose one maximizing neighbor y. The chosen undirected edges are distinct: any repeated edge would be chosen from both endpoints, which is impossible since each choice goes to a strictly larger value. Hence `sum_x d(x)^2<=E(f)`. Cauchy–Schwarz and solving the resulting quadratic give `E(f)>=a ||f||_2^2` with `a=(sqrt(1+h)-1)^2`.

For f(x)=1, each incident edge still occurs in the energy. The triangle inequality on the neighbor coordinates gives
$$
\sqrt{\deg(x)}
\le \left(\sum_{y\sim x}(1-f(y))^2\right)^{1/2}
 + \left(\sum_{y\sim x} f(y)^2\right)^{1/2}
\le (1+a^{-1/2})\sqrt{E(f)}.
$$
Taking the infimum over finitely supported f with f(x)=1 and using the standard identity `Cap(x)=deg(x) P_x(T_x^+=infinity)` yields `q >= (1-1/sqrt(1+h))^2>0`. The capacity identity follows, for instance, by minimizing on a finite domain with exterior value zero: the harmonic potential is the probability to hit x before exiting, and its energy equals the current out of x. Increasing domains exhaust the graph, and the finite-domain escape events decrease to no return, up to the null event of staying forever in a finite domain. The same elementary last-visit sum as in Benjamini–Salez yields `E R_t >= q(t+1)`.

## 4. The constant is sharp among countable Markov chains

For 0<q<1, use blocks indexed by i>=0; block i is a clockwise directed cycle of size `m_i=i!`. Starting at its first state, traverse it deterministically except at its last state: there, go to the first state of block i+1 with probability q, otherwise start another lap. Every state has escape probability exactly q. The numbers of laps before the first exit of each block are independent `Geom(q)` variables. For any `0<a<1/alpha`, `alpha=-log(1-q)`, the probability of staying for more than `floor(a log i)` laps is `(1-q)^floor(a log i)`, a nonsummable sequence. On infinitely many such blocks, look at time `tau_i+m_i floor(a log i)` after first entrance `tau_i`. Its range is at most `sum_(j<=i) m_j=(1+o(1))m_i`. Since `log(log(m_i floor(a log i)))=(1+o(1))log i`, the same monotonicity of `(log log t)/t` gives liminf at most 1/a. Letting a increase to `1/alpha` and applying Section 1 proves equality.

If irreducibility is required, at the gate of block i use probabilities `a_i=q/(1-r_i)` to advance and `b_i=a_i epsilon 2^(-i)` to move to the first state of block i-1, with `b_0=0`, `r_i=epsilon 2^(-i-1)`, and epsilon sufficiently small that `a_i+b_i<1` for every i. The remaining probability starts a new lap. The resulting chain is irreducible. For the embedded block-index chain above i, each down/up probability ratio is at most r_i. So `r_i^(block_index-i)`, stopped at i, is a nonnegative supermartingale: at each surviving block step its multiplier has conditional mean at most 1. Starting from i+1, the probability of reaching i by any fixed step bound is consequently at most r_i; the same holds without the bound. Every state's probability of escaping is at least `a_i(1-r_i)=q` (advance at the first gate and never return to the block), and at most `a_i+b_i` (if the first gate stays in the block it must encounter the original state again). The latter tends to q, so the infimum is q. First-entrance lap counts are independent `Geom(a_i+b_i)` by the same stopping-time argument as for the tree of cliques, with `a_i+b_i=q+O(2^(-i))`. Thus the nonsummability and the liminf upper bound remain unchanged. These chain examples are not simple undirected graph walks and do not show the precise coefficient is attained in that subclass.

## Scope and literature check

- [Benjamini and Salez, manuscript version 3](https://arxiv.org/html/2602.11051v3), Theorem 1.1 and Lemmas 2.1–2.2: proves linear *expected* range and uniform escape. The [latest record](https://arxiv.org/abs/2602.11051) is withdrawn because the main expected-range result was already known. Neither that expected result nor its overall proof method is claimed new.
- [Okamura, Theorem 1.2](https://arxiv.org/html/2606.00648v1): proves positive almost-sure linear lower range under a stronger uniform late-return condition. The example above fails even uniform late-return decay. For fixed n>=1, start at x in a clique of size m. First stay inside the clique for n steps without returning to x, then hit x before exiting. The probability of this event is `((m-1)/(m+2))*((m-2)/(m+2))^(n-1)/4`, since after step n each step before hitting x or exiting has one return edge and three exit edges. As m tends to infinity the bound tends to 1/4.
- [Windisch](https://arxiv.org/abs/1001.0355) studies bounded-degree uniformly transient graphs and entropy of the range; [Okamura's spectral dimension two paper](https://arxiv.org/abs/1903.07990) addresses a recurrent regime. Initial searches using combinations of “range,” “uniform transience,” “vertex nonamenability,” “lower envelope,” and “log log” found no matching sharp lower-order statement or same counterexample. This is not an exhaustive novelty certification. Independent expert/primary-source review is still needed before any publication claim.
