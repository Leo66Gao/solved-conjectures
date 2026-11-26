# Pointwise failure of a monotonicity conjecture for Penney races

**Statement tested.** In the notation of Drexel, Peng and Richey (2025), let
\[
 A_N(p)=\#\{(v,w):1\le |w|<|v|\le N,\quad \Pr_p(\tau_v<\tau_w)>1/2\}.
\]
Words are binary, the input is iid Bernoulli with one-probability \(p\), and first occurrences are contiguous. Conjecture 1 of [the published paper](https://doi.org/10.37236/13609) asserts that for all sufficiently large \(N\), \(A_N\) is non-increasing on \((0,1/2)\). This is the aggregate conjecture, not a statement that every individual winning probability is monotone.

**Theorem.** For every \(N\ge4\), the conjectured pointwise monotonicity fails. In fact, for each \(4\le m<N\), put \(t_m=1-2^{-1/(m-2)}\). Then, for all sufficiently small \(h>0\) (depending on \(N,m\)),
\[
 A_N(t_m+h)\ge A_N(t_m)+1.
\]
Thus the list gives at least \(N-4\) distinct failures for every \(N\ge5\); their biases accumulate at zero as the length cap increases.

**Proof.** Let \(q=1-p\), \(v=01 0^{m-1}\), \(w=0^m\). For a nonempty string \(s\) let \(P(s)=p^{\#1(s)}q^{\#0(s)}\). Define \(C(x,y)\) as the sum of \(1/P(s)\) over nonempty suffixes \(s\) of \(x\) that are prefixes of \(y\). For distinct words with neither contained in the other, the classical two-word race formula (Drexel–Peng–Richey, Theorem 4) gives
\[
 F_{v,w}(p)=A/(A+B),\quad A=C(w,w)-C(w,v),\quad B=C(v,v)-C(v,w).
\]
Here \(C(w,w)=\sum_{j=1}^m q^{-j}\), \(C(w,v)=q^{-1}\), \(C(v,v)=1/(p q^m)+q^{-1}\), and \(C(v,w)=\sum_{j=1}^{m-1}q^{-j}\). The only proper border of \(v\) is '0': a longer zero-run starts with '00' rather than '01'; its unique '1' cannot align at two distinct positions. Therefore
\[
 pq^m A=1-q^{m-1},\qquad pq^m B=p+q^{m-1},\qquad
 F_{v,w}(p)=\frac{1-q^{m-1}}{1+p}.
\]
Hence \(2F_{v,w}(p)-1=q(1-2q^{m-2})/(1+p)\). Its sign goes from negative to positive precisely at \(p=t_m\), which is strictly between zero and one-half when \(m\ge4\).

All winning probabilities of admissible pairs are continuous on \((0,1)\) by the same formula; if the shorter word is contained in the longer, the latter's strictly-earlier probability is identically zero. For completeness, continuity also follows without using the formula: on any compact subinterval of biases in \((0,1)\), a given word appears in an independent block of its length with probability bounded below uniformly. Polynomial finite-horizon winning probabilities therefore converge uniformly to the eventual winning probability. Each of the finitely many pairs favorable at \(t_m\) stays favorable for all sufficiently small positive increments. The displayed pair is *not* counted at \(t_m\) but *is* counted immediately to the right. This proves the inequality regardless of how many other pairs fall through the threshold there.

For \(N=4\), take \(v=1100,\ w=000\). The formula gives
\[
 F_{v,w}(p)=\frac{p^2(p^2-3p+3)}{p^2-p+1}.
\]
Indeed \(A=q^{-1}+q^{-2}+q^{-3}\), \(B=p^{-2}q^{-2}-q^{-1}-q^{-2}\). The sign of \(2F-1\) is the sign of \(2p^4-6p^3+5p^2+p-1=3p-p^2-1-2pq^3\). Its derivative is \(3-2p-2q^3+6pq^2\ge 1\), since \(q^3\le q\). It is negative at zero and positive at one-half. Its unique crossing \(t\approx0.450866100675496\) gives the same strict-count argument for every \(N\ge4\). ∎

**Distinction between an exact threshold and its lateral limits.** One upward-crossing pair need not make the *right-hand limit higher than the left-hand limit* of the aggregate. A pair falling at the same point can cancel or outweigh it between the open intervals. Our all-cap proof does not rule out a monotone representative after discarding all tie points. The separate numerical certificate in this folder also finds finite caps exhibiting genuine increases between distinct rational bias values. Those finite-cap tests do not alone settle eventual off-threshold monotonicity.

**Context and priority.** The [journal paper](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p57/pdf) gives the proposal in Conjecture 1 and shows a finite-cap empirical graph; its individual nonmonotonic example has equal word lengths. A [public MathDB entry](https://mathdb.com/p/364994/monotonicity-conjecture-for-favorable-longer-word-pairs) calls the conjecture solved on the basis of that same example. That pair has equal lengths, its displayed win probability is strictly below one-half on the open interval, and an individual nonmonotonic probability need not change the aggregate at all. Thus the stated justification does not establish this result. Searches by title, authors, countexample pair, threshold and equivalent count formulations located no matching proof of the result above; this does not establish priority. The paper's other, unrelated Conjecture 14 is the subject of a [previous public solution](https://github.com/discord9/penney-property-r-density) and is not claimed here.

**Reproducibility.** Run `python verify.py -N 9`. It first checks both win formulas using an independent exact absorbing-chain solver at five rational biases, for ten lengths of the family. It then counts favorable pairs by exact integer comparisons at four pairs of nearby rational biases. No floating point is used. The proofs do not require enumeration. See also `asymptotics.md` for the analytic replacement.

**Elementary derivation of the correlation identity (optional).** For one fixed target \(y\), start a new gambler with a unit stake before every toss. Each gambler stakes their entire current fortune successively on the letters of \(y\), receiving on a correct guess their stake divided by that letter's probability and otherwise losing it. The gambler retires when the word is complete. At the first time \(T\) that either target occurs, the total remaining fortune equals \(C(v,y)\) if the terminal word is \(v\) and \(C(w,y)\) otherwise: each surviving stake corresponds to a suffix that is a target prefix. A longer survivor at the shorter terminal word cannot extend behind that word: a longer prefix of the other target ending in the shorter terminal word would make it contained in the other target. There are no earlier completions. Fairness gives expected total fortune \(\mathbb ET\), by first stopping at \(T\wedge n\); before stopping, the total fortune is uniformly bounded in \(n\) (at most one active unit for each target-prefix length, each with bounded winnings), and \(\mathbb ET<\infty\) by disjoint fixed-length blocks. Apply this equation for both choices of gambler target \(y\) and subtract to obtain \(F[A+B]=A\).

For a wider finite-cap check, ordinary rational biases \(p=0.4709\) and \(p'=0.4710\) give \(A_5(p)=27\) and \(A_5(p')=28\). At caps 6, 7 and 8 the respective pairs of counts are (84,86), (208,210), (473,475). This particular interval no longer increases at cap 9 (1086 to 1084), as can happen even before eventual asymptotic ordering. The narrower interval in the recorded diagnostics still increases at cap 9.
