# The limiting shape behind the failed finite monotonicity

## Setup

Let \(H_N(p)=A_N(p)/T_N\), where \(T_N\) is the number of ordered pairs of nonempty binary words of lengths at most \(N\) with the first longer than the second. This denominator counts containment pairs as well; omitting them changes all limits below by an exponentially small term. Uniform words used to *count pairs* have fair letters, distinct from the race stream whose one-probability is \(p\). Let \(\Phi\) be the standard normal cdf. Logs are natural.

**Theorem 1 (critical window).** If \(p_N\in(0,1/2]\) and \(\sqrt N(1/2-p_N)\to\lambda\in[0,\infty)\), then
\[
 H_N(p_N)\longrightarrow L(\lambda):=
 \sum_{d=1}^\infty 2^{-d}\Phi\!\left(-\frac{d\log 2}{2\sqrt2\,\lambda}\right),
 \qquad L(0)=0.
\]
The limit strictly increases from zero towards one-half with \(\lambda\). For every fixed \(0<p<1/2\), \(H_N(p)\to1/2\). The same limit one-half holds for \(p_N\to1/2\) with \(\sqrt N(1/2-p_N)\to\infty\).

**Theorem 2 (fixed bias, first correction).** Put \(q=1-p\) and \(c=-\log q/\log(q/p)>0\). For irrational \(c\),
\[
 \lim_{N\to\infty}\sqrt{\pi N}\,[1/2-H_N(p)]
   = S(c):=\tfrac12+\sum_{d=1}^{\infty}2^{-d}\lceil dc\rceil .
\]
As a function of \(c\), the one-sided staircase jumps at every reduced rational \(a/b>0\), by precisely \(1/(2^b-1)\). It is continuous at irrationals and strictly increasing overall: a positive interval contains a rational. These sums in particular describe the main aggregate trend without asserting false pointwise monotonicity at each finite cap.

At a reduced rational \(c=a/b>0\), the exact value of the limit is
\[
 S(c)+\frac{1+z(p)}{2(2^b-1)},
\]
where \(S(c)\) in this expression uses the ordinary ceiling at integer arguments (the left limit). The boundary-overlap probability \(z(p)\) is defined below and satisfies \(1/16\le z(p)\le1\). The finite-scale theorem is already complete without this rational refinement.

**Corollary (pointwise eventual monotonicity).** For every two *fixed* biases \(0<p_1<p_2<1/2\), there is \(N_0(p_1,p_2)\) such that \(A_N(p_1)>A_N(p_2)\) for every \(N\ge N_0(p_1,p_2)\). This exchanges the order of the uniformity quantifiers in the failed conjecture. Indeed, \(c(p)\) is strictly increasing: its positive numerator increases and positive denominator decreases. The coefficient at any rational lies between its own left and right limits. Between any two distinct arguments lies another rational with a strictly positive jump; local uniform convergence of the ceiling series then shows that the second bias has a strictly larger scaled deficit. Since the normalizing number of pairs is independent of bias, the eventual strict inequality follows. This neither supplies a uniform cap nor says when the eventual inequality begins.

The corollary does not in fact require evaluation of \(z(p)\) or even convergence at resonant parameters. At each raw-mass tie, bounding the fraction of favorable races just by zero and one places the lower and upper subsequential scaled deficits between the staircase's lateral limits. Those intervals are strictly ordered at any two distinct slopes.

## Proof

**Lengths.** Write \(|v|=M=N-i,\quad |w|=m=N-i-d\), where \(i\ge0,d\ge1,i+d\le N-1\). The probability of these lengths for a uniformly counted pair is proportional to \(2^{-2i-d}\); its normalizer converges exponentially to \(4/3\). In particular the limiting mass of \(d\) is \(2^{-d}\). Given lengths, letters in both words are iid fair. All expectations over words below use this law.

**Overlap approximation.** For \(x,y\in\{v,w\}\) use the correlations \(C(x,y)\) of the companion proof; an overlap means a nonempty suffix of the source equal to a same-length prefix of the target. Leave out full self-overlaps. For each feasible proper self-overlap of length \(k\), its probability is \(2^{-k}\), because it imposes period \(|x|-k\) and exactly the first \(|x|-k\) bits can be freely chosen. This applies also to overlaps longer than half a word. For distinct source and target the same probability follows from independence. Hence the probability of at least one overlap with \(k>K\) is at most \(4\,2^{-K}\). The probability that \(w\) is contained anywhere in \(v\) is at most \((d+1)2^{-m}\).

Fix a compact subinterval of \(p\in(0,1)\) and let \(\rho<1\) bound \(\max(p,1-p)\) there. On the event of no containment and no overlap longer than \(K=\lfloor m/2\rfloor\), for either source word \(x\) and other word \(y\),
\[
 C(x,x)-C(x,y)=P(x)^{-1}(1+E_x),\qquad |E_x|\le2N\rho^{m-K}.
\]
Indeed an overlap term \(1/P(s)\) times \(P(x)\) equals the word probability of the nonoverlapping part of \(x\). Thus if \(m\ge N/2\), outside an event of exponentially small probability and for large \(N\), the log of the true odds differs by exponentially little from
\[
 B_N=\log(P(v)/P(w))=d\log q+\Delta\log(p/q),\qquad \Delta=\#1(v)-\#1(w).
\]
Both corrections are uniform in these lengths and in the specified compact set. The cap has exponentially small probability of \(m<N/2\) by the length weights.

**Normal window.** The law of \(\Delta\) is exactly that of \(X-m\), with \(X\sim\mathrm{Bin}(M+m,1/2)\) (complement the bits of \(w\)). Its mean is \(d/2\). For fixed \(i,d\), \(\Delta/\sqrt N\) tends to a normal of variance \(1/2\). If \(\lambda>0\), then \(\log(p_N/q_N)\sqrt N\to-4\lambda\) and \(d\log q_N\to-d\log2\). The limit of the log odds is normal with mean \(-d\log2\) and variance \(8\lambda^2\), so the conditional favor probability tends to the summand's cdf factor. If \(\lambda=0\) the log odds tend in probability to the negative number \(-d\log2\). In the other regimes stated in Theorem 1 divide the log odds by \(\sqrt N|\log(p_N/q_N)|\), which tends to infinity; its sign tends in distribution to that of a centered continuous normal, giving probability one-half. Summing the limiting conditional probabilities with the geometric length weights by dominated convergence proves Theorem 1.

**Lattice correction.** At fixed \(0<p<1/2\), raw masses favor \(v\) exactly when \(\Delta<-cd\). For fixed \(i,d\) with \(cd\notin\mathbb Z\), the distance to the nearest lattice point is positive; hence the strict sign of the raw odds agrees with the race odds except with exponentially small probability. For fixed integer \(k\), binomial symmetry and Stirling yield
\[
 \Pr(\Delta\le k)=\tfrac12+
 \frac{k+1/2-d/2}{\sqrt{\pi N}}+o(N^{-1/2}).
\]
Indeed each fixed lattice mass near the center equals \((1+o(1))/\sqrt{\pi N}\); start at the symmetry center, counting half the center atom if it exists. For noninteger \(cd\), use \(k=-\lceil cd\rceil\). The resulting correction to \(1/2-H_N\), multiplied by \(\sqrt{\pi N}\), is \(\lceil dc\rceil+d/2-1/2\). Averaging over lengths gives \(S(c)\), since \(\sum_{d\ge1}d2^{-d}=2\).

Here is a domination argument which avoids any uniform Diophantine assumption on \(c\). If \(m\ge N/2\), both exact and approximate thresholds are between integer cutoffs \(-cd\pm C_p\) except on an exponentially unlikely event (one may take \(C_p=1\) for all sufficiently large \(N\)). The largest atom of the binomial law is \(O(N^{-1/2})\); comparing the cutoffs with the symmetry center \(d/2\) gives the absolute scaled deviation from one-half \(O_p(d+1)\), uniformly over these lengths. If \(m<N/2\), the trivial bound \(\sqrt N\le\sqrt{2(i+d)}\) suffices. Both bounds are summable against \(2^{-2i-d}\), so dominated convergence applies to the scaled conditional deviations, also at rational \(c\). Local uniform convergence of the ceiling series establishes the claimed lateral limits and jump sizes: the jump at \(a/b\) comes from indices \(b\mid d\), each contributing \(2^{-d}\).

**Raw-mass ties.** To complete the rational-case assertion, use independent infinite fair starting rays \(P_1,P_2\), and independent infinite fair ending rays \(E_1,E_2\) read backwards from the end. All four rays are independent. Each source \(j\) and target \(k\) has a match at \(\ell\) when \(\mathrm{rev}(E_j[1:\ell])=P_k[1:\ell]\). Let \(C^*_{jk}\) be the sum of inverse Bernoulli-word probabilities over all such matches. It is finite almost surely: the chance of any match past length \(K\) is at most \(4\,2^{-K}\). Set
\[
 Z=C^*_{22}-C^*_{21}-C^*_{11}+C^*_{12},\qquad z(p)=\Pr(Z=0).
\]
Simultaneously exchanging subscripts 1 and 2 negates \(Z\), so \(\Pr(Z>0)=(1-z(p))/2\). A simple lower bound on \(z\): with probability \(1/8\) the two starts agree in their first three bits, so all matches of lengths at most three cancel row by row; conditionally on the starting rays the probability of any later match is at most \(4\,2^{-3}=1/2\) by the independent uniform ends. Thus \(z\ge1/16\).

For fixed \(i,d\), suppose \(cd\) is integral and condition on \(\Delta=-cd\) (probability asymptotic to \(1/\sqrt{\pi N}\)). Then every fixed set of boundary bits converges in total variation to independent fair bits. Indeed, after complementing the shorter word the condition fixes the total count of ones within a bounded distance of its mean, so every fixed pattern of \(j\) entries has probability tending to \(2^{-j}\), by ratios of binomial coefficients. The conditional probability that any relevant overlap has length greater than \(K\) is \(O(2^{-K})+o(1)\): for \(K<\ell\le m/4\), expose the at most \(2\ell\) bits determining each specific overlap. The remaining fair bits attain any prescribed count with probability \(O(1/\sqrt N)\), uniformly in their exposed values. Dividing by the probability of the conditioning event hence bounds its conditional overlap probability by \(O(2^{-\ell})\). For \(\ell>m/4\), the crude unconditional tail bound divided by the atom probability is \(O(\sqrt N\,2^{-m/4})\); the same argument makes containment negligible. On this atom the full self terms cancel *exactly*. Thus the sign of the conditional comparison is the sign of the signed proper-overlap sum, whose positive and zero probabilities converge to those of \(Z\), by first fixing the cutoff then sending it to infinity. This argument gives convergence even at the zero atom, which weak convergence of real variables alone would not ensure.

Consequently a fraction \(\kappa=(1-z(p))/2\) of the raw-mass ties count as strictly favorable in the limit. For each resonant \(d\), use the strict integer cutoff \(-cd-1\) and add \(\kappa/\sqrt{\pi N}+o(N^{-1/2})\). Its scaled deficit exceeds the left-limit coefficient by \(1-\kappa=(1+z(p))/2\). Summing over multiples of \(b\) proves the rational formula. ∎

**Scope.** This is an asymptotic analysis of the precise aggregate counting experiment, not optimization over competing words. Dudley Stark's [long-word Pevzner theorem](https://doi.org/10.1017/S0963548300001656) is about the existence of a favorable response to any sufficiently long word *of the same length*. Drexel, Peng and Richey's [2025 study](https://doi.org/10.37236/13609) gives the biased race setting, the exact correlation formula and the finite-cap conjecture. Searches did not locate this particular critical-window or lattice law; no claim of established publication priority or external review is made.

**Numerical diagnostics.** The standard-library script `asymptotic_checks.py` computes the finite-binomial, length-mixture *raw mass* surrogate, not a finite-cap exact race probability. At \(p=1/3\) (irrational \(c=\log(3/2)/\log 2\)), the predicted scaled deficit is 2.17741148; the surrogate at cap 6400 gives 2.17596792. For the critical window \(\lambda=1\), the predicted limit is 0.32373342, and the same cap gives 0.32333490. The exact tests in `verify.py` instead count the actual finite races.

For the first rational resonance \(c=1\), \(q=1/\varphi\), \(p=q^2\). Every overlap weight is \(\varphi^{k+s}\) for length \(k\) with \(s\) ones; these are represented exactly in \(\mathbb Z[\varphi]\) by Fibonacci integer pairs. The program `resonance.cpp` exactly enumerates the four-boundary truncation: for fixed starts \(A,B\), collect the signed scores \(D(E)=C(E,B)-C(E,A)\) of all endings and count ordered pairs of scores summing to zero. The conditional test is precisely \(Z=0\), and the truncation error in its probability is at most \(4\,2^{-K}\). Build with `c++ -O3 -std=c++17 resonance.cpp -o resonance`; run `./resonance 10`. See `resonance-results.txt`. These checks supply independent numerical handles on the correction, not substitutes for its proof.

**The sparse-stream edge.** In fact, for *any* sequence \(p_N>0\) tending to zero, however quickly,
\[
 \sqrt{\pi N}(1/2-H_N(p_N))\longrightarrow \tfrac32.
\]
To see why the compact-bias assumption is not needed at this edge, refine the good event in the overlap approximation: require at least \(m/8\) ones in the first \(\lfloor m/2\rfloor\) bits of each fair random target. For \(m\ge N/2\) this fails with exponentially small probability by the binomial lower-tail bound. Removing any suffix of length at most \(\lfloor m/2\rfloor\) leaves these bits intact, so the row errors are now at most \(2N p_N^{m/8}\), uniformly \(o(p_N)\) for \(p_N\le1/2\) and \(m\ge N/2\). For each fixed gap \(d\), at \(\Delta=0\) the raw log odds are \(d\log(1-p_N)\le-p_N\), and at \(\Delta=-1\) they tend to positive infinity. Consequently the good-event sign test is exactly \(\Delta\le-1\) for large \(N\). The lattice expansion gives conditional scaled deficit \((d+1)/2\), which averages to \(3/2\). The same summable domination applies: eventually \(p_N\le1/4\), the raw lattice cutoff in absolute value is \(dc(p_N)=O(d)\), and the log-odds spacing is at least \(\log3\). No unproved uniform approximation over bias or length gaps is used.
