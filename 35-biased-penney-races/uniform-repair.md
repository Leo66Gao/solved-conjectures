# Exponential uniform repair and a short proof of the fixed-bias theorem

**Theorem.** There exist constants \(C,c>0\) such that for each cap \(N\) one can remove at most a \(Ce^{-cN}\) fraction of all ordered binary pairs \((v,w)\) with \(1\le|w|<|v|\le N\), leaving a collection in which *every individual favorable indicator* \(\boldsymbol1\{\Pr_p(\tau_v<\tau_w)>1/2\}\) is non-increasing on the entire interval \(0<p\le1/2\). The removed collection does not depend on \(p\). Thus \(H_N\) differs uniformly from a non-increasing function by at most \(Ce^{-cN}\), and
\[
 \sup_{0<p_1<p_2\le1/2}(H_N(p_2)-H_N(p_1))\le Ce^{-cN}.
\]
This concerns the fraction among all length-eligible word pairs; their *unnormalized* number may still increase, and is known to do so at every length cap at least four.

**Proof.** Write \(M=|v|,m=|w|,d=M-m\), and draw the pair uniformly as in `asymptotics.md`. Discard pairs with \(m<N/2\), any containment, any proper self or cross overlap longer than \(K=\lfloor m/2\rfloor\), or fewer than \(m/8\) ones among the first \(K\) letters of either word. The probability of a small \(m\) is exponentially small by the weights \(2^{-2i-d}\), where \(i=N-M\); indeed the unnormalized tail \(\sum_{i+d>N/2}2^{-2i-d}\) is \(O(N 2^{-N/2})\). The containment bound \((d+1)2^{-m}\), proper-overlap union bound \(4\,2^{-K}\), and the binomial lower-tail estimate for each word's first \(K\) independent fair bits show that the remaining exclusions also total at most \(Ce^{-cN}\). Constants may absorb bounded small caps.

For any retained pair, let \(P(x)=p^{\#1(x)}q^{\#0(x)}\), \(q=1-p\), and use the correlation sums from the companion proof. The normalized row difference at source \(x\), with other target \(y\), is
\[
 P(x)\{C(x,x)-C(x,y)\}=1+E_x(p).
\]
Here \(E_x\) is a signed sum of at most \(2N\) monomials \(p^s q^t\), the probabilities of the portions of \(x\) left after removing the corresponding suffix. Every such portion contains the first \(K\) letters, hence \(s\ge m/8\). Uniformly for \(0<p\le1/2\), a monomial is bounded by \(2^{-m/8}\), and its derivative in absolute value by \(4N\,2^{-m/8}\): differentiate each power, using \(p^{s-1}\le2^{1-s}\); if \(t\ge1\) then \(q^{t-1}\le1\), and if \(t=0\) that derivative term is absent. Consequently \(|E_x|+|E'_x|\le C N^2 2^{-m/8}\) uniformly over this whole bias interval.

By the race formula, the log odds of the longer word are
\[
 O(p)=d\log q+\Delta\log(p/q)+e(p),\qquad
 \Delta=\#1(v)-\#1(w),\quad e=\log(1+E_w)-\log(1+E_v).
\]
The bound just proved gives \(\sup_p(|e|+|e'|)=O(N^2 2^{-N/16})\). If \(\Delta\le0\), then \(O'(p)=-d/q+\Delta/(pq)+e'(p)<0\) for sufficiently large \(N\). If \(\Delta\ge1\), the raw odds satisfy \(q^d(p/q)^\Delta\le p\le1/2\), so \(O(p)<0\) uniformly. Either way the indicator of \(O>0\) is non-increasing. Sum the retained indicators, dividing by the original total pair count. The original fraction exceeds this non-increasing subcount by between 0 and the removed fraction, proving the conclusion. ∎

**Corollary.** For every pair of fixed biases \(0<p_1<p_2<1/2\), there exist \(a>0,N_0\) depending on those biases such that \(H_N(p_1)-H_N(p_2)\ge a/\sqrt N\) for \(N\ge N_0\). This is an explicit alternative to using the full staircase law.

**Proof.** Write \(c_j=-\log(1-p_j)/\log((1-p_j)/p_j)\); then \(0<c_1<c_2\). Take a fixed gap \(d\) so large that \((-dc_2,-dc_1)\) contains an integer \(k\) strictly inside. The lengths \(M=N,m=N-d\) have limiting positive probability \((3/4)2^{-d}\). Conditionally, the chance \(\Delta=k\) is asymptotic to \(1/\sqrt{\pi N}\), since \(\Delta+(N-d)\sim\mathrm{Bin}(2N-d,1/2)\). With this gap and count difference, raw log odds are strictly positive at \(p_1\) and strictly negative at \(p_2\), with fixed margins. Outside the exponentially small exceptional collection the actual log odds have the same signs. These pairs, a fraction bounded below by a positive constant times \(N^{-1/2}\), switch from favorable to unfavorable; no retained pairs switch the other way. The exceptional fraction cannot offset this drop. ∎

The upper bound in this fixed-bias comparison is also \(O(N^{-1/2})\) by the lattice estimates in `asymptotics.md`, which additionally identify the limiting coefficient.
