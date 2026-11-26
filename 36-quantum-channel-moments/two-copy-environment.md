# A separate finite-order clause: environment monotonicity at two copies

Conjecture 1 in Appendix B of [Duschenes et al.](https://arxiv.org/html/2511.12700v2) verbally asks, among other things, whether the cHaar moment operator's Hilbert–Schmidt norm is nonincreasing as environment dimension grows. Its displayed environment inequality reverses the words. We establish the decreasing direction for every fixed concatenation count k≥1 and system dimension d≥2 at t=2. This does not establish the all-t conjecture.

The [published public counterexample note, “Eventual increase for every d,e”](https://www.trureturing.org/research/duschenes-garciamartin-holmes-cerezo-2026-chaar-concatenation/) gives, in a calculation independent of the environment-monotonicity question, the exact formula

    N_e = ||(T_2)^k||_F²
        = 1 + (d²−1) h(e)² + q(e)^{2k},
    q(e)=e(d²−1)/(d²e²−1),  h(e)=(1−q(e)^k)/(d²e+1).

It also follows by taking powers of the two-by-two triangular block in the identity/swap basis. For real e≥2,

    h(e) = [(e−1)/(d²e²−1)] [1+q+⋯+q^{k−1}].

The first bracket is positive and strictly decreasing: its derivative has numerator d²e(2−e)−1<0. The second bracket is positive and nonincreasing because q has derivative −(d²−1)(d²e²+1)/(d²e²−1)². Thus N_e is strictly decreasing on [2,∞). The remaining integer step, e=1 to 2, is also strict: N_1=2, while for e≥2 we have 0<x=q(e)^k<1, c=(d²−1)/(d²e+1)²<1 and hence N_e=1+c(1−x)²+x²<1+(1−x)²+x²<2. This proves the claim. The exact norm formula itself, and its *non*-monotonicity in k, are prior work, not discoveries here.
