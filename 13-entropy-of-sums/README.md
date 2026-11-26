# Sharp entropy of finite-alphabet sums with symmetric summands

**Status:** proved subclass of Kovačević’s maximum-entropy conjecture; not a solution of the unrestricted conjecture. AI-assisted research manuscript by Leo Gao. Not peer reviewed.

- **Inputs:** independent integer-valued variables in `{0,...,r}` for arbitrary `r,n >= 1`. At most one marginal can be arbitrary; the other marginals are symmetric, even about different individual centers.
- **Result:** sharp upper bound, attained by exactly the conjectured input laws up to permutation. If `h_d` is fair-binomial Shannon entropy in nats, the maximum is `log(exp(h_n) + (r−1) exp(h_{n−1}))`. In the common-midpoint case the entropy deficit dominates relative entropy to the optimizing sum law.
- **Why it matters:** all larger alphabet sizes are covered within a natural class, matching the symmetry regime of the established continuous theorem. A separate argument is essential for the finite-lattice boundary atoms. Previous unrestricted work settles the binary and ternary alphabets and the case of two summands; these overlaps are not new results here.
- **Proof and reproducibility:** [paper.pdf](paper.pdf), [LaTeX source](paper.tex), [integer-only verifier](verify.py), [recorded output](verification.txt). The argument is analytic; tests do not stand in for a proof. Run `python3 verify.py 9 14` to reproduce the recorded larger check; `python3 verify.py` runs a shorter check.
- **Original contribution asserted in this note:** the discrete boundary/open-cell comparison after conditioning on endpoint signs, the resulting sharp symmetric-case bound with rigidity, and the translated half-grid treatment. The cube isodiametric theorem is cited, not claimed. Search did not reveal the discrete theorem but this is not an exhaustive or independent priority certification.

## Adversarial checks

1. Dropping all midpoint hypotheses breaks the linear supporting certificate: deterministic zeros have positive centered cost when `n>=2`. This does **not** disprove the underlying entropy conjecture.
2. An integer tie in the interior cannot simply be discarded as in the continuous problem. Comparing the actual boundary cost with the farther open-cell cost after averaging the endpoint binomial is what closes this gap.
3. Closed tails use a **strictly shortened** sign family. A diameter argument used indiscriminately on endpoint signs is wrong; they are first split off and convolved back at the last step.
4. The middle tie when the number of shortened signs is even has two equally priced neighboring cells. The cases of zero/one shortened sign, midpoint atoms, and `r=1` are included.
5. Shifting individually symmetric marginals can leave a half-integer lattice. The proof uses a separately normalized reference measure there; it does not assign half-integer inputs to the old probability mass function.
6. Identifiability is separate from KL equality: the polynomial root at `exp(i*pi/r)` forces the prescribed endpoint factors without a uniqueness assumption.
7. Independent midpoint symmetrization is not an entropy-increasing operation in general: the paper gives a pair of explicit four-symbol rational laws such that symmetrizing both strictly lowers the sum entropy, verified by integer products. This blocks the straightforward route to proving the unrestricted conjecture.
8. The verifier compares products of integer powers of primes, not floating-point entropies; it tests all unordered radius vectors in its stated parameter range. The odd-diameter tail bound is checked separately with exact integer counts.

## Prior-art screen (26 November 2026)

- [Kovačević, original conjecture, 2021](https://doi.org/10.1137/S0040585X97T99054X); [author preprint](https://arxiv.org/abs/2008.01138). Includes the construction, binary/other special cases, and all two-summand alphabets.
- [Kovačević, ternary result, 2026](https://doi.org/10.1016/j.spl.2026.110867); [full author preprint including failure of the residue-class method for r≥3](https://arxiv.org/html/2605.11831v1). Solves arbitrary marginals for r=2, not general r.
- [Ordentlich, continuous symmetric extremum](https://doi.org/10.1109/TIT.2006.872858), [Yu, shorter proof](https://doi.org/10.1109/TIT.2008.917660). Their differential-entropy laws are not discrete lattice laws.
- [Huang, Klurman and Pohoata, Theorem 1.1](https://arxiv.org/abs/1812.05989), a primary proof of the exact odd-diameter input.
- Searches used the conjecturer’s name and diacritic variants with “symmetric summands”, “all alphabets”, finite/discrete and bounded-additive-channel terminology, the continuous authors’ names, and searches including recent AI work. No equivalent prior discrete symmetric theorem surfaced. Expert literature review is appropriate before any novelty or priority claim.
