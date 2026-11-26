# Penney races: false uniform monotonicity, true fixed-bias monotonicity

**Leo Gao** · AI-assisted research · Independent review and priority assessment pending

Drexel, Peng and Richey's [Conjecture 1](https://doi.org/10.37236/13609) says that, at all sufficiently large length caps, increasing the density of ones toward one-half cannot increase the number of longer words favored in head-to-head races. This is false at every cap at least four. For each shorter length m≥4, the pair (01 followed by m−1 zeros, m zeros) crosses upward at the explicit bias 1−2^{-1/(m−2)}. An elementary finite-continuity argument makes that one pair decisive at the exact threshold even if other pairs switch in the opposite direction. Exact counts also increase between ordinary rational values at several small caps.

In fact an exponentially small fraction of exceptional pairs accounts for **all** departures from monotonicity simultaneously over the entire bias interval. A quantifier change also recovers strict monotonicity: **for any two fixed distinct biases below one-half, all sufficiently large caps favor more longer-word pairs at the smaller bias**. The proof gives a first-order lattice correction, with a jump at every rational log-likelihood slope. It also gives the nontrivial central-limit crossover within O(1/√N) of a fair coin. The first theorem is a direct counterexample to a published conjecture; the replacement laws are additional results. External priority and peer review have not been established.

- `proof.md`: primary conjecture, explicit family, elementary proof and prior-art caveat.
- `uniform-repair.md`: exponential uniform repair and a short independent route to the fixed-bias theorem.
- `asymptotics.md`: asymptotic and corrected monotonicity theorems, including an explicit overlap formula at lattice ties.
- `verify.py` and `check-results.txt`: exact integer enumeration and independent Markov-chain formula tests.
- `asymptotic_checks.py` and `asymptotic-results-fast.txt`: length/composition diagnostics.
- `resonance.cpp` and `resonance-results.txt`: exact four-boundary enumeration at the first arithmetic resonance.

Open: the all-cap disproof alone does not settle eventual uniform monotonicity *after* removing the exact tie biases. The finite-cap increases on open intervals do not settle that strengthened uniform-in-bias question for all sufficiently large caps. The cap size needed for a given pair of biases is not bounded explicitly here. The sparse-stream limit is also calculated: for any positive bias tending to zero, the scaled deficit tends to 3/2.
