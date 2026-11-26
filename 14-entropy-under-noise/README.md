# Which independent refresh chains have completely monotone Shannon entropy deficit?

**Leo Gao · AI-assisted research**

**Result:** A finite product of independent coordinate-refresh chains has completely monotone relative entropy to stationarity for every initial law exactly when, aside from deterministic factors, it is empty, a single fair bit, or two fair bits refreshed at equal rates. Every unequal rate ratio fails on two bits, even when it is arbitrarily close to one. Three fair bits suffice for a counterexample with equal rates.

This is a theorem about a discrete channel family, not a solution to the already-disproved Gaussian completely monotone conjecture. Novelty was searched, not certified. No peer review is claimed.

- [Read the paper](paper.pdf) · [LaTeX](paper.tex)
- [Exact verifier](verify.py): run `python3 verify.py` (no dependencies).
- [Numerical/exact checks](verification.txt)

The proof is analytic; finite-grid checks do not establish the two-bit infinite derivative hierarchy. The first failing derivative is not determined.
