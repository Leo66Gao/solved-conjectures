# Bapat’s real q-permanent monotonicity conjecture

AI-assisted research draft. Independent review and priority assessment are pending.

The manuscript specifies a real symmetric positive definite integer matrix of order $10^{35}$ with negative endpoint derivative. The witness is specified by a formula, and the manuscript establishes a violation between two points in the original interval $[-1,1]$.

[PDF](paper.pdf) · [LaTeX](paper.tex)

## Order-8,192 certificate

The explicit integer matrix $A=WW^{\mathsf T}+I_{8192}$ violates monotonicity. The exact checker reconstructs the bundled Gram factor, bounds the normalized endpoint derivative strictly below $-1/8000$, and certifies a strict decrease at two interior points.

[Certificate and run instructions](order-8192/) · [Proof](order-8192/proof.md) · [Recorded output](order-8192/verification-local.txt)

## Reproducing the checks

Run `python3 verify.py` with the Python standard library. It checks the rational inequalities and compares the endpoint identity against direct permutation sums for 72 small Gram matrices. The full counterexample matrix is represented by its defining formula.

[Recorded output](verification.txt)

## Rank-three supplement

The supplement gives a positive definite integer witness of order 271,147,008 with negative endpoint derivative. Its ordered Gram factor has three columns before the positive diagonal lift. The proof gives a strict comparison at two rational points inside the original interval.

[Supplement PDF](rank-three.pdf) · [LaTeX](rank-three.tex) · [Exact rational checker](rank3_certificate.py) · [Recorded output](rank3-verification.txt)

Run `python3 rank3_certificate.py` with the Python standard library. The script verifies the inequalities in the analytic certificate. The script bounds the full derivative through the analytic certificate.
