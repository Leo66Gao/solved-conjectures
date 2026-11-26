# Bapat’s real q-permanent monotonicity conjecture

AI-assisted research draft. Independent review and priority assessment are pending.

The manuscript specifies a real symmetric positive definite integer matrix of order $10^{35}$ with negative endpoint derivative. The witness is specified by a formula, and the manuscript establishes a violation between two points in the original interval $[-1,1]$.

[PDF](paper.pdf) · [LaTeX](paper.tex)

## Reproducing the checks

Run `python3 verify.py` with the Python standard library. It checks the rational inequalities and compares the endpoint identity against direct permutation sums for 72 small Gram matrices. The full counterexample matrix is represented by its defining formula.

[Recorded output](verification.txt)
