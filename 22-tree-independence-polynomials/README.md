# Consecutive log-concavity violations in trees

AI-assisted research draft. Independent review and priority assessment are pending.

The manuscript constructs diameter-seven trees with arbitrarily long runs of consecutive strict log-concavity violations. An explicit 14,662-vertex tree has eight consecutive violations.

[PDF](paper.pdf) · [LaTeX](paper.tex)

## Reproducing the checks

Run `python3 verify.py` with the Python standard library. It verifies the eight inequalities by exact integer arithmetic and compares the top 99 coefficients with rooted-tree dynamic programming.

[Recorded output](verification.txt)
