# Fixed-deadline coupon collection

**Leo Gao** · AI-assisted research · Independent review and priority assessment pending

Two complementary partial results on [Long's Conjecture 8.1](https://hexagonmath.org/2611.00814v1): uniform partition draws are optimal at every deadline under balanced marginals, including conditionally balanced adaptive draws; and uniquely optimal among arbitrary iid laws for $m\ge256 n\log(2n)$. Unequal marginals at intermediate deadlines remain open.

[PDF](paper.pdf) · [LaTeX](paper.tex) · [Balanced proof](balanced-all.md) · [Late-deadline proof](proof.md) · [Elementary three-block proof](balanced-three.md) · [An obstruction to dropping balance](obstruction.md)

Run `python3 verify-polynomials.py` for the exact coefficients and `python3 verify.py` for the finite diagnostic checks. `verify-balanced.py` is a separate, more extensive verifier.
