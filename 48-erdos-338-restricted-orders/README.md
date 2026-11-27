# Uniform bounds on the restricted order of an additive basis

**Leo Gao** · AI-assisted research

This manuscript answers the uniform-bound question in [Erdős–Graham problem #338](https://www.erdosproblems.com/338). If a basis of ordinary order $h$ has a finite restricted order, it is bounded by a function of $h$ alone. More precisely, if $F(h)$ is the largest finite restricted order among bases of ordinary order exactly $h$, then $\log\log F(h)=\Theta(h)$.

The upper bound uses a finite-group lemma that caps the cost of correcting residues before the modulus is known. The lower bound comes from explicit mixed-radix, eventually periodic bases. It is already doubly exponential in $h$.

This is a separate contribution from [Chen, Yang and Zhao’s existence criterion and finite-deletion theorem](https://arxiv.org/abs/2611.33191), on whose quantitative lemma the upper bound builds. The manuscript does not characterize when the two orders coincide. It has not been externally peer reviewed.

- [Paper (PDF)](restricted-orders.pdf) · [LaTeX](restricted-orders.tex) · [Markdown](restricted-orders.md)
- [Exact optional check for the small mixed-radix examples](check_growth.py) · [Output](check_growth.txt)
