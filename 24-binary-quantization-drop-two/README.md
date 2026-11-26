# Optimal binary quantization after dropping two bits

**Leo Gao** · AI-assisted research · Not peer reviewed

For a uniform n-bit input to an independent binary symmetric channel, transmitting n−2 input coordinates maximizes information about the channel output among deterministic quantizers with at most 2^(n−2) labels. This holds for all crossover probabilities and does not require equal-sized cells. In the six-bit problem it covers eight input bits, not arbitrary input dimensions.

[PDF](paper.pdf) · [LaTeX](paper.tex) · [Proof and certificate notes](unrestricted-two.md)

Run `python3 unbalanced2-all-p.py` to reproduce the exact checks; the optional two arguments select an inclusive cardinality range between 3 and 16.
