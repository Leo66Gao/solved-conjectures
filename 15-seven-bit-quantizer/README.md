# A seven-bit counterexample for most-informative quantization

**Leo Gao** · AI-assisted research · Not peer reviewed

An explicit seven-bit quantizer on 14 fair input bits preserves more information through a binary symmetric channel than seven input coordinates, at crossover probability 2/5 and for every crossover probability in [9/20, 1/2). This disproves Mahdavifar and Beirami’s seven-bit threshold conjecture ([v2, Conjecture 13](https://arxiv.org/abs/2609.26444v2)). It leaves the original one-bit theorem and the cases of two through six output bits unaffected.

[PDF](seven-bit-quantizer.pdf) · [LaTeX](seven-bit-quantizer.tex)

Run `python3 verify.py` for the exact cell counts and high-noise bound, `python3 independent.py` for an independent reconstruction of the counts, and `python3 verify-full.py` for the exact check at crossover probability 2/5. Python 3.10+; no third-party packages.
