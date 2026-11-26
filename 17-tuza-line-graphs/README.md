# Tuza’s conjecture for line graphs

AI-assisted research draft. Independent review and priority assessment are pending.

The manuscript proves the packing–covering inequality for line graphs of finite simple graphs. It also bounds the covering number in terms of the root graph’s degrees and characterizes equality. The general Tuza conjecture remains open.

[PDF](paper.pdf) · [LaTeX](paper.tex)

## Reproducing the checks

With NetworkX installed, run `python3 verify.py`. The script checks exact packing and covering witnesses on the full graph atlas, 100 seeded random graphs, and local clique orders through 200.

[Recorded output](verification.txt)

## Supplement on tight cores

A vertex-extension theorem and an incident-edge restoration argument restrict the shape of a hypothetical edge-minimal counterexample. Deleting the edges of any triangle would leave a tight graph with packing number one smaller and a triangle component other than a $K_4$ or $K_5$.

[Supplement PDF](tight-core.pdf) · [LaTeX](tight-core.tex)

With NetworkX installed, run `python3 verify-tight.py` for exact packing, covering, and open-wedge checks on the graph atlas. [Recorded output](tight-verification.txt)
