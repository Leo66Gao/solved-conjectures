# Solved conjectures and mathematical results

**Leo Gao** · AI-assisted research · Not peer reviewed

Proofs, LaTeX manuscripts, and reproduction files. Each result is stated at the scope proved. Computational proofs use exact arithmetic; partial results are listed separately.

## Solved statements

| Result | Statement proved | Manuscript |
| --- | --- | --- |
| **Width of thin lattice simplices** | Kurylenko’s Conjectures 1.5 and 1.6 and both parts of Question 1.4. Odd-dimensional thin simplices have width one; in each fixed dimension only finitely many have width at least two. | [Proof](01-thin-simplices/Thin-simplex-proofs.md) · [PDF](01-thin-simplices/manuscript.pdf) · [LaTeX](01-thin-simplices/manuscript.tex) |
| **Fallat–Xing spectral spread, order 9** | A rank-two endpoint matrix attains the maximum spread for every nondegenerate entry interval in dimension nine. The unrestricted conjecture is not claimed. | [Proof](04-spectral-spread/n9/PROOF.md) · [PDF](04-spectral-spread/n9/manuscript.pdf) · [LaTeX](04-spectral-spread/n9/manuscript.tex) |
| **Fallat–Xing spectral spread, order 10** | The same statement in dimension ten, including the unequal-cluster case near the endpoint. Both finite-dimensional proofs use exact certificates. | [Proof](04-spectral-spread/n10/PROOF.md) · [PDF](04-spectral-spread/n10/manuscript.pdf) · [LaTeX](04-spectral-spread/n10/manuscript.tex) |
| **Line-graph signature at fixed cycle rank** | A finite reduction for every fixed cycle rank, and the exact conjectured maximum through rank seven. The formula remains open at higher ranks. | [Proof](05-line-graph-signature/NOTES.md) · [PDF](05-line-graph-signature/manuscript.pdf) · [LaTeX](05-line-graph-signature/manuscript.tex) |

## Further theorems

| Result | Statement proved | Manuscript |
| --- | --- | --- |
| **Couplings of finite uniform distributions** | Greedy coupling majorizes every coupling of two uniform distributions. An infinite family with three marginals has no greatest coupling and greedy is not Shannon-optimal. | [Proof](02-uniform-couplings/euclidean-majorization.md) · [PDF](02-uniform-couplings/manuscript.pdf) · [LaTeX](02-uniform-couplings/manuscript.tex) |
| **Almost-sure range of uniformly transient walks** | A sharp lower-envelope order of $t/\log\log t$; an expanding simple graph shows that a linear almost-sure lower bound need not hold. | [Proof](03-random-walks/Sharp-almost-sure-range.md) · [PDF](03-random-walks/manuscript.pdf) · [LaTeX](03-random-walks/manuscript.tex) |

## Partial result

**[Distinct covering systems](06-covering-systems/report.md)** · [PDF](06-covering-systems/manuscript.pdf) · [LaTeX](06-covering-systems/manuscript.tex)  
The exact conditional optima are 84 and 68 uncovered residues at periods 10,080 and 15,120 under the stated fixed-prefix constraints. Neither period is excluded globally.

## Reproducing the computations

- **Spectral spread:** run `sh 04-spectral-spread/reproduce.sh` with C++17, GMP, and Python 3. The certificates cover 12,451,530 exact positive-definiteness checks and the rational interpolation inequalities.
- **Line-graph signature:** see the [exact enumeration instructions](05-line-graph-signature/COMPUTATION.md) for cycle ranks six and seven.
- **Uniform couplings:** from the [verification directory](02-uniform-couplings/), run `python uniform_coupling.py 25` and `python verify_three_uniforms.py`.
- **Covering systems:** from the [certificate directory](06-covering-systems/), run `python proof_check.py`.
- **Integrity:** run `sha256sum -c SHA256SUMS.txt` from the repository root.

Each manuscript includes an AI-assistance disclosure and distinguishes its contribution from known results. No claim of peer review or confirmed priority is made.
