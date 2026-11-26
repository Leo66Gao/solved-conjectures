# Solved conjectures and mathematical results

**Leo Gao** · AI-assisted research · Not peer reviewed

Proofs, LaTeX manuscripts, and reproduction files. Each result is stated at the scope proved. Computational proofs use exact arithmetic; partial results are listed separately.

## Solved statements and cases

| Result | Statement proved | Manuscript |
| --- | --- | --- |
| **Width of thin lattice simplices** | Kurylenko’s Conjectures 1.5 and 1.6 and both parts of Question 1.4. Odd-dimensional thin simplices have width one; in each fixed dimension only finitely many have width at least two. | [Proof](01-thin-simplices/Thin-simplex-proofs.md) · [PDF](01-thin-simplices/manuscript.pdf) · [LaTeX](01-thin-simplices/manuscript.tex) |
| **Fallat–Xing spectral spread, order 9** | A rank-two endpoint matrix attains the maximum spread for every nondegenerate entry interval in dimension nine. The unrestricted conjecture is not claimed. | [Proof](04-spectral-spread/n9/PROOF.md) · [PDF](04-spectral-spread/n9/manuscript.pdf) · [LaTeX](04-spectral-spread/n9/manuscript.tex) |
| **Fallat–Xing spectral spread, order 10** | The same statement in dimension ten, including the unequal-cluster case near the endpoint. Both finite-dimensional proofs use exact certificates. | [Proof](04-spectral-spread/n10/PROOF.md) · [PDF](04-spectral-spread/n10/manuscript.pdf) · [LaTeX](04-spectral-spread/n10/manuscript.tex) |
| **Line-graph signature at fixed cycle rank** | A finite reduction for every fixed cycle rank, and the exact conjectured maximum through rank seven. The formula remains open at higher ranks. | [Proof](05-line-graph-signature/NOTES.md) · [PDF](05-line-graph-signature/manuscript.pdf) · [LaTeX](05-line-graph-signature/manuscript.tex) |
| **Random-to-below card shuffling** | Grinberg–Lafrenière’s Conjecture 15.8 for every deck size, with a Gumbel separation profile. | [Details](07-random-to-below-shuffle/) · [PDF](07-random-to-below-shuffle/paper.pdf) · [LaTeX](07-random-to-below-shuffle/paper.tex) |
| **Reconstruction from substring compositions** | Exact maximum class sizes at lengths $pq-1$, $p^2q-1$, and $4p-1$ for the specified primes; full ambiguity classification at length $pq-1$. | [Details](08-substring-reconstruction/) · [PDF](08-substring-reconstruction/equicomposable.pdf) · [LaTeX](08-substring-reconstruction/equicomposable.tex) |

## Further theorems

| Result | Statement proved | Manuscript |
| --- | --- | --- |
| **Couplings of finite uniform distributions** | Greedy coupling majorizes every coupling of two uniform distributions. An infinite family with three marginals has no greatest coupling and greedy is not Shannon-optimal. | [Proof](02-uniform-couplings/euclidean-majorization.md) · [PDF](02-uniform-couplings/manuscript.pdf) · [LaTeX](02-uniform-couplings/manuscript.tex) |
| **Almost-sure range of uniformly transient walks** | A sharp lower-envelope order of $t/\log\log t$; an expanding simple graph shows that a linear almost-sure lower bound need not hold. | [Proof](03-random-walks/Sharp-almost-sure-range.md) · [PDF](03-random-walks/manuscript.pdf) · [LaTeX](03-random-walks/manuscript.tex) |
| **Perfect state transfer** | Unit-gain circulants admit universal perfect transfer only on two or three sites; the allowed triangle phases are classified. | [Details](09-perfect-state-transfer/) · [PDF](09-perfect-state-transfer/paper.pdf) · [LaTeX](09-perfect-state-transfer/paper.tex) |
| **q-Stirling coefficient limits** | A boundary classification and uniform local Gaussian limit, plus an explicit sign-reversing involution for two known identities. | [Details](10-q-stirling/) · [PDF](10-q-stirling/result.pdf) · [LaTeX](10-q-stirling/result.tex) |
| **Ehrhart roots of arbors** | All roots are real for singleton arbors of height at most two; at height three the number of distinct nonreal pairs can grow at least as the square root of the dimension. | [Details](11-ehrhart-roots/) · [PDF](11-ehrhart-roots/paper.pdf) · [LaTeX](11-ehrhart-roots/paper.tex) |

## Partial results

**[Distinct covering systems](06-covering-systems/report.md)** · [PDF](06-covering-systems/manuscript.pdf) · [LaTeX](06-covering-systems/manuscript.tex)  
The exact conditional optima are 84 and 68 uncovered residues at periods 10,080 and 15,120 under the stated fixed-prefix constraints. Neither period is excluded globally.

**[Elementary-positive spider graphs](12-spider-graphs/)** · [PDF](12-spider-graphs/spider.pdf) · [LaTeX](12-spider-graphs/spider.tex)  
Finiteness for fixed shortest leg at least two other than three. The exact classification and shortest-leg-three finiteness are not settled.

## Reproducing the computations

- **Spectral spread:** run `sh 04-spectral-spread/reproduce.sh` with C++17, GMP, and Python 3. The certificates cover 12,451,530 exact positive-definiteness checks and the rational interpolation inequalities.
- **Line-graph signature:** see the [exact enumeration instructions](05-line-graph-signature/COMPUTATION.md) for cycle ranks six and seven.
- **Uniform couplings:** from the [verification directory](02-uniform-couplings/), run `python uniform_coupling.py 25` and `python verify_three_uniforms.py`.
- **Covering systems:** from the [certificate directory](06-covering-systems/), run `python proof_check.py`.
- Each result’s page links to its verification commands and source files.
- **Integrity:** run `sha256sum -c SHA256SUMS.txt` from the repository root.

Each manuscript includes an AI-assistance disclosure and distinguishes its contribution from known results. No claim of peer review or confirmed priority is made.
