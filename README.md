# Project Prometheus: six research runs
26 November 2026 · AI-assisted research notes · Not peer reviewed

Six agents independently selected problems from the same research prompt. These are the strongest documented results, with scope, proofs, and executable checks where relevant. A complete argument below means complete at the stated scope, not independently published or field-verified. Literature searches did not establish priority.

| Result | What is established at this scope |
| --- | --- |
| [Thin lattice simplices](01-thin-simplices/Thin-simplex-proofs.md) | Proofs of Kurylenko’s Conjectures 1.5 and 1.6 and both parts of Question 1.4. Every odd-dimensional thin simplex has width one. In any fixed dimension only finitely many thin simplices have width at least two, with normalized volume at most `(d+1)!`. Spanning thin simplices that are not free joins are finite in each dimension and absent in odd dimensions. |
| [Couplings of uniform distributions](02-uniform-couplings/euclidean-majorization.md) | The greedy coupling of two finite uniforms simultaneously maximizes every top-`k` mass sum, hence minimizes all Rényi entropies. For the family of three uniform marginals with sizes `(3,4,12t+7)`, a greatest mass vector does not exist and greedy is Shannon-suboptimal. |
| [Almost-sure random-walk range](03-random-walks/Sharp-almost-sure-range.md) | Uniform escape gives a sharp almost-sure lower bound on the `t/log(log(t))` scale. A tree of cliques shows this is the best general order for vertex-expanding simple graphs, despite linear expected range. The exact coefficient is proved sharp for countable Markov chains, not for undirected graphs. |
| Fallat–Xing spectral spread in [dimension nine](04-spectral-spread/PROOF-DIMENSION-9.md) and [dimension ten](04-spectral-spread/PROOF-DIMENSION-10.md) | Full parameter-interval proofs for nine-by-nine and ten-by-ten real symmetric matrices; no assertion about higher dimensions. The included archive contains exact certificates for 12,451,530 positive-definiteness tests and rational interpolation inequalities. |
| [Line-graph signature](05-line-graph-signature/NOTES.md) | A finite reduction of the maximum-signature problem at each fixed cycle rank, to graphs with at most `19(c-1)` vertices for `c >= 2`. The conjectured maximum is proved through cycle rank seven, with exact computation for ranks six and seven; the all-rank formula remains open. |
| [Distinct covering systems](06-covering-systems/report.md) | Exactly certified conditional optima of 84 and 68 uncovered residues at periods 10,080 and 15,120, respectively, for the specified fixed prefixes. Neither period is globally excluded. |

## Reproduce the computational checks
- Uniform coupling: in `02-uniform-couplings`, run `python uniform_coupling.py 25` and `python verify_three_uniforms.py`. These independent integer checks supplement the proofs.
- Spectral spread: unpack the inner archive in `04-spectral-spread`, then follow its proof note. The verifier requires C++17 and GMP. Verification itself uses no NumPy and no floating point.
- Line-graph signature: see `05-line-graph-signature/COMPUTATION.md` for reproducing the checked-integer enumeration at cycle ranks six and seven.
- Covering systems: in `06-covering-systems`, run `python proof_check.py`. The checker validates the integer certificates and the explicit assignments, independently of the floating-point search.
- The proof notes cite the original sources and distinguish completed results from conjectures, novelty checks, and incomplete searches. Nothing here was submitted for publication.
