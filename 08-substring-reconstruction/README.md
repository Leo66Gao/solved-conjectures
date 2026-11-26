# Reconstruction from substring compositions

**Leo Gao** · AI-assisted research · Not peer reviewed

Exact worst-case class sizes are four at lengths $pq-1$ and $4p-1$, and eight at lengths $p^2q-1$, for odd primes that are distinct where two occur. The proof classifies all nontrivially ambiguous words at length $pq-1$. The conjecture for arbitrary lengths remains open.

[Read the PDF](equicomposable.pdf) · [LaTeX source](equicomposable.tex)

## Reproduce the checks

Compile `verify.cpp` and `verify_ternary.cpp` with C++17 and optimization; run the executables in this directory. Run `python3 partitions.py` for the finite partition check. Output logs are included.
