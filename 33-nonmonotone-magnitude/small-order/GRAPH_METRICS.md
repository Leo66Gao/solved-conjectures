# No connected unweighted graph of order at most eight gives a negative-type counterexample

**Theorem.** If a connected simple graph has \(2\le n\le 8\) vertices and its shortest-path metric has negative type, then \(M'(t)>0\) for all positive \(t\). This includes 2,570 isomorphism classes of order-eight negative-type shortest-path metrics having at least three distinct positive distances. This is not a theorem about arbitrary weighted graphs or arbitrary distances.

## Exact certificate

1. **Enumerate isomorphism types.** Starting with the singleton, extend each representative by one new vertex and every possible choice of its incident edges. The canonical labeling first repeatedly refines colors by their old color and vector of counts of adjacent colors; color names are assigned by lexicographic order of these isomorphism-invariant signatures. Finally minimize the labeled edge word over all orderings that respect color classes, allowing every permutation within each class. Isomorphic graphs get the same code by equivariance; graphs with the same code are isomorphic since that code is an actual relabeling. Extending by one vertex covers all types because any graph can be obtained by first deleting a vertex. The total enumerated counts match the [classical unlabeled graph counts](https://oeis.org/A000088); the proof does not require assuming those counts.
2. **Check metric and type.** Reject disconnected graphs; otherwise compute all shortest-path distances by integer Floyd–Warshall. With distance matrix \(D\), negative type is equivalent to positive semidefiniteness of the excess matrix \(B_{ij}=D_{i0}+D_{j0}-D_{ij}\), \(1\le i,j<n\). Indeed the distance quadratic form of a zero-sum vector is the negative of the excess quadratic form of its last \(n-1\) entries. Test the excess matrix by exact integer Schur complements: if a diagonal entry is negative, or zero with nonzero row, reject. A zero row and column can be removed. A positive pivot \(p\) reduces the test to the matrix \(pB_{\rm tail}-bb^T\), where \(b\) is the rest of the pivot column. This is the Schur complement multiplied by \(p>0\).
3. **Check all positive scales at once.** Put \(q=e^{-t}\), \(K_{ij}=q^{D_{ij}}\), \(P(q)=\det K(q)\), and \(N(q)=-\det\begin{pmatrix}K(q)&\mathbf1\\\mathbf1^T&0\end{pmatrix}\). By Gaussian positivity \(P>0\) where \(0<q<1\), and the magnitude equals \(N/P\). Its \(t\)-derivative has the sign of \(F(q)=N(q)P'(q)-N'(q)P(q)\). Compute these determinants using exact Laplace expansion by subsets; all entries are monomials or zero. Transform \(F\) by \(q=x/(1+x)\) and clear the positive denominator \((1+x)^{\deg F}\). Every surviving graph above has **all nonnegative integer coefficients and at least one positive coefficient** in the resulting polynomial. Hence \(F>0\) on \(0<q<1\). This is a test of coefficient signs, not of a grid of scale values. The optional exact Sturm fallback was never needed.

| Vertices | Connected | Negative type | Negative type and diameter at least 3 |
|---:|---:|---:|---:|
| 2 | 1 | 1 | 0 |
| 3 | 2 | 2 | 0 |
| 4 | 6 | 6 | 1 |
| 5 | 21 | 19 | 6 |
| 6 | 112 | 85 | 45 |
| 7 | 853 | 452 | 310 |
| 8 | 11117 | 3174 | 2570 |

**Reproduce:** `g++ -O3 -std=c++17 enumerate_graphs.cpp -o enum && ./enum | python verify_graph_metrics.py`. The Python part requires only the standard library. The graph generator and exact sign verifier do not read precomputed classifications or coefficients. Output is in `graph-metric-verification.txt` (typical run time a few seconds).

For background see [Leinster and Meckes on magnitude](https://arxiv.org/abs/1606.00095) and [Gomi and Tsuji on the small-order question](https://arxiv.org/html/2608.15720v1). The sources located do not give this finite classification; this is not a comprehensive claim of bibliographic priority.
