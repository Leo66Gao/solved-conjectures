# Fallat–Xing spectral spread: dimensions 9 and 10

This package gives computer-assisted proofs of the 2012 Fallat–Xing conjecture **for dimensions 9 and 10**, for every nondegenerate real entry interval. It does not resolve the conjecture in arbitrary dimension. Prior work covered dimension eight and selected cases beyond it; see the primary sources in each proof. Our literature check was bounded, and there has been no external review of these results.

For a real symmetric matrix, the spread is the largest eigenvalue minus the smallest. For entries in [a,1] with -1 <= a < 1, the largest possible spread in either dimension n is

    max_{1<=k<n} sqrt((k*a-(n-k))^2+4*k*(n-k)).

It is attained by the rank-two matrix that has a k-by-k square block of a's and ones everywhere else. The proofs restrict the unrestricted problem to 131,072 signed patterns (n=9) or 524,288 (n=10); use a small number of analytic exclusions; and certify the rest with exact integer positive-definiteness checks, plus exact rational tangents to extend from finitely many nodes to entire parameter intervals. Dimension ten includes a separate interlacing proof for an unequal pair of competing blocks that ties to first order at a=1.

## Reproduce

In each subdirectory, with a C++17 compiler, GMP development headers/libraries and Python 3 installed:

    g++ -O3 -std=c++17 verify.cpp -lgmpxx -lgmp -o verify
    python3 -O verify_arithmetic.py

Read each PROOF.md for a self-contained argument and an explanation of what the finite checks certify. No floating-point software is used by the certificate checker. NumPy is optional, for regenerating initial rational guesses only.

Verified integer positive-definiteness counts:

| Dimension | Left endpoint | Interior nodes | Right endpoint | Total |
| --- | ---: | ---: | ---: | ---: |
| 9 | 988 | 2,358,900 | 131,050 | 2,490,938 |
| 10 | 2,008 | 9,434,448 | 524,136 | 9,960,592 |

In each dimension 16 strict scalar inequalities cover eight contiguous intervals, with separate analytic and exact scalar checks at the ends. Witness tables and logs are included.
