# Real q-permanent monotonicity counterexample, order 8192

This directory specifies **one fixed integer matrix** A = W W^T + I, with W supplied as an 8192-by-3 JSON array. It certifies P'_1(A)<0 with explicit finite coefficient arithmetic. It does not compute the full integer derivative; rigorous bounds on its two terms suffice. No numerical sphere sampling, asymptotic estimates, downloaded data, or precomputed permanent bounds are required.

## Running

Requires Python 3.9+ (standard library, Unix resource module), a C++17 compiler available as `g++` with unsigned __int128 support. On a Unix-like system:

    python3 verify.py

The default uses entirely integer dyadic outward rounding in C++ and exact Python fractions. A second faster implementation uses directed long-double arithmetic:

    python3 verify.py --kernel interval

The latter additionally needs IEC binary long double with at least 64 significand bits and working directed rounding (tested on x86-64 GCC). The arithmetic checks reject an unsupported environment. Do not run Python with -O or change the C++ flags to fast-math. Both modes compile their own source, compare with small direct permutation sums, reconstruct the supplied W and recompute the complete sparse norm bound. There is no option to supply a precomputed bound. The only floating-point numbers in Python are printed for human readability and runtime measurement.

Files:
- `witness_8192_rows.json`: exact ordered integer Gram factor W, 8192 rows, 3 columns.
- `verify.py`: exact construction, independent small tests, integer exterior-numerator calculation, positive-definite lift and rational sign certificate.
- `ring_dyadic.cpp`: integer-only upper norm kernel.
- `ring_interval.cpp`: alternative hardware-directed upper norm kernel.
- `proof.md`: mathematical justification of both kernels and the lift.
- [Local integer verification output](verification-local.txt) and the two original run logs.

SHA256 of the supplied factor:
9a773987466300c0fdb99741fbfbf3f9ffe9413f627210aba246eefc12852298

Expected final output includes R certified lower (display) approximately 1.0001340517 and CERTIFIED: A=W W^T+I positive definite, integer, non-diagonal; P_prime(1)<0. The exact comparison is performed on rational numbers before success is printed.

This is the smallest dimension certified in this research session, not a claim of minimality. The previous 2560-row candidate remains uncertified. Four 8064-row trials failed this sufficient certificate, which does not exclude them as counterexamples. No external referee or proof assistant has verified this result.

## Measured full-package runs

Intel Xeon Platinum 8370C, x86-64, GCC, Linux. Both commands above were executed in full, including compilation, direct permutation self-tests, sparse norm calculation, reconstruction of the actual Gram factor and exact final inequalities. The interval run took 17.17 s wall time and 100256 KiB peak RSS; the integer-only run took 56.17 s and 100232 KiB peak RSS. Both exited with status zero. The logs `package_interval.log` and `package_integer.log` are included.

The integer verification also passed on macOS with Apple Clang in 13.68 seconds. The archived source was adjusted to disambiguate a C++ helper name and report macOS memory usage in KiB. The arithmetic and the supplied Gram factor are unchanged.
