# The first unresolved order: no sparse counterexample at five

At order 5, every circulant unistochastic matrix with a zero entry admits a circulant unitary lift. In conjunction with the 6×6 example this puts any smaller counterexample strictly inside the positive part of the stochastic simplex. It does **not** decide whether such a matrix exists.

By multiplying by a cyclic column permutation we can put a zero coefficient at displacement 0. Write the square roots of the other four coefficients in order as `a,b,c,d`. First assume all four are positive and `a²+b²+c²+d²=1`. An exact characterization is:
1. the three lengths `ab,bc,cd` are the sides of a possibly degenerate triangle;
2. `b²c²−a²b²−c²d²=a²d²−a²c²−b²d²`.

**Necessity for an arbitrary unitary.** Consider rows 0 and 1 of a purported lift. Their three nonzero inner-product terms lie in columns 2,3,4 and have lengths `ab,bc,cd`. Write `δ` for the angle between the terms in columns 2 and 4. Their sum must have length `bc`, so
```
2abcd cos δ = b²c²−a²b²−c²d².
```
Now consider columns 2 and 4. Their three common nonzero rows are 0,1,3 with respective lengths `bd,ac,ad`. The first and second terms have relative angle `δ` up to sign: in both calculations the relevant phase is that of the same rectangle product `U_02 conj(U_12) conj(U_04) U_14` or its conjugate. Hence their sum has squared length `b²d²+a²c²+2abcd cosδ=a²d²`, giving (2).

**Sufficiency with a circulant lift.** Choose angles `A,B,C` such that
```
ab exp(iA)+bc exp(iB)+cd exp(iC)=0.
```
They exist by (1). Put `c_0=0` and give `c_1,c_2,c_3,c_4` moduli `a,b,c,d` and phases `0,A,A+B,A+B+C`. The cyclic autocorrelation at shift 1 vanishes by construction. At shift 2 the three remaining terms are
```
ac exp(i(A+B)),  bd exp(i(B+C)),  ad exp(−i(A+B+C)).
```
The squared modulus of the sum of the first two is `a²c²+b²d²+2abcd cos(A−C)=a²d²` by (2) and the first triangle. Add the same parameter `t` to each of `A,B,C`; this preserves shift 1, rotates that sum by `2t` and rotates the third term by `−3t`. Choose `5t` to make the terms cancel. Shifts 3 and 4 are conjugates of 2 and 1; shift 0 is 1. This gives a circulant unitary lift, including degenerate triangles.

**Smaller supports.** A singleton support is a cyclic permutation. A two-point support has a singleton overlap with a nonzero translate, ruling out any unitary lift. For a three-point support partition its three unordered pairs into cyclic distance 1 and distance 2. Neither category can contain all three pairs, since the graph formed by either distance is a 5-cycle with no triangle. One category therefore contains exactly one pair; the corresponding oriented shift then gives a singleton overlap and prohibits a unitary lift. The zero support is not stochastic. This exhausts the boundary.

An exact parametrized example: probabilities `p=(0,x,x,x,x)` with `x=1/4` satisfy both conditions; arbitrary four positive probabilities do not. More generally the equality in (2), not an inequality, cuts out an algebraic surface in the three-dimensional face. This requirement concerns existence of a lift at all, not just existence of a circulant lift.

Primary context and source scope are documented in [RESULT.md](RESULT.md). We did not locate this precise boundary formula in the sources screened; no comprehensive claim of priority.
