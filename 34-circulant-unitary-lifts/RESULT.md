# Symmetry can disappear on taking squared moduli: two obstructions to circulant unitary lifting

## Result and scope

Write indices modulo `N`. A stochastic matrix with entries `B_ij=p_{j-i}` is **circulant unistochastic** if some unitary `U` satisfies `B_ij=|U_ij|²`. A circulant lift additionally requires `U_ij=c_{j-i}`.

**Theorem.** In every composite dimension `N≥6`, there is a circulant unistochastic matrix without a circulant unitary lift. In particular the first row
```
(1/2, 1/6, 0, 1/6, 0, 1/6)
```
works in dimension 6. The least dimension of failure is consequently 5 or 6. The even-order examples may even be entrywise positive and rational, with a quantitative obstruction; see [POSITIVE.md](POSITIVE.md). For example, the all-positive order-6 first row is (32398,10800,1,10800,1,10800)/64800. We have not decided any odd prime dimension ≥5. The separate proof [THREE.md](THREE.md) handles 9 (indeed, all multiples of 3 at least 6) via a cubic phase obstruction. At order 5 every example with at least one zero has a circulant lift whenever it has any unitary lift; see [ORDER5.md](ORDER5.md) for the exact boundary test. Moreover, every circulant orthostochastic matrix at order 5 has a real circulant orthogonal lift ([REAL5.md](REAL5.md), with a short exact enumeration); any order-5 counterexample must require complex phases as well as full support. This is a single-matrix lifting result, not a characterization of spectra or a nonexistence result for general lifts.

The universal assertion was **already refuted**, and is not a new disproof here. Rajchel-Mieldzioć, Korzekwa, Puchała & Życzkowski, [J. Math. Phys. 63 (2022), Lemma 18 and Conj. 19](https://arxiv.org/pdf/2101.11288), establish equality through dimension 4 and pose it in all dimensions. The [TrureTuring primary proof record](https://www.trureturing.org/research/rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift/) reports a machine-checked refutation at 10 and a proof for every even order ≥10, explicitly leaving 6, 8 and odd dimensions outside its result. The small even orders and odd composite family below extend the dimension coverage of those sources. Targeted searches for further examples and equivalent formulations found no identical theorem; this is not exhaustive bibliography or priority certification. The classical obstruction in the even proof is not claimed as a new Hadamard theorem.

## 1. A flat bipartite transition kernel

Let `N=2k` and `0<a<1`. Put `b=sqrt(1-a²)`. Define
```
p_0=a²,       p_j=b²/k for all odd j,       p_j=0 for all other j.
```
This is unistochastic: order the indices by parity, choose any normalized `k×k` Fourier matrix `F`, and set
```
U = [ a I     b F  ]
    [−b F*    a I  ] .
```
Then `UU*=I`, and the squared entries have exactly the stated values. Choosing `a²=1/2` yields rational counterexamples, in particular the displayed one.

Suppose a circulant lift `C` exists. Multiply by a scalar unit complex number so its diagonal is `a`, and write `C=aI+bQ`. The circulant `Q` has coefficients only at odd displacements. In `CC*=I`, the term `Q+Q*` has odd support while `QQ*` has even support. Thus `Q*=-Q` and `QQ*=I`. Under Fourier diagonalization of the circulant, each eigenvalue is consequently `i e_r` with `e_r∈{−1,1}`. The absence of even coefficients implies `e_{r+k}=−e_r` (evaluation at minus a root of unity flips the sign of an odd polynomial).

Write `P(x)=Σ_{r=0}^{k−1} e_r x^r`. Fourier inversion gives the modulus of the coefficient of `Q` at each odd displacement `j` as `|P(exp(−π i j/k))|/k`. It must be `1/√k`. Equivalently, `|P(x)|²=k` at every root of `x^k=−1`. Define signed periodic extension `e_{r+k}=−e_r`, and its negaperiodic correlation
```
C_h=Σ_{r=0}^{k−1} e_r e_{r+h}.
```
For these roots, `P(x)P(x^{-1})` reduced using `x^k=−1` is `Σ_{h=0}^{k−1} C_h x^h` (wraparound terms change sign). The roots are distinct, so `C_h=0` for `1≤h<k`. Conversely such signs, inserted into the Fourier eigenvalues `i(e_0,...,e_{k−1},−e_0,...,−e_{k−1})`, produce a skew-Hermitian unitary `Q` with the required moduli. This proves an exact equivalence with existence of a real negacyclic Hadamard matrix of order `k`.

For a self-contained contradiction when `k>2`: odd `k` cannot have `C_1=0`, an odd sum of signs. For even `k`, the product of the `k` summands in `C_h` is `(−1)^h` for `1≤h<k` (exactly `h` terms wrap). A zero sum would make the same product `(−1)^{k/2}`. Using both `h=1` and `h=2` gives opposite signs. For `k=1,2` signs exist. This agrees with [Lee and Szöllősi (2013), Lemma 3.2](https://journals.uwyo.edu/index.php/ela/article/download/1323/1323/1323) on negacyclic Hadamard matrices. The new use here is the Fourier/parity equivalence for the transition kernel.

## 2. Exact mass quantization in a short cyclic band

Fix `N=km`, integers `k≥2, m≥5`. Suppose a circulant unitary with coefficient vector `c_j` is supported on the three residue classes `d=−1,0,1 (mod m)`. Define `M_d=Σ_{j≡d (mod m)} |c_j|²`. Then
```
k M_d ∈ {0,1,...,k}     (d=−1,0,1).
```
Indeed write its Fourier eigenvalue as `Σ_{d=-1}¹ z^d A_d(z^m)` on `z^N=1`, with `A_d(w)=Σ_{t=0}^{k−1} c_{d+tm}w^t` (indices modulo N). Fix a `k`th root `w`; the expression `L(z)=z^{-1}A_{-1}(w)+A_0(w)+z A_1(w)` has modulus 1 at all `m` distinct roots of `z^m=w`. On the unit circle the Laurent polynomial `L(z)overline{L(1/conj(z))}−1` has exponents in `[−2,2]`. After multiplication by `z²` the degree is at most four, so it vanishes identically. Thus exactly one of the three coefficients is nonzero, of modulus 1: the coefficient at the maximal exponent difference in `L L* ` is the product of the extreme nonzero coefficients, impossible for a positive difference. Summing `|A_d(w)|²` over all `w` and using Parseval gives `kM_d=#{w: |A_d(w)|=1}`. This elementary finite-cycle argument is related to the classic scalar finite-propagation no-go lemma of [Meyer (1996)](https://arxiv.org/abs/quant-ph/9604011), but concerns masses of displacement classes in a finite cyclic group.

## 3. An ordinary unitary with fractional band mass

Write `i=ma+r` with `0≤a<k,0≤r<m`. In the `k`-dimensional fibre choose the orthonormal Fourier vectors `u_a=1/√k`, `v_a=exp(2π i a/k)/√k`. Let `P=uu*+vv*`, `R=uv*`. Choose `0<s<1` and `t=sqrt(1-s²)`. With `T_{r,l}=1` if `l=r+1 (mod m)` and zero otherwise, set
```
U = [I+(t−1)P] ⊗ I_m + s ( R ⊗ T − R* ⊗ T* ).
```
In fact `X=R⊗T−R*⊗T*` is skew-Hermitian with `X²=−P⊗I`, since `R²=(R*)²=0`, `RR*+R*R=P`. The first term commutes with `X` and its square is `[I−s²P]⊗I`; thus `UU*=I`.

The three terms access three disjoint residual displacements `0,+1,−1 (mod m)`. For the central class (`r=l`), the block `I+(t−1)P` is circulant on fibre coordinates, so its squared entries depend only on `b−a (mod k)`, i.e. the full displacement `j−i=m(b−a)`. In either lateral class every nonzero entry has modulus `s/k`; possible carries in `j−i` are therefore immaterial. All other entries vanish. It follows that `B=|U|²` is circulant, entrywise. Every lateral class has `k` offsets, and its mass is `s²/k`; hence `kM_1=s²∈(0,1)`, contradicting Section 2 for any circulant lift. Taking `(t,s)=(3/5,4/5)` gives fixed algebraic examples in every allowed dimension.

For odd composite `N≥15`, divide by its least prime factor `k`: the cofactor `m≥5` (the only odd composite with larger factor below 5 is 9). No coprimality of the two factors is required. Note that this construction also covers even `N≥10`.

## Reproduction

Run `python3 verify.py` and `python3 verify_extra.py`, then `python3 verify_ortho5.py` in this directory (Python 3 plus SymPy). Finite arithmetic checks are supplementary; the two universal exponents/quantifiers are proved in the text. See `CHECKS.txt` and `CHECKS_EXTRA.txt`. Neither a floating phase search nor a failure to find any particular lift is used as a certificate.
