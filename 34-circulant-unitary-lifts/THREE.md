# The order-nine gap: an extremal trimer and a cubic twist

For every `k≥2`, set `N=3k`. The circulant stochastic matrix with displacement probabilities
```
p_0=4/9,     p_{3j+1}=4/(9k),     p_{3j−1}=1/(9k),
p_{3j}=0 for j≠0 mod k
```
is unistochastic but has no circulant unitary lift. In particular this covers `N=9`, the odd composite missing from the short-band argument. Its first row, multiplied by 27, is `(12,4,1,0,4,1,0,4,1)`.

**Existence.** Set `a=b=2/3` and `c=1/3`. The real circulant `3×3` matrix `H` with displacement coefficients `(a,b,−c)` is orthogonal: `a²+b²+c²=1` and `ab−ac−bc=0`. Take three mutually unbiased orthonormal bases of the fibre `C^k`, i.e. unitary matrices `G_0,G_1,G_2` whose relative change-of-basis matrices `G_r* G_l` for `r≠l` have entries of modulus `1/√k`. Such a triple exists for all `k`: take `G_0=I,G_1=F,G_2=DF` with the normalized Fourier matrix `F`, and diagonal `D` having entries
```
D_jj = exp(π i j(j+e)/k),   e=0 for even k,   e=1 for odd k.
```
The sequence is periodic since `k+e` is even; its cyclic autocorrelation at every nonzero shift `h` is a constant phase times `Σ_j exp(2π i hj/k)=0`. Thus its discrete Fourier transform has all moduli `√k`, proving the property for `F* D F`.

Write each state as `i=3u+r` with `0≤u<k`, `0≤r<3`. Form the unitary with `(r,l)` fibre block `H_rl G_r*G_l`; it is a block-diagonal unitary conjugate of `H⊗I_k` after grouping states by residue. Diagonal blocks are `a I`, all displacements `1 mod 3` have modulus `b/√k`, and all displacements `−1 mod 3` have modulus `c/√k`. Thus the squared entries are exactly the displayed probabilities, even on wraps.

**Rigidity for a putative circulant lift.** Normalize its coefficient at displacement 0 to `a>0` by a common phase. Let `u_j` be its coefficients and put
```
X(w)=Σ_{j=0}^{k−1}u_{1+3j}w^j,    Y(w)=Σ_{j=0}^{k−1}u_{−1+3j}w^j.
```
At each `k`th root of unity `w`, choose a unit cube root `z` with `z³=w`; let `x=zX(w), y=z^{-1}Y(w)`. The three corresponding Fourier eigenvalues are `a+ω^h x+ω^{-h} y`, `h=0,1,2`, `ω=exp(2πi/3)`. All moduli are 1, and Fourier inversion in `h` gives
```
a²+|x|²+|y|²=1,       ax+a conjugate(y)+y conjugate(x)=0.
```
So `a|x|≤(a+|x|)|y|`, i.e. `|y|≥a|x|/(a+|x|)`. The right side strictly increases in `|x|` while `sqrt(1−a²−|x|²)` decreases, and equality holds at `(|x|,|y|)=(b,c)`. Hence `|x|≤b`. Parseval gives `(1/k)Σ_w |X(w)|²=Σ_j |u_{1+3j}|²=b²`. Thus every `|x|=b, |y|=c` and equality holds in the triangle inequality. The directions of `a conjugate(y)` and `y conjugate(x)` must both be opposite to `ax`. With `x=b exp(iα), y=c exp(iβ)`, this reads `−β≡α+π` and `β−α≡α+π (mod 2π)`. In particular `3α≡0`. Therefore
```
X(w)^3=b³ w^{-1}   for every w^k=1.
```

**Flat cubic roots are impossible.** Set `η_r=X(exp(2πir/k))/b`. This unimodular sequence has a flat inverse Fourier transform (all original coefficients `u_{1+3j}/b` have modulus `1/√k`), so its cyclic autocorrelation at lag 1 vanishes, `Σ_r η_{r+1}conjugate(η_r)=0`; here `k≥2` is essential. Each
```
λ_r=exp(2πi/(3k)) η_{r+1}conjugate(η_r)
```
is a cube root of unity by the preceding cube identity, including for `r=k−1` with cyclic indexing. They sum to zero. Since `1,ω,ω²` have the unique rational dependence proportional to `1+ω+ω²=0`, they occur equally often. Their product is therefore `1`. But the product of the ratios telescopes, so `Π λ_r=exp(2πi/3)≠1`, a contradiction.

This proof uses a sharp Fourier-mode inequality, not numerical nonconvergence. Order 3 itself (k=1) has a circulant lift H, correctly excluded by the nonzero-lag step.
