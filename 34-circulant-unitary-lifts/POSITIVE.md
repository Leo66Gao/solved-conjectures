# Strictly positive rational counterexamples, with a quantitative gap

For `N=2k≥6`, put `δ=1/(20k)`. There is no circulant lift of the **strictly positive** circulant unistochastic matrix given by
```
p_{2s+1}=1/(2k)  (all s);
p_{2s}=δ²/(2k²)  (s not ≡0 mod k);
p_0=1/2−(k−1)δ²/(2k²).
```
At order 6 the first row multiplied by 64800 is `(32398,10800,1,10800,1,10800)`.

**Unistochasticity.** Let `a=b=1/√2`. Choose a unit scalar `z` with `|z−1|=δ` and the unitary circulant `V=I+(z−1)J/k`, where `J` is all ones. In the parity-ordered block lift from Section 1 of RESULT.md, left multiply by `diag(V,V)`. The diagonal blocks become `aV`; the off blocks `bVF` and `−bVF*` still have every modulus `b/√k`, because the columns of both Fourier matrices consist of eigenvectors of the circulant V. This gives the stated probabilities (the diagonal value also follows by the unit row sum).

**Quantitative obstruction.** Suppose `c_j` is a circulant lift, normalized to make `c_0>0`. Write `ξ=exp(2πi/(2k))` and split its Fourier eigenvalues into the normalized even- and odd-offset sums
```
A_r=(1/a) Σ_{j even} c_j ξ^{rj},     B_r=(1/a) Σ_{j odd} c_j ξ^{rj}.
```
Then `A_{r+k}=A_r, B_{r+k}=−B_r`, and both `a(A_r+B_r)` and `a(A_r−B_r)` have modulus one. Hence `|A_r|²+|B_r|²=2` and `Re(A_r conjugate(B_r))=0`. The formula for V gives `|c_0/a−1|=||1+(z−1)/k|−1|≤δ/k`. Every other even coefficient has modulus `aδ/k`. Thus `|A_r−1|≤δ`, and
```
||B_r|−1|≤||B_r|²−1|=||A_r|²−1|≤(2+δ)δ,
| A_r/|A_r|−1 |≤2δ.
```
Neither `A_r` nor `B_r` vanishes since `δ≤1/60`. By their real orthogonality there are signs `e_r` with `B_r=i e_r |B_r| A_r/|A_r|`, and `e_{r+k}=−e_r`. It follows that `|B_r−i e_r|≤(4+δ)δ≤5δ`, and `|B_r|≤1+3δ`.

Since the original odd coefficients are all flat, `Σ_{r=0}^{2k−1}B_{r+h} conjugate(B_r)=0` for `1≤h<k`, by Fourier orthogonality and the sum of `ξ^{hj}` over odd `j`. The summands are k-periodic, so the sum over just `r=0,…,k−1` also vanishes. Comparing termwise with the sign sequence then gives, for the negacyclic correlation,
```
|Σ_{r=0}^{k−1}e_{r+h} e_r|≤k·5δ(2+3δ)<1.
```
The last inequality uses `δ=1/(20k)`, `k≥3`. These are integers, so both lag 1 and lag 2 correlations vanish. The exact sign-parity contradiction in Section 1 of RESULT.md rules this out.

This estimates a neighborhood within the displayed one-parameter family; it does not assert the same bound for arbitrary perturbations of all entries.
