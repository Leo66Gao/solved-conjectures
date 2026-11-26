# A sharp spectral analysis of the reflected-layer bound for distinct subset sums
Research note by Leo Gao, developed and checked with AI assistance, 26 November 2026. No independent review. Status: improvement to a specific preprint's quantitative theorem, not the determination of the order of the extremal function; priority unconfirmed.

Let f(n) denote the least possible largest of n positive integers such that their 2^n subset sums are pairwise different. Erdős's historical conjecture f(n) >> 2^n was *already disproved*; see [Adamczewski–Bloom, Appendix B.1](https://arxiv.org/html/2609.25050v1#A2.SS1). Our target was the remaining order of growth, not the historical conjecture. [Dubroff–Fox–Xu](https://doi.org/10.1137/20M1385883) proved the asymptotic lower constant sqrt(2/pi) on the 2^n/sqrt(n) scale; [Costa–Della Fiore](https://arxiv.org/abs/2609.27941) sharpen the finite lower bound. The reflected-layer construction, credited to GPT-6 Astra in Boris Alexeev's repository, gives the smaller maximum f(n) <= ((9/4)^(1/3)+o(1)) 2^n/n^(1/3): [original mathematical write-up, §§2–4](https://github.com/plby/lean-proofs/blob/main/pdf/Erdos1b.pdf), [primary Lean statement](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1b.lean). Those works, rather than this note, supply the graph, modular reduction, and exponent 1/3.

**Result.** For every α>0 write
C(α)=(2α)^(1/3) [1+2 sum_{m>=1} exp(-2 π² α m²)].
Then limsup f(n)n^(1/3)/2^n <= inf_{α>0} C(α) < 0.737. The previous bound in the cited construction is 1.31037..., so this is an improvement to its stated constant, without improving its exponent. The smallest limiting normalized determinant in that particular constant-width, even-layer family is exactly inf C. Numerical optimization gives ≈0.7363036892 at α≈0.13278118; no global optimization of the floating estimate is needed for the <0.737 theorem or asserted. The class obstruction is not a universal lower bound on f.

## Inputs from the known construction
For K>=2, s>=1 take r=2s(K-1)+1. The cited graph (§2) produces a positive odd modulus q and r labels in Z/qZ with all equal-cardinality subset sums distinct (that property is required *separately within each cardinality*). In §3 the exact quantity q/2^r is (Q^s)_00/2, where Q=(I+D)^(-1), with the self-adjoint weighted-path operator
(Dv)_0=v_0-v_1; (Dv)_j=2(2v_j-v_{j-1}-v_{j+1}) for 1<=j<K-1; (Dv)_{K-1}=2(v_{K-1}-v_{K-2}).
The reversible weights are proportional to (2,1,...,1). These are specific prior lemmas used as input, not claims of our contribution.

## Spectral calculation
For 1<=m<K, let θ_m be the unique solution in (0,π) of
(K-1/2)θ + arctan(3tan(θ/2))=mπ.
The left side is continuous, strictly increasing from 0 to Kπ. Put u=tan(θ/2). The vector v_j=cos((K-1/2-j)θ) solves the interior and right-end equations for eigenvalue λ=4(1-cos θ)=8sin²(θ/2), by using the reflected endpoint v_K=v_{K-1}. At the left endpoint, v_0-v_1=λv_0 is exactly tan((K-1/2)θ)=-3tan(θ/2) (v_0 is nonzero at these roots). These K-1 distinct modes together with the constant vector give the full eigenbasis. Their diagonal projector weights at 0 are 2v_0²/(v_0²+sum_j v_j²). Here v_0²=1/(1+9u²), and
sum_{j=0}^{K-1} cos²((j+1/2)θ)=K/2+sin(2Kθ)/(4sin θ).
Expanding sin(2(K-1/2)θ+θ) gives sin(2Kθ)/sin θ=(-2-6u²)/(1+9u²). Thus the weights are 4/[K+1+(9K-3)u²]. The constant mode has weight 2/(K+1). In particular, **exactly**
q/2^r=1/(K+1)+sum_{m=1}^{K-1} 2(1+8sin²(θ_m/2))^(-s)/[K+1+(9K-3)tan²(θ_m/2)].

## Limit, padding, and certificate
For t in (0,π), θ/2<=arctan(3tan(θ/2))<=3θ/2 with θ=t; this follows e.g. by comparing derivatives to 3/2 for the upper bound, and by monotonicity for the lower. Consequently mπ/(K+1)<=θ_m<=mπ/K. Along s/K²→α in (0,∞), for fixed m one has Kθ_m→mπ and s log(1+8sin²(θ_m/2))→2απ²m². To interchange limit and series, note log(1+x)>=x log(9)/8 for 0<=x<=8 and sin(θ/2)>=θ/π. After multiplication by K, each summand is bounded by 2 exp(-c(α) m²) once K is sufficiently large. Hence Kq/2^r→1+2 sum_{m>=1} exp(-2απ²m²). Since r~2αK³, r^(1/3)q/2^r→C(α).

For each large K take s=ceil(αK²) and t=2ceil(log₂ r), n_K=r+t. Represent the modular labels by c in [0,q). Add the t terms 2^i q, i<t, and use shifted labels (2^t+r)q+c. A signed relation first forces the signed number of shifted labels to be 0, since all other terms in absolute value total <(2^t+r)q. Modulo q the cardinality condition forces each signed label coefficient to vanish; the powers of two then rule out any nonzero relation. Thus max(A)/2^{n_K} lies between q/2^r and (1+(r+1)/2^t)q/2^r. For n_K<=n<n_{K+1}, repeatedly replace A by {1} union 2A, preserving the normalized maximum. Since n_{K+1}/n_K→1 and n_K/r→1, this gives the asserted global limsup for each α.

For a rational bound fix α=2/15. With π>3.1415, the Taylor polynomial through degree 11 for e^{4(3.1415)^2/15} exceeds 1/(0.072), by rational arithmetic. Thus x=e^{-4π²/15}<0.072, and sum_{m>=1} x^{m²}<=x+x^4/(1-x^5). Cubing the resulting upper bound for C gives (4/15)[1+2(0.072+0.072^4/(1-0.072^5))]^3 < (737/1000)^3. See verify.py.

## Sharpness for this family
If r→∞ and K stays bounded, the constant spectral mode alone gives r^(1/3)q/2^r→∞. For K→∞ and s/K²→∞ the same lower bound gives divergence. If K→∞ and s/K²→0, put M=floor(K/(4sqrt(s+1))). Then M→∞. For 1<=m<=M, θ_m<=π/(4sqrt(s+1)), so tan²(θ_m/2)<=tan²(π/8), and (1+8sin²(θ_m/2))^(-s)>=exp(-2s θ_m²)>=exp(-π²/8). Each term in the exact formula is bounded below by an absolute positive constant divided by K. Thus q/2^r >> 1/sqrt(s+1), and r^(1/3)/sqrt(s+1) >> (K²/s)^(1/6)→∞. Any bounded normalized subsequence has after extraction s/K²→α in (0,∞), where its limit must be C(α). Conversely each C(α) occurs. This proves the sharp infimum for the modular normalized determinant and for the stated asymptotically lossless padding. It does NOT cover other graphs, other modular labels, better ways to load a group, or give a matching lower bound for arbitrary dissociated sets.

## Verification, scope, and attribution
verify.py directly constructs the rational transition matrix from the previous paper and compares 52 direct exact return probabilities with the spectral formula evaluated numerically (agreement <1e-11). On the included cases with r<=10 it also reconstructs the integer determinant and enumerates all subsets by cardinality modulo q. The decimal 0.737 bound has a separate all-rational test; finite checks serve as diagnostics, not a proof of the limit. No external review or new Lean formalization. Comparison is to the exact constants located in the cited primary sources, not a comprehensive priority claim. Reproduction: python verify.py (Python 3, NumPy, SciPy, SymPy).

The change from a Green-function bound to a full path spectral decomposition does not close the exponent gap. Non-constant-width or differently connected graphs are not precluded. No new sharp-order theorem is claimed.
