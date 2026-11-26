# Two copies control every moment of a bounded channel product

Research note, 26 November 2026. Finite-dimensional complex quantum systems only. The claims below are proved here, not just observed numerically. Bibliographic originality is a separate question; see priority.md.

## 1. Spectral stabilization for arbitrary channel ensembles

Let Φ be drawn from any probability law on completely positive trace-preserving (CPTP) endomorphisms of the d-by-d matrices, d≥2. Independently resample this law at each step, but use the **same** realization on every copy within one step. Set T_n=E[Φ^{⊗n}]. Define s(T_n) as the largest modulus among eigenvalues after deleting *one occurrence* of 1, counting algebraic multiplicity.

**Theorem 1.** s(T_n)=s(T_2) for every n≥2. More explicitly, write A for the restriction of Φ to traceless Hermitian matrices in a fixed Hilbert–Schmidt orthonormal basis, and B_r=E[A^{⊗r}]. Then

    s(T_n) = max{ρ(B_1),ρ(B_2)}                 (n≥2).

Here ρ is spectral radius. In particular, two-copy contractivity in the sense of Wallman–Flammia is equivalent to n-copy contractivity at every higher order.

**Proof.** The real space of Hermitian matrices complexifies to the full matrix space. In trace-adapted coordinates a channel is block triangular, [[1,0],[b,A]], without any unitality requirement. Split the n-fold tensor product into 2^n summands according to which factors are traceless and which are scalar. A factor already traceless stays so. Ordering by support size therefore triangularizes T_n, with one diagonal block B_|S| for each subset S of [n]; the empty block is [1]. This is a characteristic-polynomial factorization, so it does not require diagonalizability.

Let P_m=A_m⋯A_1 for independent draws. E[P_m^{⊗r}]=B_r^m. Every product Φ_m⋯Φ_1 is positive and trace preserving. On Hermitian matrices its trace norm operator bound is 1 by Jordan decomposition and the triangle inequality. Thus the induced Hilbert–Schmidt norm of P_m is at most √d, since ||X||_2≤||X||_1≤√d||X||_2. This bound is uniform in m, **not** (√d)^m. Real and complex Euclidean operator norms coincide for a real matrix.

Let v=vec(I_h), h=d²−1. Then

    E||P_m||_F² = v^T B_2^m v.

Indeed the right side averages the sum of the squares of all real matrix entries of P_m. For r≥2,

    ||B_r^m|| ≤ E||P_m||^r
        ≤ d^{(r−2)/2} E||P_m||_F²
        ≤ d^{(r−2)/2} h ||B_2^m||.

Take m-th roots and use the spectral radius formula. This gives ρ(B_r)≤ρ(B_2) for all r≥2, including when the latter vanishes. Since both first- and second-order blocks actually occur for n≥2 the claimed maximum is attained. □

The proof also holds for random positive trace-preserving maps, even though their tensor powers need not be positive. In abstract form it only requires affine linear maps whose linear parts generate a bounded semigroup. This is an annealed spectral radius; it does not assert a bound on one-step singular values or finite-time norms independent of n.

## 2. Fixed noise conjugated by any exact unitary 2-design

Let Λ be a fixed CPTP endomorphism and A its traceless block. Let Φ=Ad_U ◦ Λ ◦ Ad_{U†}, where the probability law of U is any exact unitary 2-design (including Haar; no group assumption). Write h=d²−1,

    p=Tr A/h,                    u=||A||_F²/h.

**Theorem 2.** For n≥2, s(T_n)=max(|p|,u). If Λ is nonunitary this is strictly below one. For unitary Λ it equals one at every n≥2.

**Proof.** Conjugation on the traceless Hermitian space is represented by real orthogonal R(U); a draw has linear block C=R A R^T. Haar conjugation averages any real supermatrix M on that space to (Tr M/h)I. This follows from Schur's lemma since the complex traceless conjugation representation is irreducible (its invariant subspaces are Lie ideals in the simple algebra sl_d). The same identity holds under the 2-design: the entries of R M R^T have bidegree (2,2) in U and its conjugate. Thus E C=pI and E CC^T=E C^T C=uI.

Under vectorization B_2 represents X↦E[C X C^T], and B_2 v=u v. Iterating the identity for E C^T C gives E||P_m||_F²=h u^m. The estimate of Theorem 1 yields ρ(B_2)≤u; equality follows from the eigenvector. Cauchy–Schwarz gives |p|≤√u.

For completeness, in an orthonormal Hermitian basis ||Λ||_F²=1+||b||²+||A||_F². Reshuffling the unnormalized Choi matrix J into the superoperator does not change its Frobenius norm. J≥0 and Tr J=d, so ||Λ||_F²=Tr J²≤d². Equality requires rank one, i.e. a single Kraus operator K with K†K=I, hence a unitary. Therefore u≤1 with equality exactly for unitary channels (the unitary case has b=0 and A orthogonal). □

This is strictly a statement about eigenvalue moduli; it does not assert the fixed state is maximally mixed.

## 3. Haar–Stinespring interactions: exact equilibrium and sharp L² rate

Fix system dimension d≥2 and environment dimension e≥2. A step draws a Haar isometry V:C^d→C^d⊗C^e and updates the density matrix by Φ_V(ρ)=Tr_E(VρV†). Use a fresh isometry at each step. Let π denote the law of G†G/Tr(G†G) for a de-by-d standard complex Ginibre matrix G (normalized induced Wishart law with parameters d,de). Let K act on functions by Kf(ρ)=E f(Φ_V(ρ)).

**Theorem 3.** π is stationary and the chain is reversible. Its absolute L²(π) spectral gap is

    1−q,                 q=e(d²−1)/(d²e²−1).

The norm of K on mean-zero L²(π) equals q; centered purity attains it. In particular all nonconstant square-integrable observables decorrelate at most as q^m in m steps in stationarity. All T_n, n≥2, have subdominant modulus exactly q as well.

**Stationarity and reversibility.** In the polar decomposition G=V(G†G)^(1/2) the isometry is Haar and independent of G†G, by left-unitary invariance of the Gaussian. Partition G vertically, by the environment index, into e matrices G_a of size d-by-d. With c=Σ_a Tr(G_a†G_a), a stationary transition candidate is the explicit pair

    X=Σ_a G_a†G_a/c,         Y=Σ_a G_a G_a†/c.

The polar decomposition gives Y=Φ_V(X). Replacing all G_a by G_a† preserves their joint law and exchanges X and Y exactly. Hence π is stationary and K is self-adjoint on L²(π). This is an exact finite-dimension identity, not only a Marchenko–Pastur limit.

**A two-copy computation.** For Hermitian X (not assumed traceless), embed X into dimension N=de by an isometry, zero elsewhere. Write z=Tr X, w=Tr X². The Haar average of the tensor square of the unitary conjugate of this embedded matrix lies in span{I,F_N} by the two-copy Haar commutant. Taking its traces against I and swap F_N gives coefficients α=(z²−w/N)/(N²−1), β=(w−z²/N)/(N²−1). The swap trick and the two partial traces give

    E Tr[Φ_V(X)²] = α d e² + β d² e
                    = a z² + q w,
    a=d(e²−1)/(d²e²−1),   q=e(d²−1)/(d²e²−1).

Thus E A^T A=qI_h by polarization on traceless inputs. E A=0 by output-unitary invariance, and E A A^T=qI_h by isotropy and trace. As in Theorem 2, ρ(B_2)=q. By Theorem 1 all s(T_n)=q for n≥2. For a density matrix, K(Tr ρ²)=a+q Tr ρ², so Tr ρ²−a/(1−q) is a nonzero eigenfunction (π has full support). Its subtracted mean equals d(e+1)/(d²e+1).

**All L² observables.** Each polynomial of degree ≤n in the real coordinates of ρ is a linear combination of functions f_H(ρ)=⟨H,ρ^{⊗n}⟩, homogenizing with Tr ρ=1. The map H↦f_H intertwines T_n^* with K, so the restriction to this finite-dimensional polynomial space is a quotient of T_n^*. Since q<1, the constant eigenvalue is simple and all others have modulus at most q. K is self-adjoint in the stationary inner product: this spectral bound is also an operator norm bound on every centered polynomial. These polynomials form a dense subspace of centered L²(π), by Stone–Weierstrass on the compact density-matrix set and density of continuous functions. The bound extends to all centered functions; centered purity shows equality. Uniqueness of the stationary law among all probability measures follows separately: for any initial law the polynomial moments converge to the π-moments (simple eigenvalue, strict gap), and on a compact set these determine weak convergence. □

**Scope.** This is the gap of the random *update kernel on density matrices*, not the spectral gap of one channel sampled once and held fixed; also not a dimension-free total-variation mixing-time estimate. The explicit induced equilibrium supplies every limiting tensor moment:

    E_π[ρ^{⊗n}] = [Σ_{σ∈S_n} (de)^{#cycles(σ)} F_σ] / [(d²e)(d²e+1)⋯(d²e+n−1)],

by taking a partial trace of the Haar pure-state n-copy average on C^d⊗C^{de}. For fixed n, T_n^m(X) converges to Tr(X) E_π[ρ^{⊗n}]. The stationary state law and the kernel on density matrices are different from the stationary n-copy density matrix, which is the corresponding moment.

## 4. A pure-state random circuit with a sharp gap at every order

Let a pure state on C^d_A⊗C^e_E⊗C^d_B be updated by an independent Haar gate on AE or EB, chosen with probability 1/2 each. On the entire space L² of the Haar **projective-state** distribution, the Markov operator has absolute spectral gap (1−q)/2, with the same q as above. For three qubits the gap is 3/10. This is not a gap on the full unitary group.

Indeed, twirling EB is the orthogonal projection onto the functions of the marginal ρ_A, and twirling AE projects onto those of ρ_B. To see this, purifications with the same marginal form a single orbit of the unitary group on the purifying factor, whose Haar measure is the conditional uniform law on that orbit. In a Gaussian realization of a Haar pure vector, (ρ_A,ρ_B) has the same law as (X^T,Y) up to labeling from Theorem 3. The transpose does not alter the space of functions, and purity is invariant under it. The exact norm of conditional expectation between the two mean-zero function spaces therefore equals q by Theorem 3. Equivalently the largest possible Pearson correlation between arbitrary real square-integrable functions of those two marginals equals q, attained by their purities.

Let J_A and J_B embed the marginal mean-zero spaces into the joint space by pullback, and L=[J_A,J_B]. Twice the random-gate Markov operator on the centered space is LL*, whose norm is ||L*L||. The latter has identity diagonal blocks and off-diagonal blocks equal to a conditional expectation operator and its adjoint, of norm q. Hence ||L*L||≤1+q. Equality follows by using the same unit-variance centered purity in the two marginal slots: the Rayleigh quotient is 1+q. Positivity makes the ordinary and absolute gaps coincide. Since purity is degree two in the pure-state projector, the spectral endpoint occurs in every (homogenized) projective-state moment of order at least two. No assertion is made here for unitary designs, larger chains, or diamond-norm error.

**Many sites, larger gates.** More generally take N≥3 equal local dimensions d and, at each step, leave one uniformly chosen site untouched while Haar-randomizing the other N−1 jointly. Its stationary Haar projective-state L² spectral gap is exactly

    1−[1+(N−1)q_N]/N,    q_N=d^{N−2}(d²−1)/(d^{2N−2}−1).

Each gate average is the pullback projection for the marginal at the untouched site. Each pair of distinct marginals is exactly the tripartite model with environment dimension e=d^{N−2}. Writing L=[J_1,...,J_N], for vectors f_i in the centered marginal spaces the quadratic form of L*L is bounded by Σ_i||f_i||²+q_N Σ_{i≠j}||f_i|| ||f_j|| ≤ [1+(N−1)q_N] Σ_i||f_i||². Taking the same standardized centered purity in every slot attains equality. This is an (N−1)-site-gate model; for N>3 it is not a two-local circuit.

## 5. Unequal dimensions: maximal correlation of two Haar marginals

For a Haar pure state on C^a⊗C^e⊗C^b, let ρ_A,ρ_B be the outside marginals and assume a,b,e≥2. Define q_j=e(j²−1)/(e²j²−1). Then

    sup_{f,g} Corr(f(ρ_A),g(ρ_B)) = √(q_a q_b),

where the supremum is over square-integrable nonconstant real functions, and it is attained by the two centered, standardized purities. There is **no restriction on relative dimensions**. In particular the exact pure-state gap of the two-edge random-gate chain in §4 with unequal end dimensions is (1−√(q_a q_b))/2.

**Proof.** Relabel the ends so b≤a. Conditional expectation of observables of A given B, followed by conditional expectation in the reverse direction, determines a two-step B→A→B Markov kernel. As an operator on B-functions this is D*D for the conditional-expectation operator D from B-functions to A-functions. It is self-adjoint and its norm on the centered space is the square of the maximal correlation in question.

It suffices to compute the two-step kernel up to unitary conjugations/transposes of the input, on which it does not depend. To condition on ρ_B, flatten a normalized Ginibre vector into an ae-by-b matrix. Its polar factor is an independent Haar isometry V:b→a⊗e. With V stacked from e matrices K_j of shape a-by-b, the conditional distribution of ρ_A is the channel output Σ K_j ρ_B K_j†. The physical marginal convention can transpose ρ_B; this does not affect the distribution because V is right-unitarily invariant and ρ_B and its transpose have the same spectrum. In the reverse direction, fixing ρ_A fixes its nonzero eigenvalues on the be-dimensional purifying space; the conditional state on that space is a Haar conjugate of that spectrum padded by zeros. Tracing out E then gives ρ_B'. This holds also when a>be and ρ_A is rank deficient.

The subtlety when a>be is to realize this round trip by a probability law on **linear channels**, not a nonlinear eigenvalue update. Set W=[K_1 ⋯ K_e], a by be, and S=W†W. Then Tr_E S=I_b. Define J_V(X)=S^(1/2)(I_e⊗X)S^(1/2). This is CPTP from b to be: complete positivity is immediate and the trace identity follows from Tr_E S=I_b. When X≥0, J_V(X) has the same nonzero eigenvalues (with multiplicities) as W(I_e⊗X)W†=Σ K_j X K_j†. To see this, successively exchange the two factors of M†M and MM† for M=(I_e⊗√X)S^(1/2) and M=W(I_e⊗√X). Consequently the desired two-step kernel is realized by an independent Haar U∈U(be) and the random CPTP endomorphism

    Γ(X)=Tr_E[ U J_V(X) U† ].

For Hermitian X, including traceless indefinite X, cyclicity gives Tr[J_V(X)²]=Tr[(Σ K_j X K_j†)²]. The two-copy calculation in §3 applies to target dimension a with environment e (the input is embedded by the isometry V, so its dimension need not equal a). For traceless Hermitian X, it gives E||J_V(X)||²_HS=q_a ||X||²_HS. Applying the same Haar calculation to traceless J_V(X) in dimension be yields E||Γ(X)||²_HS=q_b q_a ||X||²_HS. Its mean traceless block is zero by the final output Haar invariance, and its averaged output Gram is scalar by the same invariance. Theorems 1 and the proof of 2 now bound every nonconstant polynomial eigenvalue of the two-step state kernel by q_a q_b in modulus. Polynomial density and self-adjointness extend the bound to all centered L² functions as in §3. Each one-way kernel sends centered purity to the other centered purity times the target's q; hence D*D attains q_a q_b on centered purity. After standardization the one-step correlation is its positive square root. □
