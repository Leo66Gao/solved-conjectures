# Every six-bit postprocessing of the seven-bit witness fails at every crossover

Let X be uniform on the 14-cube, Y=X⊕Z for independent Bernoulli(p) flips, V the particular balanced seven-bit quantizer from [the seven-bit counterexample](https://github.com/Leo66Gao/solved-conjectures/tree/main/15-seven-bit-quantizer), and U any postprocessing of V taking at most 64 values. Then, in nats,

    I(U;Y) < 6[ln 2 − h(p)]                 for 0 < p < 1/2.

At p=1/2 both sides are zero. At p=0 equality is possible, for example by grouping the 128 equiprobable V-labels in pairs. Randomized postprocessing independent of X,Y given V is included: realize it as a random deterministic map selected independently of X,Y, and disclose the independent seed to upper-bound information. There are only finitely many deterministic maps. This theorem does not apply to reshaping or splitting the original input cells. An [independent shorter certificate on p≥2/5](seven-coarsening.md) also quantifies the loss in squared bias.

It suffices to consider exactly 64 nonempty groups of original labels; a coarser deterministic grouping can be refined to this size and information only increases. Their sizes m range from 1 to 65 and sum to 128. Denote by Pᵢ the conditional distribution of Y from the ith original cell. All 128 cells have equal mass.

## An information loss certified with pairs

For any group S of size m≥2, let J(S)=H(Σ_{i∈S} Pᵢ/m)−Σ_{i∈S}H(Pᵢ)/m. This is the information that Y carries about the original label under a uniform prior on S. Write j for a lower bound on every two-label Jensen–Shannon divergence JS(Pᵢ,Pⱼ), and a for an upper bound on every distinct-pair affinity Σ_y√(Pᵢ(y)Pⱼ(y)). Then

    J(S) ≥ max{j, −ln[(1+(m−1)a)/m]}.

For the first bound, average the equally weighted mixtures of all distinct pairs in S and use entropy concavity. For the second, the posterior distribution π of the uniform group label satisfies H(π)≤2ln Σ_i√πᵢ, by Jensen's inequality applied to ln(1/√πᵢ). A second application of Jensen gives E H(π)≤ln E(Σᵢ√πᵢ)²≤ln[1+(m−1)a]. Subtract from ln m.

Define γ as the minimum of m/[2(m−1)] times the displayed lower bound over the integers 2≤m≤65. By the information chain rule,

    I(V;Y)−I(U;Y) = Σ_S (m/128)J(S)
                   ≥ (γ/64) Σ_S (m−1) = γ.

The factor involving m matters at low crossover: large group sizes cannot save the coarsening merely by leaving many singleton labels.

## Verifiable finite calculations for positive crossover

The C++ generator builds exactly the octacode Gray image, shortening/puncturing and lexicographic nearest-codeword cells specified in the paper. It verifies 128 cells of size 128. The set of the 16 translations that preserve the code is found by direct comparison. The nearest-center tie rule is invariant under simultaneous translation, so the original cells have eight translation orbits and the unordered pairs have 568. For each required cell and output word y, the integer distance histogram c_k(y)=#{x in the cell:d(x,y)=k} determines its conditional probability at p=A/B:

    P(y) = [Σ_{k=0}^{14} c_k(y) A^k (B−A)^(14−k)] / [128 B^14].

The full-distribution histograms collapse to 4,324 distinct types, with exact multiplicities over all 128·2¹⁴ pairs (label,y). They give I(V;Y)=Σ_{i,y}Pᵢ(y)ln(2¹⁴ Pᵢ(y))/128. To speed the pair comparisons, lump output words by a low-resolution likelihood-ratio bin computed with integer weights at p=1/4, and by whether y was in either of the two original input cells. Only the *choice of observation partition* uses the anchor 1/4: for each tested p the actual two probabilities in every bin are calculated from that bin's two accumulated distance histograms at p. The exact choice of bins is given in the source and is not a mathematical assumption. Deterministic lumping cannot increase JS (information processing), and cannot decrease affinity (Cauchy–Schwarz). The 568 pair-specific bin lists have 56,355 bins in total and yield conservative j and a at each point.

The Python certificate evaluates rational channel weights exactly. It upper-bounds each affinity term √(xy)/M by (isqrt(R²xy)+1)/(RM), R=2⁵⁴. The standard finite 2·atanh expansion encloses 257 base logarithms at arguments 1+s/256; the remaining geometric tail is bounded explicitly. Every other log first takes out a power of two and the next-lower grid argument. The residual is ln(1+t), 0≤t<1/256; the order-four/order-three alternating bounds, with directed rounding, suffice. More explicitly, round Rt down to integer z, use the cubic evaluated at z/R times R and rounded down, subtract ⌈(z+1)⁴/(4R³)⌉ on its lower side and add two on its upper side. The cubic derivative is at most one on this interval, so this covers the original t and the rounding. Only the printed diagnostics use floating point; acceptance and every endpoint are determined using integers and fractions.

To cover continua rather than single parameters, write ρ=1−2p and c(p)=ln 2−h(p). Binary symmetric channels contract divergence to the uniform cube by the square of their correlation; the elementary proof from the chain rule is in the [shorter certificate](seven-coarsening.md). In particular I(U;Y)/ρ² is nonincreasing as p increases. The positive even series for c(p) shows that c(p)/ρ² is also nonincreasing in p, with limit 1/2. For an interval [u,v] it suffices to compare the upper bound [I(V;Y_u)−γ(u)]/(1−2u)² with a **lower** bound on 6c(v)/(1−2v)². If the former is below 3, the comparison holds to p=1/2 (strict until that endpoint). Exact rational bisection selects a candidate right endpoint and the final strict inequality is checked at that rational. Starting at u=2⁻¹⁵, 17 closed overlapping-at-endpoint intervals cover [2⁻¹⁵,1/2].

## Arbitrarily small noise

If the 64-group partition is unbalanced, its entropy shortfall from 6ln 2 is at least (3ln 3−4ln 2)/128>1/256. Indeed, the integer convex sum Σ m ln m is smallest for all pairs and its next value is achieved by replacing two pairs by a singleton and triple, via the usual transfer of one unit from a larger to a smaller size. For 0≤p≤2⁻¹⁵, 6h(p)≤6·2⁻¹⁵(15ln 2+1)<1/256, so H(U) alone suffices.

Otherwise each group is a pair-cell D of size 256. Direct edge counting over all 8,128 pairs gives at least 2,462 directed edges from D to its complement, hence at least β=2462/256 per point on average. For the noisy conditional law P_D put q_y=256P_D(y)≤1 by double stochasticity. At y outside D, q_y≤14p since returning to D requires a flip starting from y. The probability of leaving via exactly one flip is at least βp(1−p)¹³, and all entropy terms −P_D(y)ln q_y are nonnegative. Thus

    H(P_D)−ln 256 ≥ β p(1−p)¹³ [ln(1/p)−ln 14] > 6h(p)

for 0<p≤2⁻¹⁵. For the strict last bound write t=ln(1/p)≥15ln 2>10. Use β>19/2, (1−p)¹³≥1−13·2⁻¹⁵>999/1000, ln 14<3, and (19/2)(999/1000)(t−3)>6(t+1) for t≥10. Since h(p)≤p(t+1), this proves the claim. Averaging proves the asserted mutual-information bound.

**Reproduce:** in the `coarsening-all` subdirectory run `sh reproduce.sh`. This generates all necessary distance histograms locally from the code definition and certifies the complete interval using C++17 and standard-library Python 3.10+. Expected output appears in `types.log` and `coverage.log`. No external datasets, floating-point inequalities or unverified optimizer claims are needed.
