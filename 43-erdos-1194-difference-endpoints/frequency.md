# How often must the witness be late? A partial result for Erdős #1194

## Setting and prior work

Let A be a set of positive integers such that every positive integer d has precisely one representation u(d)−v(d) by two members of A, u(d)>v(d). The function u(d) is the larger **endpoint**, not the d-th member of A. Erdős asks how fast u(d)/d must become large in his [1980 survey, p. 100, eq. (11)](https://www.renyi.hu/~p_erdos/1980-03.pdf#page=12). The [problem register](https://www.erdosproblems.com/1194) and the [formal-conjectures statement](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB1194%C2%BB/) describe an open growth problem, not a known conjecture with a prescribed exact rate. The greedy upper bound is O(d³). An AI-assisted [proof artifact, GPT-5.5 Pro and L. Mazur](https://github.com/lechmazur/erdos_1194), establishes a refined infinitely-often lower bound with leading term d²/(2 log(2) log d), including a log-log correction; its [authors' proof sketch](https://raw.githubusercontent.com/lechmazur/erdos_1194/main/docs/reference/floor_saving_proof_sketch.tex) gives the actual quantifiers. The frequency conclusions below are not asserted by that theorem. Results concerning the counting function of A itself (including the [2026 paper on dense perfect difference sets](https://www.sciencedirect.com/science/article/pii/S0097316526000828)) are a different kind of estimate.

All logarithms below are natural. Write E(y)=|E∩[1,y]|. The following two conclusions concern **the same A at all scales**:

1. **Positive lower logarithmic density at every subquadratic power.** For 1<c<2 and E={d:u(d)>d^c}, there is κ_c>0 such that
   Σ_{d≤Y, d∈E} 1/d ≥ κ_c log Y for all sufficiently large Y.
2. **A lower bound on each multiplicative window at the logarithmic scale.** Fix 0<λ<1/(2 log 2), and put E={d≥3:u(d)>λ d²/log d}. Then
   liminf_{X→∞} Σ_{√X<d≤X, d∈E} 1/d ≥ (1−2λ log 2)/28.
   In particular the sum over d≤Y is ≫_λ log log Y, and limsup E(Y) log Y/Y>0. These are frequency results, not a sharper exponent for the worst case. They do not resolve #1194.

The core device is to charge coarse local overcrowding to specific exceptional differences, rather than discarding an entire sequence when one spacing inequality fails.

## Counting lemma

Suppose points of A in an interval I of length L are partitioned into consecutive half-open cells of width h, with the last cell possibly shortened (endpoints can be handled by one extra cell). Let m_i be their counts, p=Σ_i binom(m_i,2), and H a bound on the differences to be counted. The number of unordered pairs in I with positive difference ≤H is at most

    (ceil(H/h)+1/2) (L/h+2+3p).                                     (1)

Indeed, points from different cells i,j can contribute only for 1≤j−i≤ceil(H/h). For each offset, Σ_i m_i m_{i+k}≤Σ_i m_i² by 2ab≤a²+b²; the within-cell pairs contribute at most (1/2)Σ m_i². Finally m²≤1+3 binom(m,2) for every nonnegative integer m. Whenever I lies above s and the increasing threshold Φ satisfies Φ(h)≤s, each within-cell pair contributes a distinct d<h with u(d)>Φ(d); distinctness follows from the unique representation. We may freely use (X/h+2) in place of the first factor of (1), and use X/h+2≤3X/h when h≤X.

Another elementary bound used below: an interval of length L holds at most 1+√(2L) members of A, since its binomial number of pairs have distinct integer differences ≤L.

## Proof of 1

Choose 1<r<2/c, and let J be the least positive integer with r^J≥c. Fix a small absolute ζ>0, say 10^−4. We account for the X differences 1,...,X for positive integer X. Those whose top exceeds X^c contribute ≤E(X). In what follows, count the rest by their tops; all the estimates work as well for real X with an O(1) rounding error.

**Early tops.** If t≤2X and the bottom is <ζX, the number of such pairs is at most
(1+√(2ζX))(1+√(4X))≤X/4 for sufficiently large X. For all remaining pairs with t≤2X apply (1) to [ζX,2X] at width h_*= (ζX)^(1/c). Since every within-cell pair is exceptional, p≤E(h_*). The volume term (X/h_*+2)(2X/h_*+2)=o(X) because c<2. The remaining term is ≤9X E(h_*)/h_*.

**Late tops.** Set R_j=2X^(r^j) for 0≤j≤J. For tops in [R_j,R_{j+1})∩[1,X^c] and differences ≤X, both points lie in [R_j−X, min(R_{j+1},X^c)]. Its bottom is ≥R_j/2. Use h_j=(R_j/2)^(1/c)=X^(r^j/c)≤X for j<J. Again p≤E(h_j). The volume term divided by X is ≪ R_{j+1}/h_j²+1/h_j=o(1), since r<2/c. There are only J fixed shells. The exceptional contribution is ≤9X E(h_j)/h_j per shell. Consequently, for every sufficiently large real X,

    1/2 ≤ E(X)/X + 9 E(h_*)/h_* + 9 Σ_{j<J} E(h_j)/h_j.          (2)

Every argument on the right is b X^t with fixed 0<t≤1 and fixed 0<b≤1. Integrate (2) against dX/X from a fixed large X_0 to Y. In each term the substitution z=bX^t gives an upper bound t^−1 ∫_1^Y E(z) dz/z² (up to an immaterial constant). Thus this integral is ≫_c log Y. But it is at most Σ_{d≤Y,d∈E}1/d by termwise integration. This proves 1. In particular the exceptions cannot have upper asymptotic density zero. No positive lower ordinary density is asserted.

## Proof of 2

For d≥3 take Φ(d)=λd²/log d and extend to [0,3] positively and nondecreasingly by a constant. Ignoring or including d≤2 never affects a window for large X. On the increasing branch write ψ=Φ^−1. Elementary inversion gives

    ψ(s)² ∼ s log s/(2λ).                                           (3)

Indeed log ψ(s)/log s→1/2 and ψ(s)²=s log ψ(s)/λ. Write M=Φ(X), Y=√X, and W_X=Σ_{Y<d≤X,d∈E}1/d. Among d≤X, at most E(X)≤Y+X W_X+O(1) can have top exceeding M.

We bound the pairs of difference ≤X with top ≤M. Take 0<δ<1, r=1+δ, K>max(3, 3/δ), and 0<ζ<1. Hold these parameters fixed as X→∞.

* For top ≤KX and bottom <ζX, there are at most (2√(ζK)+o(1))X pairs by the elementary interval bound. For the rest of these tops use I_*=[ζX,KX] and h_*=ψ(ζX). Its term without p in (1) is O_{ζ,K,λ}(X/log X)=o(X).
* For late tops use R_j=KX r^j, over j≥0 with R_j≤M. Tops in [R_j,rR_j)∩[1,M] admit the interval I_j=[R_j−X,min(rR_j,M)] of length ≤δR_j+X, and h_j=ψ(R_j−X)≤X. All h used, including h_*, satisfy h≥h_*=ψ(ζX) when X is large.

Let V be the sum of all late-shell terms without p in (1). Expanding (X/h_j+2)((δR_j+X)/h_j+2), its leading term is ≤X(δ+1/K)Σ_j R_j/h_j². The remaining sum is o(X): Σ 1/h_j=O(1/√(X log X)) by geometric decay, Σ R_j/h_j=O(√M/√(log X))=O(X/log X) by geometric growth and log R_j≥log X, and the number of shells is O(log X). By (3), uniformly over R_j≥KX,

    R_j/h_j² ≤ [2λ/(1−1/K)+o(1)]/log R_j.

The elementary decreasing sum / integral comparison gives
Σ_j 1/log R_j ≤ [log(log M/log(KX))]/log r + o(1) = log 2/log r +o(1). Hence

    V/X ≤ (2λ log 2)(δ+1/K)/[(1−1/K)log(1+δ)] +o(1).              (4)

**Charging the error.** From (1) the contribution arising from within-cell pairs in a given interval is ≤9X p/h. All have d<h and top ≥Φ(h), so d∈E. A particular pair is present in at most three of the interval partitions: consecutive late intervals may overlap, but r R_j < R_{j+2}−X since K>3/δ; the early interval counts at most once more. Each exceptional d has only one pair. Those with d≤Y therefore cost ≤27X (Y+O(1))/h_*=o(X), by (3). Those with d>Y cost ≤27X W_X, since h>d whenever they are counted. This use of the harmonic sum, rather than just E(X), is important.

Combining these bounds for all X represented differences gives

    1 ≤ 28 W_X + 2√(ζK) + (2λ log 2)(δ+1/K)/[(1−1/K)log(1+δ)] + o(1).

First let X→∞ with the parameters fixed. Now send ζ→0, then K→∞, then δ↓0. Result 2 follows. Rounding an endpoint or X affects none of the limits.

**Consequences.** Applying 2 on successive disjoint windows (Y^(1/2^{k+1}),Y^(1/2^k)] above a fixed starting scale gives the ≫log log Y sum. If E(y)=o(y/log y), partial summation on (√X,X] would give W_X≤E(X)/X+∫_{√X}^X E(t)dt/t²=o(1), a contradiction. The same counting proof also gives E(X)≫_λ√(X log X) for every large X: bound every p/h charge by 27E(X)/h_*, retain E(X) unweighted for tops >M, and fix parameters in (4) giving a strictly positive deficit.

## Status, audit and limits

This is a direct partial theorem, not a solution or a publication/prior-art priority claim. The novelty search checked the register and discussion thread; the formal Mazur project and proof sketch; Erdős's original; and the Cilleruelo–Nathanson line of results. None of these sources states the frequency conclusions proved here. The proof uses no computation or empirical premise. The crucial limiting coefficient in (4) reproduces 2λ log 2; a fixed dyadic shell ratio instead of taking δ↓0 would not justify the claimed full open range of λ. The truncated final shell matters so that h≤X and no differences greater than X can enter the charge. In 1, only a fixed number of shells can be used because r<2/c; this argument establishes neither positive logarithmic density at c=2 nor an order-n² worst-case lower bound.

A complementary theorem (density-counterpart.md) settles the lower-natural-density variant for nondecreasing multipliers: every perfect set has positive lower density of {d:u(d)>Cd} for each constant C, but already at the threshold d log(d+1) some perfect set has lower density zero, and the same obstruction works for every multiplier tending to infinity. The maintained [machine-readable register](https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml) marked item 1194 open when checked 2026-11-26, independently of whether a public-page snapshot prints a status badge. The [Cilleruelo–Nathanson paper](https://arxiv.org/abs/math/0609244) is a primary older density source.
