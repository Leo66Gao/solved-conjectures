# Almost-linear witnesses have logarithmic density zero

Let A be a perfect difference set as before and u(d) the unique larger endpoint. For every real function η(d)→0,

    lim_{X→∞} (1/log X) Σ_{d≤X : u(d)≤d^{1+η(d)}} 1/d = 0.        (A)

In fact for absolute K_0 and 1<c≤6/5 the upper logarithmic density of {d:u(d)≤d^c} is at most K_0(c−1). On the other hand, there is a perfect set for which for *each* fixed c>1 that upper logarithmic density is at least 1−1/c. Thus there is a sharp qualitative exponent-one breakpoint: subpower overhead cannot give positive upper logarithmic density, but every fixed positive power overhead can. In particular, the natural-density construction for d log(d+1) shows that this fast-witness set may have upper ordinary density 1 despite logarithmic density 0. Lower logarithmic density for late witnesses at all powers c<2, including those beyond the useful range of the estimate K_0(c−1), is proved separately in frequency.md.

## Dyadic compression

Work with integers k≥1, B_k=A∩[2^{k−1},2^{k+1}], m_k=|B_k|, and N_k(j) the number of pairs from B_k with positive difference ≤2^j. The interval packing bound gives m_k=O(2^{k/2}). For j≤ℓ, divide B_k's interval into cells of length 2^j with counts n_i; include endpoints in half-open cells as usual. The number of pairs with difference ≤2^ℓ is at most (2^{ℓ−j}+1/2)Σ n_i², by the cross-cell Cauchy argument in frequency.md. Also Σ n_i²=m_k+2Σ binom(n_i,2)≤m_k+2N_k(j). Hence

    N_k(ℓ)/2^ℓ ≤ 2m_k/2^j + 4N_k(j)/2^j.                         (1)

Set D_k=max_{floor(4k/5)≤ℓ≤k+1} N_k(ℓ)/2^ℓ. For all large k, every integer j between 5k/8 and 3k/4 is ≤ every admissible ℓ. For each fixed j, sum (1) over k with 5k/8≤j≤3k/4. Since 4j/3≤k≤8j/5, the sum of m_k/2^j is O(2^{−j/5}) by geometric summation. Further Σ_k N_k(j)≤3·2^j: each positive difference at most 2^j has only one pair, and even a single endpoint belongs to at most three of the B_k. Therefore Σ_k D_k over these k is O(1), uniformly in j. Summing in j up to K, every k≤K occurs ≫k times apart from bounded initial k, giving

    Σ_{k≤K} k D_k = O(K),        Σ_{k≤K} D_k = O(log(2K)).         (2)

The second bound follows by partial summation. Notice (1) is used for every lower scale in a fixed fraction of the logarithmic range, not merely one preceding partition.

## Counting the fast witnesses

First consider pairs with top t∈[2^k,2^{k+1}) and bottom b<2^{k−1}. Their differences are ≥2^{k−1}, so their harmonic mass is at most 2A(2^{k+1})²/2^k, where A(x) counts members up to x. Write b_ℓ=|A∩[2^ℓ,2^{ℓ+1})| for ℓ≥0. For ℓ≥1, binom(b_ℓ,2)≤N_ℓ(ℓ), giving b_ℓ²/2^ℓ≤2D_ℓ+O(2^{−ℓ/2}). A harmless endpoint at 2^{k+1} may be included using the count with < rather than ≤, or adding 1. By weighted Cauchy-Schwarz,

    (Σ_{ℓ≤k} b_ℓ)²/2^k ≪ Σ_{ℓ≤k} 2^{−(k−ℓ)/2} b_ℓ²/2^ℓ.

Summing in k≤K, the geometric weights and (2) show that the harmonic mass of all these pairs is O(log(2K)).

For the remaining pairs the two endpoints are in B_k. If t=u(d)≤d^c, then d≥2^{k/c}. Sort d into bins 2^{ℓ−1}<d≤2^ℓ. Their indices lie between k/c and k+1, up to bounded rounding, so there are at most k(1−1/c)+3. If c≤6/5 then all these indices are admissible in D_k for large k. The harmonic mass in each bin is ≤2N_k(ℓ)/2^ℓ≤2D_k. Thus the total fast-pair mass for top shells k≤K is

    O((c−1)K+log(2K)),

by (2), with an absolute implied constant independent of c. For d≤X and t≤d^c we may take K=ceil(c log_2 X), proving the asserted upper bound for upper logarithmic density. A function η(d)→0 is eventually below every fixed c−1>0. Let c↓1 to obtain (A).

## Sharpness for fixed positive powers

Use the CRT blocks of density-counterpart.md. The following extra observation controls the sums with weight 1/d. For d<m not divisible by p or p−1, a random cyclic cut loses its difference with probability d/m; hence the expected total missing harmonic mass over these d is <1. The residue classes excluded identically contribute O((log m)/p). There is a shift losing ≤2 units of total harmonic weight (or use the sum of two normalized loss functions to ensure both the unweighted estimate in the companion construction and this weighted one up to absolute factors). For clarity, Markov with factor 4 gives each of the two expected-loss failures probability ≤1/4, so a shift satisfying both exists.

At a stage with old prefix P, at most D=binom(|P|,2) vertices are deleted. For a fixed deleted vertex the harmonic weight of lost differences d≥L is O(L^{−1/2}): in each dyadic interval [2^i L,2^{i+1}L) there are O(√(2^i L)) partners, by the elementary Sidon point bound, and their weight is at most 1/(2^i L) each. Choose m at stage j so large that D≤m^{1/j}, in addition to all earlier requirements. As in the companion construction all the translated block's witnesses are ≤3m. For fixed c>1, distances d≥(3m)^{1/c} represented by this block are fast (u(d)≤d^c); the total harmonic weight of missed distances up to m−1 in this range is O(1)+O(D m^{−1/(2c)})=O(1) for large j. The harmonic mass of the entire range is (1−1/c)log m+O_c(1). This yields lower bound 1−1/c for upper logarithmic density, for every fixed c>1 in the same constructed A. The construction remains compatible with the lower-ordinary-density statement for an arbitrary prescribed multiplier tending to infinity by taking the shifts satisfying both loss criteria.

No proof here claims that the lower and upper constants for the logarithmic density at an individual fixed c are optimal.
