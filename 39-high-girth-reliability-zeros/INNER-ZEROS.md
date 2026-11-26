# The innermost zeros form an isolated regular polygon

**Theorem.** Fix 0<r<1 and construct the same graphs as in the manuscript with k=d/2 and m−1 nearest to r^(−k). Set s=(m−1)^(−1/k). For constants a,b>0 depending on r, all the k zeros of the polynomial in the disk |z|<s(bd)^(1/k) are simple. Each is within O_r(s exp(−ad)/k) of a different root of z^k=−1/(m−1), and there are no others in the disk. In particular, these are exactly the k innermost zeros; exactly one is real, negative. The next zero has radius at least s[1+(log d+O_r(1))/k].

This is a statement about each individual graph in a single sequence, not about the union of all root sets. The centers form a regular polygon of radius tending to the chosen r. The graph class is the same maximally connected regular, bipartite, unbounded-girth class as in the main theorem.

**Proof.** Choose r<ρ<r^(2/3) and α>0 so that m D_9(z)=O_r(exp(−αd)) uniformly for |z|≤ρ, using Lemma 3 in the PDF. With x=z^k and B=(1+m|x|)exp(m|x|), the estimates of Section 3 give throughout this disk

    |R_G(z)−Q_m(x)| ≤ C_r B exp(−αd).

Indeed |w_1^m−1|≤exp(mD_9)−1, |Q_m|≤B, and (|w_1|+D_9)^m−|w_1|^m≤mD_9 exp(2mD_9). Take b>0 with 6b<α. The circular contour |z|=s(bd)^(1/k) lies inside |z|≤ρ eventually and has (m−1)|x|=bd. There m|x|≤2bd, and

    |Q_m(x)| = |1−x|^(m−1) |1+(m−1)x| ≥ exp(−2bd)(bd−1),

since |x|≤1/2 eventually and log(1−u)≥−2u on 0≤u≤1/2. Thus |R_G−Q_m|<|Q_m| on this contour for sufficiently large d. Rouché's theorem gives exactly k zeros inside, since Q_m(z^k) has its k polygon zeros there and its other zeros lie on |z|=1.

For each exact polygon vertex ζ put z=ζ exp(w/k), |w|≤exp(−αd/2). On that disk (m−1)x=−exp(w) and B=O(1), uniformly in the choice of vertex. On its boundary the explicit formula

    Q_m(z^k)=[1+exp(w)/(m−1)]^(m−1)[1−exp(w)]

has absolute value at least c|w| for a fixed c>0 and all large d. The first factor tends uniformly to e on these shrinking disks; the second satisfies |1−exp(w)|≥|w|/2. Rouché again gives one zero counting multiplicity in each disk; hence these zeros are simple. The exponential maps are injective there and their images are disjoint (adjacent center arguments differ by 2π/k while arguments vary by ≤exp(−αd/2)/k). Each image lies inside the previous contour and every image point has distance O(s exp(−αd/2)/k) from its center. This accounts for all k roots. Since k is odd, the center on the negative real axis is the only real center and its disk is conjugation invariant; all other disks avoid the real line. The claimed modulus bound for the next root uses exp((log d+log b)/k)≥1+(log d+log b)/k. 

**Logarithmic girth strengthening.** We may additionally require girth(G) ≥ (1/300) log_(d−1) |V(G)|. For fixed r put ℓ=log(1/r), ρ=r^(5/6), and, in the LPS construction, choose Q between exp(pℓ/1000) and 2 exp(pℓ/1000). Here log n=(3/1000+o(1))dℓ, rather than o(d), but the only use of log n=o(d) at this prescribed radius was n^5 ρ^(d/32)→0; its logarithm divided by dℓ tends to 15/1000−5/192<0. Thus all estimates for this ρ and all conclusions above hold. The order mn has logarithm (1/2+3/1000+o(1))dℓ, whereas the girth is at least 2log_p Q≥(2/1000+o(1))dℓ/log d. The ratio of girth to log_(d−1)(mn) is at least 2/503+o(1)>1/300 eventually, a constant independent of r. Thus diagonal approximation at the boundary preserves the logarithmic bound as well. No claim of an optimal constant.
