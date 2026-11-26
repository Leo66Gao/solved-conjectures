# The sharp bounded/unbounded dichotomy for lower natural density

Let u(d) be the larger endpoint of the unique difference d in a perfect set of positive integers.

**Dichotomy.** For a nondecreasing multiplier ω≥1, every perfect difference set has positive lower ordinary density of {d:u(d)>dω(d)} if and only if ω is bounded. More quantitatively, for each fixed C≥1 and every perfect difference set,

    liminf_{X→∞} #{d≤X:u(d)>Cd}/X ≥ 1/(500C).                     (A)

The numerical dependence on C is not claimed sharp. The reverse assertion actually works for every ω tending to infinity, without requiring monotonicity. This is a solution of a *density variant*, not a resolution of Erdős's worst-case rate question.

**Proof of (A).** Write E(X) for the exceptional count. The X−E(X) nonexceptional d≤X have both witnesses in [1,CX]. If their bottom is less than X/100, their top is at most 101X/100. An interval of length L contains at most 1+√(2L) points of A by uniqueness of its positive differences. Hence these pairs number at most (2√(101)/100+o(1))X<X/4 for all large X. Both endpoints of each remaining pair are in I=[X/100,CX]. Partition I into intervals of width h=X/(100C). Every within-cell pair has d<h and top ≥X/100=Ch>Cd; all its differences are distinct, so there are at most E(X) such pairs. The elementary counting lemma in frequency.md, equation (1), gives

    X−E(X) ≤ X/4+(100C+2)(100C²+2+3E(X)).

Hold C fixed and let X→∞. This gives liminf E(X)/X ≥ (3/4)/(300C+7) ≥1/(500C). For bounded ω≤C its exceptional set contains the one for C. The construction below shows the converse.

## A complementary construction: no universal positive lower ordinary density for unbounded multipliers

For every function ω:N→R tending to infinity, some perfect difference set A satisfies

    liminf_{X→∞} (1/X) #{d≤X: u(d)>d ω(d)} = 0.

In particular use ω(d)=log(d+1): for this single A and every c>1, the set {d:u(d)>d^c} has lower ordinary density zero. Combined with the lower logarithmic density theorem for 1<c<2, it exhibits why “upper density” cannot simply be replaced by “lower density” in its ordinary-density consequence. No monotonicity of ω is needed.

**Proof.** Begin with any nonempty finite integer Sidon set P. Denote its maximum by H and the number of its distinct positive differences by D. For integer j≥2 we will preserve P and find a large cutoff X with only O(X/j) possible exceptions. At successive stages increase j.

Choose a sufficiently large prime p, put m=p(p−1), X=⌊m/j⌋, and g a primitive root mod p. In Z/m, identified by CRT with Z/(p−1)×Z/p, put C={(t,g^t): t∈Z/(p−1)}. For a difference (a,b) with a,b nonzero, the smaller-index variable in the ordered representation is uniquely given by g^t=b/(g^a−1) in F_p. Nonzero differences with either coordinate zero are impossible. In particular C is cyclic Sidon and at most X/p+X/(p−1) of the integers d≤X lack a residue representation (these are multiples of p or p−1). Here “smaller-index” just denotes the subtracted endpoint, not numerical ordering in a cyclic group.

Translate the cyclic set by a uniformly random residue and take representatives B in [0,m−1]. For a representable residue d∈[1,X], the unique lifted difference equals d except when the oriented pair crosses the cut; this occurs with probability d/m. Some translation therefore misses at most X/p+X/(p−1)+X(X+1)/(2m) differences in [1,X]. The lifted integer set is Sidon. For each positive difference of P that occurs in B, delete an endpoint of its unique corresponding pair. At most D vertices are deleted (the same already-deleted vertex need not be deleted twice). Each deleted vertex destroys at most 2+2√(2X) positive differences up to X: on each side its partners within X lie in an interval of length X containing ≤1+√(2X) points. Thus the retained B' covers all but at most

    X/p+X/(p−1)+X(X+1)/(2m)+D(2+2√(2X))

of the desired distances. Its internal positive differences are disjoint from P−P. Translate B' by H+m+1. Mixed differences with P are now >m; the internal differences of either constituent are <m if p was chosen with H<m. Two mixed differences cannot coincide by the disjoint internal-difference condition. Thus the union is Sidon and its new endpoints are ≤H+2m≤3m.

For fixed P,j choose p large enough that the preceding error is O(X/j), with an absolute constant, and ω(d)≥6j² whenever d≥X/j. This is possible since ω tends to infinity. For d≥X/j and large p we have dω(d)≥6jX≥3m. Therefore every covered d in [X/j,X] has an endpoint within the required bound; at most O(X/j) among all d≤X remain exceptions.

Finally, to ensure eventual perfection, if the positive integer j is still missing, append a pair {L,L+j} with L greater than three times the current maximum plus j. Its inner difference is new; all mixed differences exceed the old diameter and j and are distinct, since a collision between the two rows would give the old difference j. One can start with P={1,2} to cover d=1. The nested union is a perfect difference set, and previously represented distances keep their endpoints. Choose p increasing fast enough to make the cutoffs increase. The bound O(1/j) along the resulting cutoffs proves the limit inferior is zero. This construction uses the classical CRT exponential finite Sidon set and elementary cutting; priority for the resulting infinite frequency consequence has not been established.
