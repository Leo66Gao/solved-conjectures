# The seven-prime case of Erdős Problem 1100

**Leo Gao** · AI-assisted research · Independent review and priority assessment pending
26 November 2026 · finite computational theorem; not a solution of the growth question

Let g(k) be the maximum number of coprime neighboring pairs in the increasing divisor list of a squarefree positive integer with exactly k prime factors. We find

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| g(k) | 1 | 2 | 4 | 7 | 13 | 22 | 38 |
| Least maximizing integer | 2 | 6 | 30 | 210 | 14,630 | 4,405,245 | 64,908,476,787 |

**Moreover, 64,908,476,787 = 3·7·11·47·113·191·277 is the smallest seven-prime integer attaining 38. Exactly 44 divisor orderings attain it, on labeling the primes in increasing order** (here “attain it” means attaining the maximum count, not the least integer). This is an exhaustive bound for all integers in these finite-factor cases, not a scan up to a numerical cutoff. The order of growth of g(k) is still open. We did not locate an earlier computation of the 7-prime result, but do not claim priority.

## The reduction

Write the k prime logarithms in increasing order. A divisor is a subset A of the primes, its log is the sum w(A) of the corresponding weights, and coprimality of divisors is disjointness. All 2^k weights are distinct. Conversely every order given by strictly increasing positive real weights and strict subset-sum inequalities is realizable by primes: choose a prime between exp(Tw_i) and 2 exp(Tw_i) for each i by Bertrand's postulate (or use a harmless integer rounding), and take T large enough that all the resulting bounded log-errors preserve the given finite list of comparisons. The integer weight certificates in extremizers.json therefore certify genuine divisor orders.

## Exhaustive proof by insertion

The following proof specifies the primary exact verifier, independent.cpp. A k-mask is an integer with k binary digits. Suppose the strictly ordered old masks, for k-1 atoms, are s_0,...,s_(m-1), where m=2^(k-1). The next list is a merge of these masks with their shifted copies m+s_i. Both lists retain their old order. A prefix has emitted x ordinary masks and y shifted ones, and always x>=y, since each ordinary mask precedes its shifted version. The first shifted term follows the largest old singleton because primes are being inserted in increasing order.

1. The entire list is determined by its first m entries: the second half is the reverse of the first, complemented in the full k-set. This follows since complementary weights add to a constant. If x+y=m, the omitted suffixes are exactly the reflected prefixes, as checked from the reverse-complement symmetry of the smaller order.
2. A comparison of old A with shifted m+B is decided by the sign of w(A)-w(B)-w_k. It must give the same answer whenever the signed incidence difference 1_A-1_B is the same. The implementation encodes it by the difference of two sums of distinct powers of three. This encoding of balanced ternary vectors is injective. Whenever the next prefix mask a and its mirror are fixed, record their mutual comparison and their comparisons with already fixed entries on each end. Reject inconsistent signs. Within-layer comparisons are already supplied by the merge. The reflected comparison of two reflected masks is the same signed constraint as the original comparison in reverse order; this is why half of the symmetric checks suffice.
3. Let e(a,b)=[a AND b=0]+[a OR b=full]. Each first-half adjacency contributes e to the score of the complete list; its mirror contributes the second term. The middle pair always contributes exactly 1. For an upper bound at a partial prefix, drop the sign restrictions. A dynamic program, indexed by (x,y,last layer), gives the maximum remaining score: at x+y=m return 1; otherwise maximize e(last,next) plus the value of the state after appending one permitted next term. This is the exact unconstrained merge optimum, thus a rigorous upper bound in the constrained search. Prune only if already-earned score plus the bound is below the threshold. No score pruning is done for levels 1 through 6.

By induction these rules retain every representable order. They may retain infeasible weights, which cannot hurt upper bounds. Starting from [0,1], counts for levels 1,...,6 are 1,1,2,14,546,169444. Their maximum scores are 1,2,4,7,13,22. At seven atoms, threshold 39 leaves no order; threshold 38 leaves 96. The direct prime witnesses in check.py establish equality at every level.

## Second verifier

extend.cpp and extend.hpp take a different route. Through six atoms, traverse the flip graph from the binary order of all masks: consider adjacent disjoint A,B, excluding the empty mask and singleton-versus-singleton swaps. Flip their order and all translations A∪D,B∪D, for D disjoint from A∪B, only if all translated pairs are currently consecutive. This reaches every real-weight chamber: in the open cone 0<w_1<...<w_k, connect two interior witnesses by a generic polygonal line transverse to the finitely many subset-sum hyperplanes and avoiding their codimension-two intersections. Across a crossed wall all tied pairs are precisely the translations of the same disjoint pair, hence adjacent, and these are precisely the swaps performed. Additional nonrealizable orders may be visited.

To extend to seven, this verifier registers comparisons against *all future elements of the opposite layer* rather than processing the reflected prefix; it uses disjoint-mask signed keys rather than balanced ternary. Its upper-bound score recurrence is the same elementary relaxation, coded separately. It finds 703,617 surviving recursive states and zero leaves at threshold 39; 96 leaves at 38. This double implementation is not an independent peer review.

## Classifying the 96 candidates and finding the minimum

For each complete candidate order s, set r_i = 1_(s_{i+1}) - 1_(s_i). Either an integer weight vector w with all r_i·w>0 proves realizability, or a nonzero nonnegative integer vector c with sum_i c_i r_i=0 proves impossibility. The bundled exact certificates give 44 of the former and 52 of the latter. check.py verifies them using integer arithmetic; no numerical optimizer is trusted. classify.py is an optional certificate generator requiring SciPy.

For each of the 44 feasible mask orders, recursively select primes in increasing order. Given a prefix of primes and their products d_A, add a prime q. In the candidate order restricted to these old bits and the new bit, each adjacent comparison crossing the two layers is exactly either d_A<q d_B or d_A>q d_B. These comparisons give the exact allowed open interval for q, because all same-layer comparisons are already correct by induction. Enumerate the primes in this interval. At depth t with prefix product P, further completion is impossible if P q^(7-t) exceeds the incumbent; the search with cap 10^11 finds the stated least integer, then excludes every smaller possibility. At the last prime only the least admissible q need be visited. The standalone min_witness.py implements these strict integer inequalities by division, checks primality by trial division, and uses no numerical solver. The same exhaustive computation using all candidate maximizing orders (feasible or not) for k≤6 gives the other six minima in the table. loworders.cpp differs from independent.cpp by a small output hook, and min_low.py performs the corresponding bounded prime search.

## How to reproduce

Run in this directory with a C++17 compiler and Python 3:

    g++ -O3 -std=c++17 independent.cpp -o /tmp/ep1100-ind
    /tmp/ep1100-ind 39 > /tmp/ep1100-39.out
    /tmp/ep1100-ind 38 > /tmp/ep1100-38.out
    diff /tmp/ep1100-39.out independent39.txt
    diff /tmp/ep1100-38.out independent38.txt
    g++ -O3 -std=c++17 extend.cpp -o /tmp/ep1100-flip
    /tmp/ep1100-flip 6 39
    /tmp/ep1100-flip 6 38
    python3 check.py
    python3 min_witness.py
    g++ -O3 -std=c++17 loworders.cpp -o /tmp/ep1100-low
    /tmp/ep1100-low 1000 > /tmp/ep1100-low.out
    diff /tmp/ep1100-low.out loworders.txt
    python3 min_low.py

The final witness check uses the 128 integer divisors themselves. The upper-bound proof does not use prime sizes, floating-point arithmetic, randomness, or unproved conjectures.

## Sources, scope and remaining obstacle

* [Erdős, 1981, p. 173, (1.6)](https://renyi.hu/~p_erdos/1981-33.pdf) is the original squarefree extremal question. [Erdős and Hall, 1978](https://www.renyi.hu/~p_erdos/1978-26.pdf) is the earlier divisor study. [Problem 1100](https://www.erdosproblems.com/1100) combines this question with two others.
* [Erdős and Tenenbaum, J. Number Theory 31 (1989), 285–311](https://tenenb.perso.math.cnrs.fr/PPP/div-consec.pdf) settles the two other questions in the online statement (yes for almost-all growth relative to the number of prime factors, no for its suggested all-integers upper bound). It yields the squarefree upper exponential base at most 3/2^(2/3).
* In measurement theory the relevant pairs are called **critical**, rather than **flippable**. [Fishburn, Pekeč and Reeds, Math. Oper. Res. (2002)](https://doi.org/10.1287/moor.27.1.227.339) and [Chevyrev, Searles and Slinko](https://arxiv.org/abs/1103.3938) supply context. The latter exhibit F_(k+1) flippable pairs; every such pair is critical, giving g(k)≥F_(k+1) by the prime approximation above. [Christian, Conder and Slinko](https://www.math.auckland.ac.nz/~conder/preprints/FlippablePairs.pdf) study the flip graph and chamber facets; their facet counts are **not** these critical-pair maxima.
* [A current source-linked audit of #1100](https://erdosproblems.ai/wiki/problems/divisors/E1100) records recent Ross and Korsky manuscripts and a refuted quadratic formula. Its linked materials do not give the exponential growth rate. Exact-numerical and terminology searches found no prior source for the 44 maximizing seven-atom orders or the least maximizing integer. A public claim of priority would require a further literature check.
* The small cases do not determine an exponential base. A simple product of weight systems does not multiply the count: lexicographic blocks may share a nonempty old divisor, destroying coprimality. Nor may non-flippable critical pairs be flipped or counted as facets. Any advance from these finite cases to the original question must control such losses or give a tighter upper bound.
