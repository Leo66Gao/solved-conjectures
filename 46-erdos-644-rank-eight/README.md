# The exact extremal value at uniformity eight

**Leo Gao** · AI-assisted research

Let f(r,7,2) be the largest possible transversal number of an r-uniform hypergraph in which every seven distinct edges have a transversal of size at most two.

**Theorem (computer-assisted): f(8,7,2)=7.** This attains the upper bound at the specific parameter singled out on p. 278 of [Fon-Der-Flaass, Kostochka and Woodall, *Transversals in uniform hypergraphs with property (7,2)*, Discrete Mathematics 207 (1999), 277–284](https://kostochk.web.illinois.edu/docs/2000/dm1999FlaWoo.pdf). It does not resolve the two asymptotic questions in [Erdős #644](https://www.erdosproblems.com/644).

## The construction

Partition 15 vertices as X∪Y with |X|=8 and |Y|=7. Designate one vertex a∈X and one vertex b∈Y. Take all the 8-sets A satisfying

1. |A∩X| is odd; and
2. {a,b} is not a subset of A.

There are 2,352 edges. The 1999 parity construction without the second condition fails at this parameter. Deleting the edges containing one prescribed cross pair is sufficient, while sacrificing no global transversal number.

## Global transversal number

Every 9-set R contains an edge. It meets both parts because each part has at most eight vertices. If R contains both a and b, delete a when |R∩X| is even and b otherwise. If it does not contain both, delete any X-vertex when |R∩X| is even and any Y-vertex otherwise. The resulting 8-set has odd X-intersection and avoids the forbidden pair. The complement of any 6-set is a 9-set, hence no 6-set hits the whole family. Conversely Y is a transversal of size seven since the only 8-set avoiding Y is X and its X-intersection is even. Thus τ=7.

**The ground size is also minimal.** On at most 13 vertices any 8-uniform family admits a transversal of size at most six, by taking the complement of any seven vertices (or the trivial bound when there are fewer than eight vertices). On 14 vertices, transversal number at least seven forces *every* 8-subset to occur, by complementing each 6-set. But doubling each point of the Fano plane and complementing its seven doubled lines gives seven 8-sets on 14 vertices with no two-point transversal: any two points belong to a doubled line, so both miss its complement. Thus 15 is the smallest possible ground size for an extremizer.

## Local two-point transversal property

Here is the finite combinatorial lemma used in the proof. **Given seven 8-sets H₁,…,H₇ on a 15-set with no two-point transversal, either some three distinct indices have Hᵢ△Hⱼ=Hₖ, or every pair of points occurs together in at least one Hᵢ.** Both parts of the disjunction refer to the original 8-sets. The second alternative is not a statement about their complements.

The lemma implies the result: the distinguished pair excludes the second alternative, while parity excludes the first, since the mod-two indicator pairing with X is a linear functional that takes the value one on every selected edge. Its values on two edges add to zero, not one. Thus no seven edges can lack a two-point transversal. The upper bound f(8,7,2)≤7 is Theorem 2 of the cited 1999 paper at r=8. This finishes the proof modulo the explicit finite verification below.

**Independent finite proof of the lemma.** Encode each ground point x by its seven-bit miss spectrum M(x)={i:x∉Hᵢ}. Each label occurs exactly seven times since |Hᵢ|=8, and all spectra pairwise intersect because there is no two-point transversal. A spectrum has size ≥3: if a point misses at most two sets, those two intersect (as 8+8>15), so a second point completes a transversal. Since the sum of all spectrum sizes is 49=3·15+4, the multiset E of spectra larger than triples has excess exactly four. Its size pattern is 7; 6,4; 5,5; 5,4,4; or 4,4,4,4.

The self-contained Python proof `standalone_rank8.py` performs these loops without any data file or external library.

1. List all multisets E of the five size patterns on seven labels. Reduce by the 5,040 permutations of those labels. Nontriples have size ≥4, so any two of them intersect.
2. For each E, allow every triple meeting all of E. If a pair of ground points belongs to no Hᵢ, its two miss spectra have union [7]; at least one of those is in E since two triples cannot have union of size seven. Skip E only when even this preliminary necessary condition fails.
3. The remaining label degrees dᵢ=7−|{S∈E:i∈S}| must be delivered by triples. Choose one positive coordinate j; fill its entire remaining degree by a sorted multiset of allowed triples containing j. All of these automatically intersect in j. Remove all triples through j, all triples disjoint from one just placed, and all triples touching a now-full coordinate. Recurse. This is exhaustive: a feasible completion uniquely specifies the multiset used in this step, and its remaining triples survive every deletion.
4. At zero remaining degrees, whenever two realized spectra have union [7], check that some three-label mask L has |L∩([7]∖S)| even for *every* realized spectrum S. This is precisely Hᵢ△Hⱼ△Hₖ=∅ on those three indices.

On re-run, the checker reports 87,522 exceptional multisets, 86 permutation orbits, 51 orbits requiring recursion and 177 completed regular spectrum configurations checked. Run `python3 standalone_rank8.py` from any directory containing that single file. The machine check is deterministic and uses integers only.

## Scope and priority

The 1999 paper explicitly notes that the uniformity-eight parity example fails, and that reaching its general lower-bound value at m=2 would give equality here. The [July 2026 AI report](https://erdosproblemaday.com/report/644) instead treats rank twelve. Searches for the parameter in two- and three-argument notation, the main paper and later local-to-global work located no prior proof of this rank-eight exact value. This is evidence of potential novelty, not a certificate of priority or peer review. Global asymptotics and even the unrestricted exact value at rank twelve remain separate.
