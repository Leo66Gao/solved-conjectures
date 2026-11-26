# Which trees maximize the mean size of sets inducing exactly k edges?

Let X be a uniformly chosen vertex subset of an n-vertex tree T having exactly k induced edges, and let a_k(T) denote its expected cardinality. Write S(n,r) for the tree with one hub, r arms of length two, and n−2r−1 arms of length one (n≥2r+1). All isomorphism and uniqueness assertions below are for unlabeled trees.

**Theorem 1 (one edge, all orders).** For every n≥4, S(n,1) maximizes a_1. It is the unique maximizer unless n=6, when S(6,2) ties it. For every n≥5 the unique best tree after S(n,1) is excluded is S(n,2). This proves Conjecture 1 of Dossou-Olory and Andriantiana.

**Theorem 2 (many edges).** Whenever k≥1 and n≥18k+3, the unique first- and second-place trees for a_k are S(n,k) and S(n,k+1), respectively. With U=(n+2k−1)/2, the maximum is within an exponentially small error of U and the runner-up is within an exponentially small error of U−1/3, as quantified below. Every other tree has a_k≤U−1/2. The sufficient linear bound on n is not asserted to be optimal.

## 1. A structural gap

If I is a uniform independent set in a finite graph F with h vertices, put D(F)=h/2−E|I|. Conditioning on the configuration off a vertex leaves at most probability 1/2 of including it. Thus D(F)≥0. On the endpoints of a fixed edge, conditioning off that pair leaves at most two singleton possibilities and one empty possibility. Its expected occupancy is at most 2/3, hence D(F)≥1/3 whenever F contains an edge. If F has at least two edges, then D(F)≥1/2: disjoint edges cost at least 2/3 in total; if two edges meet, condition off their three endpoints. A forest on those endpoints containing the two edges is a three-vertex path. When all vertices remain available its mean independent-set size is 1; if outside selections block any vertex, the remaining at most two vertices also have mean at most 1. The same bound holds if the three endpoints form a triangle. Other vertices contribute at most 1/2 each. For an edgeless graph D=0; for one edge and isolates D=1/3.

Partition the k-edge subsets by the set H of all endpoints of their induced edges. Then T[H] has exactly k edges and no isolated vertices, so h=|H|≤2k. Let B denote the neighbors of H outside H, b=|B|, and F=T−(H∪B). Given H, X is exactly H together with a uniform independent set of F. For n>2k, H is a proper nonempty vertex set and connectivity gives b≥1. Thus the conditional loss below U is exactly

    U − E(|X| | H) = (2k−h+b−1)/2 + D(F).                 (1)

If the first term is positive, it is at least 1/2. If it vanishes, T[H] is k disjoint edges and B is a singleton, say w. Each pair in H is connected to w by exactly one edge, by connectivity and acyclicity. Each component of F attaches to w in exactly one place for the same reason. Hence F is edgeless only when T=S(n,k). If F has precisely one edge, its components are a single pair and isolates, so T=S(n,k+1). Otherwise the two-edge bound gives loss at least 1/2. Taking conditional averages gives the universal trichotomy:

* Every tree with n>2k has a_k≤U.
* If T is not S(n,k), it has a_k≤U−1/3.
* If T is neither S(n,k) nor S(n,k+1), it has a_k≤U−1/2. If n<2k+3, omit the nonexistent second shape.

There are k-edge subsets for every tree when 0≤k≤n−1: successively deleting leaves produces a connected induced subtree on k+1 vertices.

## 2. Attaining the first two levels

Take r=k or k+1, m=n−2r−1, and let w be the hub. Conditional on w being absent, exactly k of the r outer edges have both endpoints chosen. The other r−k pairs are independent, each with three equally likely assignments and expected occupancy 2/3. Thus the number of hub-absent sets is

    A = binom(r,k) 3^(r−k) 2^m,

and their mean cardinality is

    L = 2k + 2(r−k)/3 + m/2 = U − (r−k)/3.

With w present the number is exactly

    C = [x^k] (1+x)^m (2+x+x²)^r.

Indeed a length-one arm adds zero or one edge, and a length-two arm adds 0,0,1,2 edges according to the selected vertices on that arm. Since set sizes lie between 0 and n, a_k≥L−nC/A. Together with (1) this bounds the error in the stated direction. The hub-absent conditions alone also give the displayed L directly.

At x=1/8, positivity of coefficients, A≥2^m, and 2+x+x²<9/4 imply

    n C/A ≤ n (9/4) 18^k (9/16)^m.

For n≥18k+3 we have m≥n−2k−3≥16k and n(9/16)^(n−2k−3) decreases in this range. Consequently the error is at most

    (9/4)(18k+3) [18(9/16)^16]^k < (9/4)(21k)/512^k < 1/6.

These last inequalities follow by integer multiplication and k/512^k≤1/512. Therefore S(n,k) lies strictly above the cap for every nonfirst tree, and S(n,k+1) lies strictly above the cap for all remaining trees. This proves Theorem 2. The unrounded bound n(9/4)18^k(9/16)^(n−2r−1) is exponentially small in n for fixed k, and uniformly exponentially small when n≥18k+3 (split off any excess n−18k−3). The distance between the runner-up and all remaining trees is at least 1/6 minus that error.

## 3. One edge: no asymptotic qualification

Elementary case counting (or equation (3) of the source paper) gives

    a_1(S(n,1)) = [5n−13+(n+1)2^(n−4)]/[2n−5+2^(n−3)].

To check this directly, put m=n−3. For hub absent there are 2^m sets of mean 2+m/2. With hub present, choosing one direct leaf gives 2m sets of mean 5/2 (tip optional); choosing the intermediate vertex gives one set of size 2. The stated rational expression follows. It is above U−1/3=n/2+1/6 for every n≥10: clearing denominators gives 2^(n−2)>P(n)=6n²−43n+73. This holds at 10, and 2P(n)−P(n+1)=6n²−55n+110 is positive for n≥10.

For S(n,2), put m=n−5. With hub absent there are 6·2^m sets of mean n/2+1/6, since one arm supplies the induced edge and the other arm permits three independent configurations. With hub present, choosing a direct leaf gives 4m sets of mean 3; choosing the intermediate vertex of one arm gives 4 sets of mean 5/2. Hence

    a_1(S(n,2)) = n/2 + [2^m−2m²]/[6·2^m+4m+4].

This is strictly above U−1/2=n/2 from n=12 on: 2^m>2m² for m≥7, by induction. Equation (1) now settles all orders n≥12.

The only finite cases needed for both rankings are as follows. The third column counts all maximizers, including S(n,1); the fourth gives the best remaining value after S(n,1) is excluded. That fourth value is achieved by a single tree in each row: S(n,2) for n≥5, and the star for n=4.

| n | number of trees | maximum (multiplicity) | maximum after excluding S(n,1) |
|---|---:|---:|---:|
| 4 | 2 | 12/5 (1) | 2 |
| 5 | 3 | 8/3 (1) | 13/5 |
| 6 | 6 | 3 (2) | 3 |
| 7 | 11 | 86/25 (1) | 61/18 |
| 8 | 23 | 171/43 (1) | 123/32 |
| 9 | 47 | 32/7 (1) | 253/58 |
| 10 | 106 | 57/11 (1) | 59/12 |
| 11 | 235 | 526/91 (1) | 1129/206 |

For a fully reproducible finite proof run `python3 verify.py`, which has no dependencies. Start with the single vertex, append one leaf at each possible vertex, and retain one representative per canonical code. This is exhaustive by deleting a leaf from any tree. A canonical code is the lexicographic minimum over roots of a pair of parentheses containing the sorted list of child codes; equality is equivalent to isomorphism by the standard rooted recursion. For each representative the program tries every vertex subset, tests each edge for joint endpoint inclusion, sums cardinalities, and compares rational numbers exactly. It independently constructs the same isomorphism classes by enumerating multisets of rooted children, then independently recalculates all means by tree dynamic programming. It also checks the general gap inequalities whenever their parameters fit these orders, as well as the coefficient count on a larger parameter grid. The finite table and inequalities prove Theorem 1.

## Sources and scope

* A. A. V. Dossou-Olory and E. O. Andriantiana, [On the average size of 1-nearly independent vertex sets in graphs](https://arxiv.org/html/2510.23670v1), arXiv:2510.23670 (2025), especially Section 4, equation (3), Theorem 14 and Conjecture 1. The source already conditions on the unique edge and computes the value on S(n,1); the positive loss for forbidden residual edges is what identifies the extremizer here.
* E. O. D. Andriantiana and Z. B. Shozi, [The number of 1-nearly independent vertex subsets](https://doi.org/10.2989/16073606.2024.2367714), Quaestiones Mathematicae 47 (2024), 2353–2373; concerns counts rather than average cardinality.
* E. O. D. Andriantiana, V. R. Misanantenaina and S. Wagner, [The average size of independent sets of graphs](https://arxiv.org/abs/1807.08290); this is the k=0 analogue.
* Searches by conjecture title, authors, the terms “average size”, “k-nearly independent”, “inducing exactly k edges”, and candidate-tree names located no independent proof of Conjecture 1, nor the top-two theorem above. The [public problem entry](https://mathdb.com/p/371170/the-extremal-conjecture-for-average-size-of-1-nearly-indepen) also showed no submitted solution when checked. These are priority checks, not a guarantee of priority or peer review. The exact transition for growing k below n=18k+3 is not determined here.
