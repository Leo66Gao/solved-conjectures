# Twelve inputs: no six-bit counterexample from translating one cell at high noise

Let X be uniform on the Boolean 12-cube and let Y be its independent binary symmetric channel output, with crossover p, correlation ρ=1−2p, and C(p)=1−h₂(p) in bits. Suppose the nonempty cells of a quantizer are the 64 translates A+c of a single 64-point set A that partition the cube. The set of centers is **not assumed linear**. Put B(A)=Σᵢ(E[(-1)^Xi | X∈A])².

**Theorem.** B(A)≤6, with equality precisely for a coordinate six-face. Consequently I(f(X);Y)≤6C(p) throughout 0≤ρ≤1/512, and equality at nonzero ρ in this interval requires a coordinate six-face. The cell bias statistic of a translational partition equals B(A), since translation changes only the signs of its coordinate biases.

This rules out all one-template translational schemes in this dimension in an explicit interval, generalizing the previous obstruction for one particular 64-point cell. It does **not** rule out partitions mixing different shapes or independent coordinate permutations, the rest of the crossover range, or other dimensions.

## Rigidity before compression

Let s(A)ᵢ=Σ_{x∈A} (−1)^xᵢ and H(A)=||s(A)||². Translate A and permute coordinates so its signs are nonnegative and in nondecreasing order. Take A* to be the 64 points with the smallest weighted coordinate sum Σᵢ s(A)ᵢ xᵢ, breaking ties by smaller binary encoding (bit 0 is the lowest). It is closed under coordinate deletion and replacement of a present coordinate by a smaller absent coordinate. We call such families shifted. By linear maximization, s(A)·(s(A*)−s(A))≥0, whence

    ||s(A*)−s(A)||² ≤ H(A*)−H(A).

There are 1,027,170 shifted 64-point families on 12 coordinates in the included exhaustive enumeration. The maximum H is 24,672. Of the 19 with H≥6·64²=24,576, exactly one is the six-face; the other 18 contain 0, all 12 units, 51 pairs and no heavier words, with all sᵢ≥40. Thus for any qualifying A, if A* is the face, the displayed inequality forces s(A)=s(A*), and A itself is a face. Otherwise all s(A)ᵢ≥40−√96>30. If any nonempty downward edge of A failed closure, moving its upper word to the missing lower one would increase H by 4s(A)ᵢ+4>96, contradicting the universal maximum. Hence A itself is a downset.

Shift the downset by repeatedly sorting under adjacent coordinate swaps: if only the less-preferred member of a swapped pair of vertices is present, replace it by the preferred one. These operations preserve the number of words of each Hamming weight and preserve downsets. For example, replacing bit j by i in each eligible member of an inclusion ideal preserves closure because any deletion is either the identical-coordinate deletion on a smaller original word or removes the moved coordinate. Each nontrivial shift lowers the total binary encoding, so the process terminates. Its effect on the two coordinate degrees (numbers of ones) is to send (a+u,a+v) to (a+u+v,a), where u,v count the opposing exclusive fibers and a counts the common contribution. The squared norm H increases by 8uv. Equality means u=0 or v=0; the shift is then either the identity or a permutation of the two coordinates on the whole family. Hence termination at a six-face with H=24,576 could only have started from a face. In every other case the terminal list and preservation of layers show that A already consisted of 0, the 12 units and 51 pairs.

Encode these pairs by the complementary graph G of the 15 *missing* pairs. If dᵢ are its degrees, then s(A)ᵢ=40+2dᵢ and H(A)=24,000+4Σ dᵢ². The nonface eligibility criterion is exactly Σdᵢ²≥144. This description applies to individual cells independently of any tiling assumption.

## Exact enumeration of the graphs

The shifted enumeration builds an increasing list of word encodings. The generating predecessors of a word are obtained by deleting bit 0 if present or by shifting a present bit down one step into an empty position. It suffices that all fully shifted families obey these necessary conditions. At a prefix maintain the available words all of whose predecessors have appeared; append each larger available word in turn. This visits each eligible family exactly once. The executable reports 12 strict and seven level representatives.

To recover every nonshifted missing-pair graph, start from the 18 nonface terminal graphs and undo all possible pairwise shifts, including nonadjacent coordinate swaps for convenience. In a candidate inverse shift the two vertices have identical neighborhoods except that h exclusive neighbors all belong to one of them (ignoring their mutual edge). Move an arbitrary subset of t of these h neighbors to the other vertex. This reduces Σdᵢ² by 2t(h−t); discard results below 144. One need consider only 0<t≤h/2 because swapping the two vertices interchanges t and h−t. Every forward shift on the original cell's present pairs induces just this same operation, possibly with opposite direction, on its missing-pair graph. Thus reversing the shifting sequence recovers all eligible original graphs.

The Python code deduplicates by exact isomorphism: iteratively split color classes by the multisets of neighbor counts in each current class, branch over the individualizations of a vertex in a class not consisting of interchangeable twins, and take the lexicographically least full adjacency encoding over the remaining branches. Permutations of a twin class are automorphisms. The enumeration yields **151** isomorphism classes (103 with strict inequality).

## A Fourier obstruction allowing arbitrary centers

Let T be the hypothesized 64 centers. Write W_S(z)=Σ_{x∈S}(−1)^{x·z}, unnormalized. A translation tiling gives 1_A*1_T=1; hence W_T(z)=0 whenever z≠0 and W_A(z)≠0. Also for every nonzero difference x∈A+A, the center autocorrelation Σ_c 1_T(c)1_T(c+x) vanishes (otherwise two translates intersect). At zero it equals 64. Fourier inversion, using W_T(0)=64, now gives the necessary equations for x∈A+A:

    Σ_{z:W_A(z)=0} (−1)^{x·z} W_T(z)²/4096 = 63 if x=0, and −1 otherwise.

Coordinates with interchangeable adjacency rows outside the two coordinates form twin blocks in G. Their permutations preserve A, its Fourier zero set and A+A. Average these equations over the product of the block permutation groups. Frequencies have the same orbit iff their numbers of occupied positions in each block agree. After averaging, each frequency orbit O has one unknown u_O, the mean over O of W_T(z)²/4096. Its matrix entry at x is the integer Σ_{z∈O}(−1)^{x·z}. One representative per difference orbit suffices.

Gaussian elimination is over the prime 1,000,000,007, with no floating-point tests. The rational unknowns from a true tiling could be reduced modulo this prime: their denominators divide 4096|O| and |O|≤4096. For 150 of 151 graphs the augmented equations are inconsistent over the field. For the remaining graph they uniquely specify the unknowns; one orbit O of size 48 would have Σ_{z∈O} W_T(z)² congruent to 999,803,399. This nonnegative integer is at most 4096·48=196,608, which rules it out too. The only tiling template with H≥24,576 is therefore a six-face. This is a necessary-condition certificate rather than an enumeration of centers.

## An explicit, nonasymptotic noise interval

For a nonface tiling, H≤24,576−4 since each component of s is even, so B≤6−1/1024. Let the noisy density from a uniform input in A relative to uniform cube measure be 1+u. Walsh expansion gives u=ρL+R, where L=Σᵢ bᵢχᵢ, bᵢ=sᵢ/64, and R contains all degrees ≥2. Parseval on the input density 64·1_A gives Σ_{S≠∅} b_S²=63 for b_S=E_A χ_S. In particular ||R||₂≤8ρ² and E u²≤Bρ²+63ρ⁴. On ρ≤1/512, binomial expansion gives ||R||∞≤(1+ρ)^12−1−12ρ≤70ρ² (bound the ratio of consecutive degree ≥2 terms by 10ρ/3), and ||u||∞≤12ρ+70ρ²<1/4. Orthogonality and the independent coordinate signs give E L³=0, E L⁴≤3B²≤108. Minkowski thus gives ||u||₄≤(108^{1/4}+70ρ)ρ<7ρ/2, and ||ρL||₄<13ρ/4.

Factoring u³−(ρL)³, using Cauchy–Schwarz and Hölder, yields |E u³|≤8ρ⁴[(7/2)²+(7/2)(13/4)+(13/4)²]<280ρ⁴. Also E u⁴<151ρ⁴. On |u|≤1/4 the Taylor upper bound for (1+u)ln(1+u) through degree three has remainder at most u⁴/4, by the fourth derivative 2/(1+u)³. Thus the divergence from uniform in nats is ≤Bρ²/2+117ρ⁴. Since 117/512²<1/2048, this is strictly less than 6ρ²/2≤6C(p)ln 2 for any 0<ρ≤1/512. Every translate has this same divergence. A coordinate face attains equality at all p. At ρ=0 every quantizer attains zero.

**Reproduction.** In this directory run `sh reproduce.sh`. C++17 and the Python standard library suffice; assertions must be enabled. The command regenerates the full shifted extremal list, graph representatives and modular eliminations in seconds. Expected terminal output is in `tiling.log`. No priority claim is made.
