# Ordinary-count thinning test

**Leo Gao** · AI-assisted research and formalization

[Main structural proof](structural-equality.md) · [Replay and audit](lean/README.md)

**Scope.** This concerns [Remark 3(iii), p. 206 of Erdős and Graham, *On bases
with an exact order* (1980)](https://www.renyi.hu/~p_erdos/1980-22.pdf#page=6). Both orders use at most the stated number of
summands. The ordinary order permits repeats; the restricted one forbids
them. The published rank-two theorem can still retain actual pair endpoints
on an all-fringe Sidon input. This note gives a different arbitrary-rank
criterion whose observations are aggregate **ordinary** counts, not endpoints,
matchings, restricted counts, or oracle calls to a bad-target set. It also
proves a separation on nonperiodic bases. It is a response criterion, not a
finite set of tail parameters known a priori. The distinction matters: its
highest coefficient is algebraically equivalent to the restricted count.

## Observable, theorem, and proof

For fixed arity k and target n, retain each member of A∩[0,n] independently
with probability p. Let R_k(S,n) count all **ordered ordinary** k-tuples in
the retained set S with sum n; repeats are allowed. Form its mean m_k(n,p).
This can be obtained by finite averaging of ordinary counts, or by estimating
them from ordinary samples. It uses no tests of distinctness. The points
p_i=(i+1)/(k+2), i=0,…,k, are fixed once k is fixed, independently of n or A.

**Finite-panel theorem.** If A has exact finite ordinary order h, it also
has exact restricted order h if and only if for all sufficiently large n
there is some k≤h such that the k+1 mean counts m_k(n,p_i) do **not** fit a
polynomial of degree strictly less than k. For k=0 the only such polynomial
is zero. Thus the obstruction to equality is an unbounded sequence of
targets on which every arity has a low-degree ordinary thinning response.
At each probe only a scalar mean of ordinary counts is read, even if every
pair weight is weak or uniquely witnessed.

Proof. An ordinary tuple w survives with probability p raised to the number
of different labels in w: the retention variables are independent across
labels, not across potentially repeated entries. Linearity gives
m_k(n,p)=sum_w p^{|supp(w)|}, a polynomial of degree ≤k with nonnegative
integer coefficients. Its kth coefficient is positive if and only if some
ordinary k-tuple has k different labels. The k+1 rates are distinct and
therefore distinguish this polynomial from every smaller-degree polynomial
unless it actually is of smaller degree. Necessity: if restricted order h
covers all n≥N, choose the true arity independently at each n≥N. Sufficiency:
a nonfitting panel supplies a distinct tuple for each n≥N. A restricted
order below h would also be an ordinary order below h. There is only one
outer threshold, and no moving forbidden set or quantifier exchange.
Removing zero is unnecessary: the test considers each actual arity
separately and the empty tuple is allowed exactly at n=0.

**Uniform separation (Lean-checked).** At the i-th rate, the mean lies on the
rational lattice (k+2)^{-k}·ℤ. In fact multiplying by (k+2)^k turns the
contribution of a tuple with d different entries into the natural number
(i+1)^d (k+2)^{k−d}, with i indexed starting at zero. Hence rounding an
estimate with error strictly less than half the mesh uniquely recovers the
exact mean. Two bases whose corresponding ordinary thinning means differ
by less than one mesh at all late targets and all relevant arities have
identical restricted-coverage status at that order, even without identifying
any endpoints or coupling individual representations. The spacing does not
shrink with n or with the number of representations.

**A sharper robustness bound and sample access (paper corollary).** The kth finite difference
of the observed means, at the indicated k+1 equally spaced rates, is
(k!/(k+2)^k) times the number of ordered distinct k-representations. This
is the usual forward-difference identity, proved by applying the difference
operator k times to the basis monomials (it lowers degree by one and multiplies
the top coefficient by the old degree times the mesh at each step). Its
coefficients have total absolute weight 2^k. Thus either the difference is
zero or it is at least δ_k=k!/(k+2)^k. If each input mean is known to
absolute precision <δ_k/2^{k+1}, thresholding the difference at δ_k/2 gives
the correct decision. If the unthinned ordered ordinary count in the fiber
is M, observations from independent random thinnings lie in [0,M]. For
fixed h, Hoeffding and a union bound give O_h(max(1,M²) log(n+2)) samples
at each rate with error probability at most (n+2)^{-2} (adjust the constant
for the finitely many arities/rates). The first Borel–Cantelli lemma gives
almost surely correct decisions for all sufficiently large n; no independence
between targets is required. This does not assert efficient exact computation
in very high multiplicity or provide an algorithm deciding cofiniteness of
an arbitrary infinite set.

## Nonperiodic all-rank family separating pointwise raw counts

Fix h≥3, q=7h−2, C_j=100·10^j for j=0,1,… . The bad-block index set E is
arbitrary. Write G={1,2,6} and D={1,4,7}. Form A_E as follows:
- include all positive integers with residues 4,5,6,7 modulo q;
- include all positive integers with residue 3 except the marks
  n_j=q(3C_j+9)+3;
- in residue 1, include q(C_j+d)+1 for d in D if j∈E and d in G otherwise;
- include nothing else.

**Claim.** The ordinary order is h. The restricted order is h if E is finite
and h+1 otherwise. Each A_E is nonperiodic even when E itself is finite.
**At every marked target, for all k≤h, the vector of unthinned ordinary
counts is independent of the switch:** it is 6 for k=3, zero otherwise.
Nevertheless, exactly the good marks have a full response: m₃(n_j,p)=6p³
at good marks and 6p² at bad marks. Even one rate p=1/2 separates the two
scenarios, with means 3/4 and 3/2.

Proof. Positive raw residue totals of at most h summands are ≤7h. At residue
3, a representation of a mark must have raw total 3, since q+3=7h+1.
Thus it can only be a singleton or three residue-1 elements; the singleton
is absent. For three elements the three column indices must sum to 3C_j+9.
Earlier indices are ≤C_j/10+7, current indices are in C_j+[1,7], and later
indices exceed 10C_j. No later index can enter. If any earlier index entered,
even adding two of the largest permitted indices falls short since
C_j/10+7 + 2(C_j+7) < 3C_j+9 for C_j≥100. Thus all three offsets come from
the same current block and sum to 9. For G the only unordered multiset is
{1,2,6}, with six permutations; for D the only ones are {1,1,7} and
{1,4,4}, with three permutations each. This proves all the asserted fiber
counts and thinning means. The same argument handles the very first block.

All residue classes except 3 are represented by raw totals in [4,7h]:
the intervals [4k,7k] (k=1,…,h) are consecutive or overlapping and
each is a sum of k tags in {4,5,6,7}. In a fixed pattern of k tags,
choose k−1 distinct fixed positive representatives and put all remaining
size into the last term of its prescribed full residue class. For all
sufficiently large targets in that residue, this last term is bigger than
the fixed ones. There are only finitely many residue classes; take the
maximum of their thresholds. Unmarked targets with residue 3 are singletons;
marked ones have the ordinary coverage just proved. At order h−1 the
class q−1 cannot occur: (h−1)7 < q−1. This proves exact ordinary order h
and the restricted lower bound h. Bad marks occur unboundedly exactly if E
is infinite. For order h+1, even those marks are handled by the same full
classes, since 4(h+1) ≤ q+3=7h+1 ≤ 7(h+1), so the restricted order then
is exactly h+1. The infinite residue-1 column sequence is sparse with
unbounded gaps. An eventually periodic set intersected with class 1 would
give an eventually periodic column sequence, impossible here.

**What this separates.** Unthinned ordinary representation counts at the
hard targets, even at *all* allowed arities, do not determine equality
there. This is a pointwise information model, not an assertion about knowing
every count at every integer (R₁ already determines A). The example gives
a primary hard target in each block, unaffected by the choices in *all
other* blocks. It does not say all members of the example are fringe.

**Why not use just p=1/2?** The one-rate observation happens to separate the
chosen G and D stencils, but fails in general. Use G against D′={1,4} at
the same target 9. G gives 6p³, whereas D′ has just the three permutations
of (1,4,4), giving 3p². They agree at p=1/2 although only G is restricted.
The same residue embedding makes these equal half-rate observations
recur at unbounded marked targets, at any h≥3. This is not a lower bound
of k+1 samples for every model (the model could also provide other data),
but explains why one should not extrapolate the half-rate example.

## Verification and limitations

- `Thinning.lean` proves the exact polynomial expansion from an independent
  keep/drop recursion, identifies its observable with the ordinary count
  on a thinned basis, and proves the coefficient criterion at all arities.
- `Samples.lean` proves the fixed rational rates are in (0,1), that the
  lower-degree fit exists iff the top coefficient vanishes, and the endpoint
  `Erdos338.Thinning.equal_orders_iff_ordinary_thinning_panel` under the
  exact-ordinary-order hypothesis only. Formal `LowFit` takes k+1 rationals,
  not a polynomial, as input. The catalogue's `HasOrder` and
  `HasRestrictedOrder` are reused.
- `Quantized.lean` proves the lattice, uniform observation separation, and
  all-h transfer of restricted order under sub-mesh comparisons.
- `Molecules.lean` certifies the two exact response polynomials of the finite
  stencils by kernel reduction, the all-h forced residue shapes, and the
  no-cross-block lemma. The infinite family's residue-class lifts and its
  eventual order assertions above are written proofs, not formalized
  endpoints. The perturbation/sampling corollary is also paper-only.
- No claim that interpolation compresses the time required to read A, or
  that computing all these scalars is easier than enumerating representations.
  This removes named witnesses from the right-hand-side observations and is
  a substantive separation in the stated model. It does not, by itself,
  yield a geometric classification of all entirely weak bases.
