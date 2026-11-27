# When do the ordinary and restricted orders agree?

**Leo Gao** · AI-assisted research and formalization

[Problem overview](README.md) · [Lean theorem](lean/StructuralTrace.lean) · [Replay and audit](lean/README.md)

## 1. What was missing

In [Remark 3(iii), p. 206](https://www.renyi.hu/~p_erdos/1980-22.pdf#page=6),
Erdős and Graham ask: “What are necessary and sufficient conditions that
ord(A) = ord_R(A)?” The [rank-two criterion](rank-two-criterion.pdf)
proves that a centre outside the canonical fringe has enough alternatives
to repair a repeated copy even in the face of the other summands. Thus the
only targets that can fail belong to $2\cdot B+(h-2)A$ in the at-most
sense, where $B$ is the fringe and $2\cdot B$ means dilation, not
a two-fold sumset. On the footprint its exact predicate uses compatibility
of pair choices. In the all-weak case a pair weight can have just one
actual witness. Then the pair test can still have to track which of two
actual labels is shared, separately at each target. A bounded local
obstruction size does not control whether the obstruction persists.

The new lemma is simultaneous separation across infinitely many targets.
It replaces the targetwise pair search with a condition on fixed ordinary
sumsets of $A$; it does not use the pair search in its proof. The old
localization is used only to shrink the class of target sets to test.

## 2. Fixed sparse columns with a stationary head

A box $B_1+\cdots+B_k$ is the ordinary Minkowski sum. One value is taken
from each column, with no rule on equality of the values in the definition
of the sumset. The empty box is ({0}). Fix $g$ and a target set
$T$. We prove the following hereditary assertion even without the basis
hypothesis:

> There are unboundedly many rank-$h$ restricted hits in $T$ if and only
> if there is a fixed disjoint $g$-sparse box with at most $h$ columns
> that meets $T$ unboundedly, with singleton anchors and an unbounded
> intersection after every joint cutoff on its other columns.

**Necessity.** Select an increasing sequence of hits, choosing one
representation for each. One size $k\le h$ occurs infinitely often.
Keep that subsequence and sort the $k$ distinct entries in each row.
For each of the finitely many coordinate sequences, pass to a constant
subsequence if some value repeats infinitely often; otherwise every finite
initial segment of values occurs only finitely many times, so the
coordinate tends to infinity. Perform this extraction successively:
passing to a subsequence preserves a prior constant value or divergence.

Now choose another subsequence of rows. Once a row has been kept, require
every moving coordinate of each later chosen row to exceed every entry
$x$ of the currently kept rows and every $g(x)$ of those entries. The
finitely many moving coordinates all diverge, so this simultaneous demand
can be made at every step. Make (B_i) the range of coordinate (i) on this
last subsequence. Its entries belong to $A$. Different moving columns
cannot intersect across two rows by construction. A constant cannot collide
with a moving coordinate because the constant is present in that moving
entry's own row, whose entries are distinct. Two constants differ by the
same row argument. Repeated values in one column are possible only for a
constant column; all other columns are $g$-sparse. Because all moving
coordinates diverge **on the same subsequence**, for each cutoff $D$ the
same boxes with those columns cut at $D$ contain the sums of all
sufficiently late selected rows. These sums are an unbounded subset of
$T$.

**Sufficiency.** The columns of one box are pairwise disjoint. Any ordinary
element of the box therefore gives a restricted sum of at most $h$
elements of $A$. Use cutoff zero to obtain unboundedly many such hits in
$T$.

In particular the hereditary assertion identifies the *orthogonal ideal*:
a set of targets has finite intersection with every fixed sparse box if
and only if its restricted hits are bounded. It follows that an unbounded
set orthogonal to every box exists exactly when rank-$h$ coverage fails
arbitrarily far out. This is why the equality conclusion gives one
eventual threshold. If no threshold exists, the complement of rank-$h$
coverage is an unbounded witness against the structural condition. This
argument does not interchange a threshold with a target-varying forbidden
set. In the extraction the only thresholds vary with $D$ on a **chosen**
subsequence, and the finite set of anchored columns never changes.
Restricted order cannot be less than ordinary order, by inclusion of the
two kinds of sums. These observations prove both directions of the main
theorem. They also show that testing only subsets of the footprint
suffices: all large rank-$h$ failures are in it by the previously checked
repair lemma.

## 3. Quantitative and arithmetic consequences

**Arbitrary counting envelope.** For every $f:\mathbb N\to\mathbb N$
tending to infinity, choose $g(u)$ so that
$f(x)\ge h(u+2)$ for all $x\ge g(u)$. For $x$ large enough also
$f(x)\ge h$. In a column with at least two entries in $[0,x]$, let $u$
be its second largest and $v$ its largest. There are at most $u+2$
entries, and $g(u)<v\le x$. Thus its count times $h$ is at most $f(x)$.
The same bound holds for zero or one entry. With $k\le h$ the union
therefore has at most $f(x)$ entries for all sufficiently large $x$.
The case $h=0$ has an empty union. Consequently in the equality case
every escaping $T$ has an ordinary additive trace of budget $h$ inside
a subcollection of $A$ with **arbitrarily slow prescribed prefix growth**.
The version with disjoint columns is itself equivalent to equality.
Uncolored thin ordinary traces alone do not supply the converse: repeated
summands can belong to the same thin set.

**No bounded-coefficient relations inside the columns.** Given a digit
bound $M$, discard zero from the representations (the budget is at
most), and require $g(x)=(M+1)x$. Then in a given column each positive
entry $z$ is bigger than every finite sum of lower entries with digits
in $\{0,\ldots,M\}$. This holds by induction on the number of lower
entries: if the greatest lower entry is $a$, the rest sum to less than
$a$, and $Ma+a<z$. In two differing digit assignments cancel matching
digits and take the largest entry with a nonzero difference. Its effect
cannot be balanced by the lower entries. Thus even relations with no bound
on the number of participating entries are trivial. This arithmetic
version also characterizes equality, as the reverse direction uses only
the disjointness of the columns.

These are statements about uniform structure across infinitely many
targets. Merely coloring one representation per target supplies neither
the prefix-count bound on a **single** union, nor fixed anchors that
survive every cutoff, nor integer relation uniqueness inside whole
columns.

## 4. Nonperiodic examples and a finite residue profile

Suppose $A$ contains a full residue class $c\pmod q$, and let $S$ be
its complement *within* $A$. At budget $h$ suppose that in each residue
class there are arbitrarily large numbers not in the ordinary at-most
$h$ sumset of $S$. This holds, for example, if
$|S\cap[0,x]|=O(\log(x+2))$: at most $O_h((\log(x+2))^h)$ values up to
$x$ can be obtained from $S$, whereas each residue has linearly many.

A finite profile decides coverage in this class. For every $r\bmod q$,
choose a positive number $k$ of core slots and a word of outside residue
tags $u_1,\ldots,u_j$ with $k+j\le h$ and
$kc+\sum_i u_i\equiv r\pmod q$. The ordinary test needs every tag to be
present in $S$; the restricted test needs the demand for each tag to be
at most its supply. Supply is the number of outside elements in that
residue, capped at $h$. The profile reads counts, not the positions of
these elements. Necessity follows by taking a sufficiently large number
in residue $r$ missed by outside-only sums; its representation must
have a core slot. For sufficiency, choose representative outside elements
once per $r$, then choose $k-1$ distinct core representatives. Let
the last core summand absorb the remaining size. It is in the prescribed
class and exceeds all previous summands once the target is large enough.
A single threshold works by taking the maximum over the finitely many
residues. In trace terms, these fixed representatives are anchors and
the final core slot gives the moving column. In a missing residue take
the unbounded subset outside all outside-only sums: it is orthogonal
to every budget-$h$ box.

**Lean-checked example pair.** Let
$$
 A_- =5\mathbb N\cup\{1\}\cup\{5\cdot 10^j+4:j\ge0\},\qquad
 A_+=A_-\cup\{6\}.
$$
Both ordinary orders are 3. Using a core slot, the residues $0,1,2,3,4$
have ordinary outside words (), (1), (1,1), (4,4), (4).
At rank 2, residue 2 fails the profile. For $A_-$, the sole rank-3 way
to obtain residue 2 with a core slot asks for two distinct residue-1
elements. Only one exists. Three residue-4 elements repair this at rank
4. For $A_+$, two residue-1 elements are available and the other residue
tests already work at rank 3. Hence
$$
 (\operatorname{ord}(A_-),\operatorname{ord}_R(A_-))=(3,4),\qquad
 (\operatorname{ord}(A_+),\operatorname{ord}_R(A_+))=(3,3).
$$
For an explicit escaping test at $r\bmod 5$, use
$30\cdot 10^j+r$ with $j\ge1$. Every available outside element below this
target is at most $5\cdot10^j+4$. Four times that bound is smaller than the
target. This argument, both order pairs, and nonperiodicity were checked
in Lean. To see nonperiodicity, a positive eventual period $p$ would
also give period $5p$; a sufficiently large term $5\cdot10^j+4$
followed by that shift lands strictly between successive sparse terms and
remains in residue 4, a contradiction. Also $A_-$ and $A_+$ agree from
7 on. Thus their tails give identical eventual residue data at **every**
modulus but different equality behavior.

**Arbitrary $h\ge3$ (written proof).** Put $q=2h-1$, take all
multiples of $q$, the sparse infinite residue-1 set
$\{q\cdot10^j+1:j\ge0\}$, and exactly $t$ fixed residue-2 elements.
With a core slot, every residue $0,\ldots,2h-2$ is an ordinary sum
of at most $h-1$ tags from $\{1,2\}$ (use as many twos as possible),
assuming $t>0$. The last residue needs $h-1$ tags, so the ordinary
order is exactly $h$; the outside-only count cannot rescue a smaller
rank. It requires $h-1$ twos at rank $h$, deciding the restricted
case with $t=h-2$ or $t=h-1$. In the first case add two ones to
$h-2$ twos for that last residue, giving restricted order $h+1$; in
the second case all residues work at $h$. The other residues need
at most $h-2$ twos. For nonperiodicity repeat the residue-4 argument
using residue 1 and shift $qp$. This gives nonperiodic equality and
strict inequality at every ordinary order $h\ge3$, with one finite
change between the two.

## 5. The number of moving columns cannot be bounded below the rank

For any $h\ge 2$, let $D_i$ contain the positive integers with nonzero
binary digits only at positions congruent to $i$ modulo $h$, and take
$A=\bigcup_{i=0}^{h-1}D_i$. Splitting the binary digits by position
classes represents every $n$ by at most $h$ distinct terms of $A$.
Because $|A\cap[0,X]|=O_h(X^{1/h})$, the ordinary at-most $(h-1)$ sumset
$S$ has at most $O_h(X^{$h-1$/h})$ values through $X$; neither order is
below $h$. The basis is infinite with density zero, hence nonperiodic.

Enumerate the shifts $m+S$ for $m\ge0$. Recursively choose a larger
target that avoids the first $j$ shifts at stage $j$; that finite
union has density zero. The resulting unbounded set $T$ meets every
fixed shift only finitely. Any box with fewer than $h$ columns is
contained in $S$. If an $h$-column box has a finite column, it is
contained in a finite union of shifts of $S$. Neither can trace $T$.
Thus **all $h$ columns must move** on this probe. The general theorem
nevertheless yields an arbitrarily sparse choice of those columns.
The density computations and this particular example are written
proofs; the extraction theorem is checked in Lean.

There is also no universal countable menu of sufficiently sparse
boxes. For $g(x)=2x$ a column has $O(\log(X+2))$ values through $X$,
so a fixed budget-$h$ box has $O_h((\log(X+2))^h)$ such values.
In any proposed countable menu, choose an escaping target outside
the first $j$ boxes at stage $j$. This gives an unbounded probe
orthogonal to every box in the menu. The diagonal lemma
`simultaneous_escape` is Lean-checked; the logarithmic estimate is
the elementary doubling argument. This does not contradict the theorem,
whose columns are chosen relative to the whole probe $T$.

## 6. Scope

The global invariant uses ordinary sumsets of subcollections of $A$;
it is not a finite table for general $A$. The finite table in Section 4
uses its stated core and escape assumptions, not assumptions in the general
Lean theorem. In the [separate stress test](thinning-test.md) we also show why even full
**unthinned** ordinary representation counts at selected hard fibres can
fail to notice a change of equality behavior. We make no claim about
publication priority or external acceptance.
