# Erdős #338: Lean 4 formalization

**Leo Gao** · Research and Lean formalization with AI assistance

This project checks a uniform bound for part (ii) and equality criteria
for part (iii). It also formalizes the existence criterion and
finite-deletion results of **Shi-Qiang Chen, Quan-Hui Yang, and Lilu Zhao**
for parts (i) and (iv).

Let an *ordinary asymptotic basis* be a set $A\subseteq\mathbb N$ for
which every sufficiently large integer is a sum of at most $h$ elements of
$A$, repetitions allowed, for some $h$. Its *restricted order* is finite
when an analogous bound exists using distinct elements.

**Theorem.** For an ordinary asymptotic basis, finite restricted order
exists if and only if, for every positive modulus $q$, every residue
modulo $q$ is the sum of a finite subset of $A$, each element used once.

This is Theorem 2 of [Chen–Yang–Zhao, arXiv:2611.33191v1][cyz] and answers
the existence biconditional used on the [Erdős Problem a Day page][day].
The existence theorem in `Erdos338Solution.lean`, and the uniform bound in
`Full338.lean`, use the same at-most order
predicates as the [Formal Conjectures statement][fc] (eventual membership,
Multiset witnesses for ordinary order, and Finset witnesses for restricted
order). The answer uses natural residue representatives $0\le r<q$;
for $q=0$ the universal condition has no instances. This package is a
standalone check at its own pinned toolchain, not a merged upstream
Formal Conjectures pull request or a Palomar registration.

## What is checked

| Declaration | Content |
| --- | --- |
| `Erdos338.erdos_338` | Both directions of the existence criterion, unconditionally on ordinary bases |
| `Erdos338.erdos_338.variants.basis_after_finite_removal` | Finite restricted order if every finite deletion is an ordinary basis |
| `Erdos338.erdos_338.variants.same_order_after_finite_removal` | The same conclusion if every finite deletion keeps one common exact ordinary order |
| `Erdos338.erdos_338.variants.eq_order` | Leo Gao's separate rank-two equality criterion, using the catalogue's exact least orders |
| `Erdos338.erdos_338.variants.bounded_by_order` | A bound depending only on ordinary order, when restricted order is finite |

For the [structural criterion for part (iii)](../structural-equality.md),
start with `Erdos338.SparseTrace.equal_orders_iff_anchored_trace` in
[`StructuralTrace.lean`](StructuralTrace.lean). It assumes only the finite
ordinary order and tests ordinary sumsets of fixed disjoint sparse columns.
The [thinning test](../thinning-test.md) gives a separate exact equivalence.

No `sorry` or unproved analytic premise is used in the final declarations.
Their axiom audit lists only `propext`, `Classical.choice`, and
`Quot.sound`. See [proof map](PROOF-MAP.md) for which code proves each step.

**Exact scope.** The uniform bound is an unconditional, explicit recursive
function of ordinary order in Lean. It answers the original qualitative
boundedness question. The sharp growth rate has a separate
[written proof](../sharp-boundedness.pdf) outside this formalization.
Lean checks the earlier targetwise rank-two criterion and the global
sparse-sumset criterion as equivalences. Both still involve infinite
target data for general bases. Their adequacy as an answer to the historical
equality question remains open to independent assessment.

## Replay

Install [elan](https://github.com/leanprover/elan) and have Git, Bash, and
Python 3 available. From this directory:

```sh
./verify.sh
```

The first run checks out a pinned dependency and builds the named upstream
Lean modules. It needs network access and enough disk space for the Lean
toolchain and Mathlib cache. To reuse a checkout set `ERDOS335_ROOT` to
its directory. Set `ERDOS338_SKIP_DOWNLOAD=1` only if the external
checkout already has its dependencies and compiled Mathlib cache. The
script checks both dependency pins, compiles every supplied source into a
fresh directory, then imports the compiled objects and audits the original
declarations and structural extension. The build may print deprecation warnings on Lean 4.34.0.

## Credits and dependencies

* [Chen, Yang, and Zhao][cyz]: the existence criterion, the finite-deletion
  implication, and the adaptive disjoint-representation strategy.
* [Hegyvári, Hennecart, and Plagne][hhp]: positivity of the lower density
  of restricted sumsets for an ordinary basis. This package independently
  implements a finite promotion argument for the positivity it needs.
* [Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer][dyson] and
  the contributors credited in their repository: the pinned two-set
  Dyson/Kneser library primitives. The package adds mixed-list stabilization,
  common-divisor compression, and disjoint-representation lifting. It
  **does not vendor or redistribute** that external repository's sources.
* Augustinas Bakšys and Yaël Dillies: the finite Kneser code used
  in the cyclic modulus-reduction step, via the pinned Erdős #335
  dependency. The dependency's [provenance record][attribution] identifies
  that source and preserves its license.
* Erdős and Graham originally posed the questions in
  [*On bases with an exact order*, p. 206][original]. The separate equality
  criterion is carried forward from the existing Leo Gao package [here][bounds].

[cyz]: https://arxiv.org/html/2611.33191v1
[day]: https://www.erdosproblemaday.com/problem/338
[fc]: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/338.lean
[hhp]: https://doi.org/10.1515/crll.2003.055
[dyson]: https://github.com/Ghuffy1/erdos-335/tree/29e64ce67b4999f76657bb4b51e306076f59e689
[original]: https://www.renyi.hu/~p_erdos/1980-22.pdf
[bounds]: https://github.com/Leo66Gao/solved-conjectures/tree/main/erdos-338

[attribution]: https://github.com/Ghuffy1/erdos-335/blob/29e64ce67b4999f76657bb4b51e306076f59e689/ATTRIBUTION.md
