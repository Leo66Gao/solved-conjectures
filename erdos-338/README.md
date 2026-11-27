# Erdős #338

**Leo Gao** · Research and Lean formalization with AI assistance

**Lean 4 verifies a positive answer to Erdős #338(ii).** For every ordinary
order $h$, the finite restricted order is bounded by a function of $h$ alone.
For part (iii), I give a Lean-checked sparse-sumset criterion for equality
of the two orders. The project also formalizes Chen–Yang–Zhao's results
for parts (i) and (iv). The four questions appear in
[Erdős and Graham, p. 206, Remark 3][original].

[Uniform-bound theorem in Lean](lean/Full338.lean#L79) ·
[Sharp growth manuscript (written proof)](sharp-boundedness.pdf) ·
[Build and axiom audit](lean/BUILD-AND-AXIOMS.txt)

Independent review of the results and historical priority are pending.

| Original question | Result |
| --- | --- |
| When does a finite restricted order exist? | [Chen–Yang–Zhao][cyz]: every residue modulo every positive integer occurs as a finite subset sum. Formalized here. |
| Is there a uniform bound in terms of ordinary order? | Yes. Lean checks an explicit bound; a [separate paper proof](sharp-boundedness.pdf) gives the sharper growth rate. |
| When are the orders equal? | [Structural criterion and proof](structural-equality.md), checked in Lean for every finite ordinary order. For each unbounded target set and prescribed sparsity, there must be fixed, disjoint subsets of the basis whose ordinary sumset meets the target set unboundedly, even after any cutoff on the nonsingleton subsets. The criterion's adequacy as an answer to the historical question remains open to independent assessment. |
| What if ordinary order survives finite deletion? | [Chen–Yang–Zhao][cyz]: both variants imply finite restricted order. Both are formalized here. |

## Verify

[Lean guide](lean/README.md) · [Proof map](lean/PROOF-MAP.md) · [Build and axiom audit](lean/BUILD-AND-AXIOMS.txt)

With Lean 4.34.0, Git, Bash, and Python 3, run:

```sh
cd erdos-338/lean
./verify.sh
```

The script rebuilds the original and new Lean sources with pinned
dependencies and checks that the audited theorems use only standard axioms.

## Supporting proofs

- [Ordinary-count thinning test](thinning-test.md): an independent characterization and examples where raw representation counts miss the difference.
- [Earlier rank-two criterion (PDF)](rank-two-criterion.pdf): the local reduction that motivates the new global test.
- [Earlier overview (PDF)](overview.pdf) and [quantitative bounds (PDF)](restricted-orders.pdf).

The structural criterion does not require actual pair witnesses as input.
It still quantifies over infinite target sets and is not a finite decision
procedure for arbitrary bases.

[original]: https://www.renyi.hu/~p_erdos/1980-22.pdf#page=6
[cyz]: https://arxiv.org/html/2611.33191v1
