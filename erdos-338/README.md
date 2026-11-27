# Erdős #338

**Leo Gao** · AI-assisted research and formalization

This packet gives Lean 4 proofs for the questions in
[Erdős and Graham, p. 206, Remark 3][original]. It is not a claim of
external acceptance or priority.

| Original question | Result |
| --- | --- |
| When does a finite restricted order exist? | [Chen–Yang–Zhao][cyz]: every residue modulo every positive integer occurs as a finite subset sum. Formalized here. |
| Is there a uniform bound in terms of ordinary order? | Yes. Lean checks an explicit bound; a [separate paper proof](sharp-boundedness.pdf) gives the sharper growth rate. |
| When are the orders equal? | [Structural criterion and proof](structural-equality.md), checked for every finite ordinary order. Every unbounded set of targets must meet a single ordinary sum of fixed, disjoint, arbitrarily sparse subsets unboundedly. The same subsets work after cutting off the moving terms at any height. |
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
