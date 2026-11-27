# Erdős Problem #338

**Leo Gao** · AI-assisted research and formalization

This packet gives checked Lean 4 proofs corresponding to all the questions
in [Erdős and Graham, p. 206, Remark 3][original]. No declaration uses
`sorry` or nonstandard axioms. The exact equality criterion is a proposed
answer to the original wording; its adequacy and priority await external
review.

| Original question | Result and credit |
| --- | --- |
| When does a finite restricted order exist? | [Chen–Yang–Zhao][cyz]: every residue modulo every positive integer is hit by a finite subset sum. Formalized here. |
| Is there a uniform bound in terms of the ordinary order? | Yes. The Lean package gives an explicit bound depending only on the ordinary order. The sharper growth rate below is a separate paper proof. |
| When are the two orders equal? | Gao's exact rank-two criterion. The Lean proof reduces the question to two-term arithmetic and compatibility of bounded fringe data for each target. |
| What if ordinary order survives finite deletion? | [Chen–Yang–Zhao][cyz]: both variants imply finite restricted order. Both are formalized here. |

## Check it

[Lean project](lean/) · [Final declarations](lean/Full338.lean) · [Build and axiom audit](lean/BUILD-AND-AXIOMS.txt) · [Proof map](lean/PROOF-MAP.md)

With Lean 4.34.0 (via `elan`), Git, Bash, and Python 3:

```sh
cd 48-erdos-338-restricted-orders/lean
./verify.sh
```

The script fetches a pinned Lean dependency, rebuilds this source in a fresh
object directory, and audits the five declarations. See [replay instructions](lean/README.md).

## Read the proofs

- [Overview](overview.pdf) ([LaTeX](overview.tex))
- [Equality criterion and proof](rank-two-criterion.pdf) ([LaTeX](rank-two-criterion.tex)), especially Theorem 7.2
- [Sharp boundedness](sharp-boundedness.pdf) ([LaTeX](sharp-boundedness.tex)): `log log F(h) = h log 2 + O(log h)`, where `F(h)` is the largest finite restricted order at ordinary order `h`. The sharp upper growth rate is not part of the Lean audit.
- [Earlier quantitative proof](restricted-orders.pdf) ([LaTeX](restricted-orders.tex)) and [finite check](check_growth.py)

The equality condition still quantifies over sufficiently large targets.
In the entirely weak fringe it can retain the actual pair witnesses. It
is not a finite decision procedure for arbitrary infinite bases or a
classification of where the obstructions persist. The existence and
finite-deletion theorems are not claimed as new mathematics here.

[original]: https://www.renyi.hu/~p_erdos/1980-22.pdf#page=6
[cyz]: https://arxiv.org/html/2611.33191v1
