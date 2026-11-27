# Erdős #338: when do ordinary and restricted orders agree?

**Leo Gao** · AI-assisted research and formalization

The main result is an exact, **Lean-verified necessary-and-sufficient condition** for the two orders to agree. It replaces sums of distinct terms at the full order with a test built from ordinary two-term sums and a finite compatibility graph for each decomposition. This is a candidate resolution of the [original question](https://www.renyi.hu/~p_erdos/1980-22.pdf#page=6), not a claim that Erdős #338 has been accepted as solved.

## Start here

| File | What it covers |
| --- | --- |
| [Two-page overview](overview.pdf) · [LaTeX](overview.tex) | The four original questions, the equality criterion, and what remains outside Lean. |
| [Equality proof](rank-two-criterion.pdf) · [LaTeX](rank-two-criterion.tex) | The rank-two criterion, its proof, and the alternative blocker construction. See Theorem 7.2 for the main equivalence. |
| [Sharp boundedness](sharp-boundedness.pdf) · [LaTeX](sharp-boundedness.tex) | If the ordinary order is at most $h$, the worst-case finite restricted order $F(h)$ satisfies $\log\log F(h)=h\log 2+O(\log h)$. |
| [Lean 4 project](lean/) · [Build and axiom audit](lean/BUILD-AND-AXIOMS.txt) | The equality criterion, the blocker construction, the mixed-radix lower bound, and several special cases. |

## What the criterion says

Group a proposed representation into pairs, and a singleton if needed. At each pair weight, the test either certifies that the weight is unaffected by small deletions from the fringe or lists its possible fringe supports. The fringe consists of elements with too few symmetric replacements. The chosen supports must be disjoint. A repair argument then removes any remaining repeated summands without increasing the order.

This gives an equivalent condition for equality for every ordinary basis. The test still has to hold for all sufficiently large targets in the fringe footprint; it does not classify when those obstructions persist, or give a finite decision procedure for arbitrary infinite bases.

## Scope and reproduction

The Lean statement for the equality question is [`equal_order_iff_reflected_footprint`](lean/Erdos338/Equality.lean). The project builds with Lean 4.19.0 and Mathlib v4.19.0. From this directory, run `cd lean && bash verify.sh`. The audited theorems use no `sorry` or project-specific axioms.

The existence criterion and the two finite-deletion variants are due to [Chen, Yang and Zhao](https://arxiv.org/abs/2611.33191). The analytic input for the uniform upper bound and the full existence and deletion arguments are not verified in Lean here. The [earlier quantitative proof](restricted-orders.pdf) remains available with its [source](restricted-orders.tex) and [finite check](check_growth.py).
