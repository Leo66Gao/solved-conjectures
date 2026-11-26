# Certified conditional bounds for distinct covering systems

**Leo Gao** · AI-assisted research · Not peer reviewed

[Read the PDF](manuscript.pdf) · [LaTeX source](manuscript.tex)

> **Abstract.** We give explicit partial distinct covers of periods $10{,}080$ and $15{,}120$, and prove exact minimum defects of $84$ and $68$ under specified fixed-prefix constraints. Weighted certificates and exhaustive integer branching establish these conditional optima. Neither candidate period is excluded without the prefix constraints.

## Result and scope

[Zhang, *Small-LCM Distinct Covering Systems*, §3.2](https://arxiv.org/html/2611.01282v1) reports that the least period of a distinct congruence cover with minimum modulus 8 is one of 10080, 15120 and 20160, constructs the 20160 case, and leaves 10080 and 15120 unresolved. We obtained two dense partial covers and certified that neither can be repaired by changing only its tail. The problem of completely covering either period is **not** resolved.

| Period | Fixed residues | Free residues | Optimal defect |
| ---: | ---: | ---: | ---: |
| 10,080 | 35 | 30 | 84 |
| 15,120 | 44 | 29 | 68 |

The full residue assignments are in `best-10080-11.txt` and `best-15120-12.txt`.

Each row uses every divisor of the period that is at least 8, with exactly one residue per divisor. The two files hold **modulus, residue** pairs. A direct modular scan confirms 9,996 and 15,052 covered residues. The frozen portions end at moduli 144 and 252, respectively. No global optimality is asserted. The neighborhood optima, however, are exact.

The weaker restriction keeping just 25 or 32 of the smallest moduli's shown residues already admits exact integer-weight certificates of at least 7 or 1 missing residues, respectively. Those bounds prohibit completion but need not be tight.

## Proof and exact replay

Let U denote the residues not already covered by the frozen choices. For any nonnegative integer weight w supported on U, the total weight covered by the tail is at most
$\sum_d \max_r \sum_{\substack{u\in U\\u\bmod d=r}} w(u)$.
A union counts covered points at most once, and each modulus contributes at most its own maximum. Subtract this from the total weight and divide by the largest weight (round up) to bound the number of uncovered residues. The weights in the four `witness-*.json` files are explicit and checked independently of the LP that proposed them.

For the sharper, exact neighborhood optima, run `python proof_check.py` with Python 3.10 or later, no third-party packages. The included solver tests feasibility of 83/67 holes. It branches on residue choices, tracking the set already covered. For both U and the unit-weight witness subset W, it adds up the maximum gains of the not-yet-used moduli, ignoring overlaps. A branch that cannot reach the corresponding cardinality target even under this optimistic bound is impossible. Residue choices whose individual loss exceeds the available slack are impossible for the same reason. Choices with identical new covered sets are equivalent; a zero-gain choice is dominated by a positive one. A modulus for which every class contains at most one point of U can be left to the end: it can then cover any one point still needed, so a pool of k such moduli can cover exactly min(k, remaining) points. Exhausting all branches gives the exact exclusions in 1,985 and 1,931 nodes. Direct brute force independently agrees with the pruning procedure on 500 seeded small test instances. `certified-results.txt` records the output.

## Structural continuation: project to the smaller CRT period

For L=35Q with gcd(35,Q)=1, at each base residue x modulo Q, classes with moduli coprime to 35 either cover the entire 5×7 fiber or miss it. In an uncovered fiber, a 5-only class hits one whole row, a 7-only class one column, and a class divisible by 35 one cell. If there are r matching row classes, c matching column classes and k matching cell classes at x, even allowing all row and column labels to be optimally distinct, the uncovered count is at least $\max\{0,\max(5-r,0)\max(7-c,0)-k\}$. Summing this inequality uses only projected residue choices in periods Q=288 or 432. For the explicit partial covers it accounts for 71 of 84 and 58 of 68 holes, so rearranging mod-5/mod-7 labels without changing their base projections cannot repair them. The smaller relaxed optimization might be a practical way to attack the global exclusion, but a search failing to reach zero is not an exclusion proof.

The neighborhood witness method is a standard covering/packing idea applied to these concrete congruence instances. No claim is made of a literature-first algorithm or a verified scientific breakthrough.
