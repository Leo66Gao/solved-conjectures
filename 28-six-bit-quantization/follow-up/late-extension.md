# Refining the partition-aware interval to crossover 0.310012817

**Theorem.** On the ten-dimensional Boolean cube with uniform input and independent binary symmetric noise, every deterministic quantizer with at most 64 values satisfies the six-coordinate information bound for every
\[
 0\le p\le20317/65536=0.3100128173828125.
\]
This is an unrestricted result in this dimension, not a bound for arbitrary input length. It strictly exceeds the rigorous obstruction for any independent-cell affine certificate, which already fails at \(20202/65536\); see **band-proof.md**. The range above \(20317/65536\) remains open for arbitrary ten-input maps.

Use the notation \(C(p)=\ln2-h(p)\), \(J(A,p)=I(X_A;X_A\oplus Z)\) in nats, for \(X_A\) uniform on the cell of size \(m\). Consider the band \([20201,20317]/65536\) and put
\[
 F(A,p)=J(A,p)-[4+\lambda(1-16/m)]C(p),
 \qquad\lambda=141926/100000,\quad\eta=1/15360 .
\]
The earlier **band-proof.md** gives the conclusion for all smaller crossover. We use the same three critical types as **critical-tiling.md**: the 11-point full ball, the 20-point edge-ball, and a coordinate four-face. This proof uses all isometric copies of each named type.

## Exact margins and their transfer to uncompressed cells

For each critical ball or edge-ball the complete-band shell check **late-critical.py** proves \(F>-\eta\) by 767 and 743 exact closed interval checks respectively. Four-faces have \(F=0\). For all other sets shifted by two-point polarizations, **verify-late-margin.cpp** on the six size ranges proves the uniform strict lower bounds on \(mF\) in the table. The exceptional sets listed here use integer binary encodings; bit 0 has mask 1.

| Shape | Strict lower bound for \(mF\) |
|---|---:|
| Every noncritical shape other than the three below | 69/1000 |
| \(E_{12}\): full radius-one ball plus the point 3 | 34/1000 |
| \(E_{18}\): bit 0 free, bits 1–8 in a radius-one ball, bit 9 fixed to zero | 45/1000 |
| \(E_{19}=E_{18}\cup\{512\}\) | 34/1000 |

At \(m=44\) the check uses the stronger target \(J(A,p)-(4+\lambda)C\), extending to all \(m>44\) by uniform-subset concavity. For the checks with \(t=4+\lambda(1-16/m)\le0\), use \(J\ge0\) for \(m=1\), and \(J\ge C\) for \(m\ge2\). The latter follows by representing the uniform cell law as a uniform mixture of laws on two-point subsets: observing a coordinate on which the two points differ gives \(C\) for each such subset. The rest of the exact fixed-point test is as described in **band-proof.md**, with the indicated margin added before testing. See **late/*.log**.

The estimates extend to uncompressed cells, with the low margins needed only for actual isometric copies of the three exceptions. The key is a sharper version of the inverse-compression calculation in **partition-extension.md**. Suppose a single allowed compression maps a cell to a known target shape \(S\) up to isometry. Let \(X\) be the set of singly occupied reflection pairs on the preferred side of \(S\), and \(X_+,X_-\) the nonempty opposite orientations they came from, if the compression is not simply an isometry. With \(g_y=|S|P_S(y)\) and \(\Delta_x(y)=K_p(y,x)-K_p(y,\sigma x)\), the same pairwise binary-entropy calculation gives
\[
 |S|\Delta H \ \ge\ \sum_{x\in X_+,z\in X_-}w_{xz},\qquad
 w_{xz}=\sum_{\text{preferred }y}\frac{2\Delta_x(y)\Delta_z(y)}{g_y+g_{\sigma y}} .
\]
Rather than a single cap on the denominator, **inverse-strong.py** keeps the individual pair denominators. Over the containing interval \([20201/65536,5/16]\), it upper-bounds each kernel in the denominator by substituting the largest possible values of \(p,1-p\) separately, and lower-bounds each numerator difference by substituting the smallest possible \(p,1-p,1-2p\) into the positive product \((1-2p)p^d(1-p)^{10-r-d}\), with \(r=1\) or 2 reflected bits. Products are rounded outward to an integer scale \(2^{52}\). The program checks all conjugate reflections up to permutations within coordinates of the given shape (equivalence classes are interchangeable by inspection of the masks). If there are \(u\) singly occupied pairs and the smaller side of a cut has size \(k\), its weight is at least both \(k(u-k)w_{\min}\) and \(k\deg_{\min}-k(k-1)w_{\max}\). These inequalities apply to the exact lower-bound weight matrix, not to approximate entropy values. Taking the maximum of the bounds and then the minimum over \(1\le k\le u/2\) gives a lower bound for every nontrivial orientation pattern.

The resulting verified lower bounds on \(m\Delta H\) exceed \(1/10\) for each critical type, \(36/1000\) for \(E_{12}\) and \(E_{19}\), and \(25/1000\) for \(E_{18}\). If a cell compresses to a special type but was not isometric to a special type of that size, use the last non-isometric compression in the sequence; its image is isometric to the final shape. The entropy improvement transfers to the total decrease by monotonicity. For the critical types, even their possible negative gap costs at most \(20\eta\) in the weighted \(mF\), so \(1/10-20\eta>69/1000\). For the three exceptions their low margins plus the verified improvement each exceed \(69/1000\). Thus the table is valid for *all original cells*, counting critical cells separately by their signed gap bounds.

## Compensating for the critical cells

Average \(F\) with weights \(m/1024\). If there are fewer than 64 nonempty cells, the affine benchmark itself exceeds \(4C\) by at least \(\lambda C/64>\eta\), since \(C\ge(1-2p)^2/2\) and \(p\le5/16\). The possible total gap loss is at most \(\eta\). Suppose there are exactly 64 cells. Cases are as follows.

- If every cell is critical, the tiling result in **critical-tiling.md** implies all are four-faces and the bound is an equality.
- If at least two cells are noncritical, the weighted sum of their unnormalized gains is \(>2(34/1000)>1024\eta=1/15\). This compensates for every possible negative critical gap even if all other mass is charged.
- If there is just one noncritical cell and it is none of the three exceptions, its unnormalized gain is \(>69/1000>1024\eta\), again sufficient.
- If the sole noncritical cell is \(E_{12}\) or \(E_{19}\), it is impossible by full-cube parity. The signed parity sum of a full ball is \(\pm9\), and that of an edge-ball or four-face is zero. The respective exceptions have signed sums of absolute values 8 and 1, which cannot cancel a multiple of 9.
- If the sole noncritical cell is \(E_{18}\), let the counts of 11-point and 20-point critical cells be \(a,b\). The volume and cell counts force \(a=4q+2\), \(b=5q+2\), with the number of four-faces \(59-9q\), and integer \(q\ge0\). The exact shell certificates below imply \(q\le4\), so the total number of points in the two potentially negative cell types is at most \(11\cdot18+20\cdot22=638\). Their combined unnormalized deficit is at most \(638\eta<45/1000\), paid for by the \(E_{18}\) cell alone.

The final shell certificates are in **single18-duals.json**, checked by **verify-single18.py**. Isometrically fix \(E_{18}\) in the displayed position. There is at least one full ball since \(a=4q+2>0\). Its center is at bit 0 equal to zero after a free-coordinate reflection, with its set bits in the eight active coordinates moved first by permuting those coordinates, and its fixed-coordinate bit either zero or one. The verifier covers all 13 relative positions that give disjointness. For each such pair the same nonnegative shell relaxation as in **critical-tiling.md** has type right-hand side \((1,2,59)\) (one full ball already fixed); the \(q\)-column again has coefficients \((-4,-5,9)\). The integer dual upper-bounds \(q<5\) or yields a Farkas contradiction, verified against every eligible remaining tile. No floating-point numerical decisions are used in checking the archived certificates.

Thus in all scenarios the conditional information is at least \(4C\), so \(I(U;Y)=10C-I(X;Y\mid U)\le6C\).

## Reproduction

Compile **verify-late-margin.cpp** with **g++ -O3 -std=c++17 -DTANGENT**; for each of the six size bands use trailing arguments **20201 20317 16 141926 100000**. Run **python3 late-critical.py**, **python3 inverse-strong.py**, **python3 verify-single18.py**, and the earlier exact verifiers referenced above. All need enabled assertions. Their archived log outputs are in the bundle. The proof is a computer-assisted, reproducible certification; it has not had external peer review.
