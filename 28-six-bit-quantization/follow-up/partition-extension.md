# A partition constraint extends 10-to-6 optimality past the single-cell obstruction

**Theorem.** For uniform \(X\in\{0,1\}^{10}\), independent Bernoulli(\(p\)) noise on each coordinate, and every deterministic \(U=f(X)\) taking at most 64 values,
\[
 I(U;X\oplus Z)\le6(1-h_2(p))\qquad\text{for all }0\le p\le79/256=0.30859375.
\]
The interval includes a range in which no independent-cell affine certificate in the cell cardinality can work: in **band-proof.md**, the ball and edge-ball cells prove that such a certificate is impossible from \(20202/65536\) up to (but not including) \(1/2\). Neither the result nor the obstruction rules out a six-bit counterexample at larger crossover.

## A stable gap certificate

The independent-cell certificate already covers \(0\le p\le20201/65536\). Work in nats on the remaining interval \(P=[20201/65536,20224/65536]\). Put \(C=\ln2-h(p)\), \(\lambda=141909/100000\), \(\gamma=1/64\), \(\eta=\gamma/1024=1/65536\), and define the cell gap
\[
 F(A,p)=J(A,p)-[4+\lambda(1-16/m)]C,\qquad m=|A|.
\]
The critical geometric types are (i) a full radius-one ball with \(m=11\), (ii) a free bit times a radius-one ball with \(m=20\), and (iii) a coordinate four-face with \(m=16\). All their isometric copies are included.

**Critical cells.** The four-face has \(F=0\) identically. For the ball and edge-ball the exact integer shell enumerator **verify-gaps.py** proves \(F>-\eta\) throughout \(P\): if \(t=4+\lambda(1-16/m)\), then \(F=(10-t)C-D\) with noisy-output divergence \(D\) to uniform. On a closed subinterval, use the increasing-noise monotonicity of both quantities to lower-bound this expression by \((10-t)\) times the capacity lower bound at the right endpoint minus the divergence upper bound at the left. The log records 447 and 300 successful subintervals respectively.

**Other shifted cells.** The exact fixed-point program **verify-partition-gap.cpp** runs the same directed test described in **band-proof.md**, but checks \(mF>\gamma\) and skips the three critical shapes. There is only one shifted orientation of each: stability under down-compressions forces the ball and edge-ball centers to have zeros in every nonfree coordinate (otherwise their bit means would have the wrong sign), and stability under coordinate shifts puts free coordinates first (occurrence counts are nonincreasing with the coordinate index). Thus the skipped masks are exactly the three indicated isometry types among shifted sets. Sizes \(m\le44\) are handled simultaneously and all six size groups pass the whole band in one interval. The check at size 44 is stronger, replacing \(t\) by \(4+\lambda\); the concavity and uniform-subset argument yields \(mF>\gamma\) for all \(m>44\). For nonpositive \(t\), the code instead uses \(J\ge0\) plus the exact positive capacity lower bound at the right endpoint. See **part/*.log**.

## Quantitative inverse polarization

It remains essential to control noncritical cells that compress to a critical one. Merely knowing strict entropy improvement would not quantify a margin.

Let a two-point compression with reflection \(\sigma\) map a size-\(m\) set to a critical shape \(S\), using only cube-isometric conjugations to identify the critical shape with the canonical orientation. If the operation is not just the identity or a global isometry, then its singly occupied orbits originally occurred in both orientations. Index the preferred-side points in the singly occupied pairs of the compressed shape by \(X\), and split \(X=X_+\sqcup X_-\) into the two original orientations. Both subsets are nonempty. For preferred-side output \(y\), write
\[
 R_\pm(y)=\sum_{x\in X_\pm}(K_p(y,x)-K_p(y,\sigma x))\ge0.
\]
In the output pair \(y,\sigma y\) the mass sum \(s_y\) is fixed, while its absolute mass difference changes from \(|R_+-R_-|/m\) to \((R_++R_-)/m\). The entropy improvement on that pair is at least \(2R_+(y)R_-(y)/(m^2s_y)\). This follows from the positive even power series for the binary deficit \(C\) as a function of correlation, keeping just its quadratic term; all remaining changes are nonnegative. Fixed output points contribute zero.

For all \(p\in P\), the critical normalized masses \(g_y=mP_S(y)\) have maximum at most \(1/5\). Each canonical set is a downset, so the convolution stays monotone in each bit and is maximized at zero. The maximum of the ball output is \((1-p)^{10}+10p(1-p)^9\), and that of the edge-ball has the same formula with 9 replacing 10. The four-face value is \((1-p)^6\). All decrease with \(p\) and are below \(1/5\) already at \(p=3/10\). Thus \(s_y\le2/(5m)\), giving
\[
 m\,\Delta H\ \ge\ 5\sum_{x\in X_+,z\in X_-}\sum_{y\ {\rm preferred}}
 [K_p(y,x)-K_p(y,\sigma x)] [K_p(y,z)-K_p(y,\sigma z)] .
\]
The inner sum is \(K_q(x,z)-K_q(x,\sigma z)\) for \(q=2p(1-p)\), by reflecting to the other output side and applying the noise semigroup. On the chosen side the reflected positions agree for \(x,z\); reflection changes either one or two bits, say \(r\), raising their mutual distance by \(r\). At \(d=d(x,z)\) the difference is \((1-2q)q^d(1-q)^{10-r-d}\) for either \(r=1\) or 2.

On \(P\subseteq[3/10,31/100]\) we have \(1-2q=(1-2p)^2\ge(19/50)^2\), \(q\ge21/50\), and \(1-q\ge57/100\). The minimum of the resulting rational lower bound for an eligible reflection is attained at the maximum distance of a pair in \(X\). Also \(|X_+||X_-|\ge|X|-1\). Enumerate the ten bit reflections and the transpositions of two coordinates, with or without complementing both swapped coordinates; this covers every cube-isometric conjugation of the allowed compression reflections. A reflection that places singly occupied pairs of \(S\) on both sides is not eligible as a compression output. The other cases with at least two singly occupied orbits give rational margins explicitly verified by **verify-gaps.py**. The minimum weighted entropy improvement exceeds \(1/64\) for each of the three critical shapes.

Now follow any compression sequence from a cell to its final stable family. If the result is noncritical, its verified margin is inherited by the original cell. If the result is critical but the original is noncritical, consider the last compression that is not a global isometry or identity. Its result is an isometric critical shape; the quantitative bound applies there and is inherited by the total entropy decrease. Consequently every cell satisfies \(F>-\eta\) (or \(F=0\) for a four-face), and each noncritical cell satisfies
\[
 F>-\eta+\gamma/m .
\]

## Averaging with a genuine partition

If there are fewer than 64 nonempty cells, the mean lower bound gains at least \(\lambda C/64\) over \(4C\), while losing at most \(\eta\) from the cell gaps. The gain is strictly larger: use \(C\ge(1-2p)^2/2\ge(19/50)^2/2\) and \(\lambda>1\). If there are 64 cells and any is noncritical, its additional \(\gamma/m\) is averaged with weight \(m/1024\), exactly canceling the total possible deficit \(\eta\); the strict bounds give a strictly positive result. Finally, if all 64 cells are critical, **critical-tiling.md** with the exact shell duals proves that every cell is a coordinate four-face, giving equality. Thus \(I(X;Y\mid U)\ge4C\) and \(I(U;Y)\le6C\) in all cases.

## Reproduction

Compile **verify-partition-gap.cpp** with **g++ -O3 -std=c++17 -DTANGENT**. Run it with first and last size bands \((1,19),(20,23),(24,34),(35,39),(40,43),(44,44)\), followed by the five arguments **20201 20224 16 141909 100000**. Run **python3 verify-gaps.py** and **python3 tiling-obstruction.py**. All require enabled assertions. The earlier bands and their independent-cell obstruction are described separately in **band-proof.md**. No solver is required to check the archived tiling certificates.
