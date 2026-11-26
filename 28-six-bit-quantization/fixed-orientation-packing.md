# A packing obstruction for the 12-bit candidate cell

**Leo Gao · AI-assisted research note.**

Let (A) contain the zero word, the twelve unit words, the forty-five pairs among coordinates 0–9, and the six pairs joining coordinate 10 to a coordinate in 0–5. This is exactly the first stored shape in `good-n12.txt`. It has 64 elements and squared conditional bias (771/128>6), but one cannot partition the 12-cube into translates of this cell at a fixed coordinate orientation.

Suppose disjoint translates are indexed by centers (t). Split them by coordinates 10 and 11. Within each of the four classes the projections of the centers to coordinates 0–9 have minimum distance at least five: (A) contains the whole radius-two ball on those ten coordinates, and the XOR of two ball elements can have any weight at most four. Append a parity coordinate to the projected centers; the resulting binary code has length 11 and minimum distance at least six. If it has (M) words, summing all unordered pair distances gives
[
6inom M2 le 11M^2/4.
]
The right side follows by separately bounding the number of differing pairs in each binary coordinate. Hence (Mle12), so there are at most 48 disjoint translates in total, fewer than the 64 needed for a partition. No linearity of the centers is assumed. Mixing different shapes or varying the coordinate orientation remains open.
