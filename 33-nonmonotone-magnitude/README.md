# Results from the metric-magnitude investigation

**Leo Gao** · AI-assisted research · Independent review and priority assessment pending

1. **[Nine points suffice](NINE_POINTS.md).** An explicit strict-negative-type metric drops from 1.4187004613 to 1.3882616818 when its scale doubles. This answers the published question of whether fewer than fourteen points suffice; it does not identify the minimum. Included are a short tensor/Schur proof, an exact finite certificate and a scaling family.
2. **[Obstruction below nine](TWO_DISTANCE.md).** At most eight points with only two distinct nonzero distances can never give a counterexample, for any real ratio. All 501 proper nonsingleton subsets of the unperturbed nine-point witness are also strictly monotone.
3. **[Finiteness phase transition](PHASE_TRANSITION.md).** A countable compact strong-negative-type space of zero box dimension has infinite magnitude at every scale up to and including 1, but finite magnitude above. The blowup is asymptotic to $(\log 2)/(2\log t)$. A different construction includes the critical scale in the finite range.
4. **[Small-scale cubic obstruction](CUBIC_OBSTRUCTION.md).** The cubic degeneracy used by the split-cube construction cannot occur in a base with seven or fewer points. This does not establish the minimum.
5. **[Multiscale consequences](MAGNITUDE.md).** One strong-negative-type compact space with finite magnitude everywhere has unbounded relative declines between asymptotically equal scales at infinity. A separate Ahlfors-regular construction realizes repeated arbitrarily large fixed drops at any chosen positive dimension.

**Fast checks:** Run `python verify_nine.py`, `python verify_phase.py`, `python verify_degree_bound.py`, and `python verify_cube_deletions.py`. They use only the standard library. For the separate, exhaustive ratio-2 census, compile `enumerate_graphs.cpp` and pipe its output into `python verify_two_distance.py`. The extra `verify.py` is an exact interval check for Pendyala's 14-point seed, not a priority claim for that example. The main analytic results do not depend on numerical optimization, asymptotic numerical sampling, or graph enumeration software outside this folder.

**Limits:** The minimum number of points in the unrestricted dilation-monotonicity problem lies between 4 and 9 on the sources located here. Neither lower bound research nor independent priority searches establish unrestricted nine-point optimality.
