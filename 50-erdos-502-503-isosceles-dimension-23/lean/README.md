# Dimension-23 geometry: Lean 4 proof components

Lean 4 proves the **278-point isosceles lower bound in dimension 23** with
an explicit construction. It also checks the abstract binary rank/refinement
obstruction used in the [dimension-23 paper](../). The binary hypotheses have
not yet been derived from an arbitrary Euclidean two-distance set in Lean,
so this is **not** a full Lean proof of the maxima or a resolution of the
all-dimensional Erdős problems.

- `ModFour.lean` checks the binary digit identities and their finite-sum
  expansion, by kernel reduction and induction.
- `BinarySaturation.lean` proves both the identity-Gram rank bound and the
  quadratic contradiction at saturation. The sum of the evaluation vectors
  has the same pairing values as the special basis vector, so equality of
  feature dimension forces the vectors to coincide. Their quadratic values
  differ in dimension 278.
- `Rank23.lean` proves `Erdos23.dimension23_at_most_277` for any supplied
  quadratic feature certificate of the stated lattice ranks. It restricts
  a purported larger certificate to 278 evaluations and then excludes it.
- `QuadraticFeatures.lean` constructs the polar form from products of
  linear coordinates; it does not assume the polarization law. The
  arithmetic conditions on actual lattice evaluation vectors remain inputs.
- `Axis.lean` proves the centre-and-poles construction in a real
  inner-product space. A supplied injective 275-point spherical
  two-distance family with a norm-matched orthogonal pole yields 278
  distinct isosceles points.

- `GolayCore.lean` constructs the punctured binary Golay code, checks its
  weights and the 253 weight-seven words by Lean kernel reduction, and proves
  the intersection law using XOR closure. It realizes the 276 equiangular
  vectors in `EuclideanSpace ℝ (Fin 23)`, derives the 275-point McLaughlin
  core, and applies `Axis` to it. The unconditional theorem is
  `Erdos23.exists_isosceles_278_fin23`.

The remaining work for the full formalization is the bridge from actual
integer distance lattices to the certificate, the distance-ratio reduction
and geometric upper bounds, and the separate 277-point two-distance
construction. The eight other dimensions from the paper are outside this
Lean supplement.

Run `bash verify.sh` with Lean/Lake 4.34.0, Git and Bash. It pins Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`, builds into a fresh temporary
directory, and kernel-replays only these modules against their pinned
dependencies. For an existing dependency checkout, set `MATHLIB_ROOT`
to it, `LEAN_LAKE_ROOT` to its containing Lake workspace, and
`SKIP_CACHE_DOWNLOAD=1`. See the included build record.

The finite computations use `decide`, not `native_decide`. The build record
shows the axioms and independent kernel replay.
