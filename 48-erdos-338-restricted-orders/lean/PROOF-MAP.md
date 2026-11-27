# Proof map for the checked original questions

1. **Necessity.** A sufficiently large natural can be chosen in each
   residue of every positive modulus. Its restricted representation is a
   finite subset sum. The final statement therefore implies modular
   completeness directly.
2. **Uniform local completeness.** Ordinary order and modular completeness
   produce a uniform bound on the number of elements required for a
   subset-sum residue witness, independent of the modulus. The Lean proof
   in `UniformLocal.lean` obtains a single cylinder of fresh modular
   approximations by finite cylinder refinement and descending rank,
   then adds bounded modular correctors.
3. **Positive restricted density.** `HHPFinite.lean` converts ordinary
   coverage into a positive linear lower bound for the number of finite
   restricted sums in long prefixes. It promotes one summand at a time
   into a protected, distinct part of a witness. The bounded loss per
   promotion and bounded shift of the prefix are proved in finite counts.
4. **Popular sums and robust mixed layers.** The finite estimates in
   `PopularityCounting.lean` and `CollisionBridge.lean` count pairs of
   small restricted sums and give a greedy packing of sufficiently many
   disjoint witnesses. `RobustLayers.lean` chooses a fixed rank-dependent
   number of copies of sets of popular sums. Their combined prefix counts
   eventually exceed twice the prefix length, and disjoint witnesses
   can be lifted even after any fixed bounded deletion.
5. **Mixed arithmetic progression.** `MixedDyson.lean` generalizes
   simultaneous Dyson counting to a receiver and finitely many donor sets.
   `MixedStable.lean` derives a system with controlled loss of prefix mass,
   all donors divisible by one positive step, and a long progression in
   the receiver with that step. `CoinBox.lean` combines the individual
   steps by a finite Bézout argument. `DilationCount.lean` and
   `Compression.lean` divide by the common step, retaining prefix mass
   greater than one. `MixedWindow.lean` turns the normalized long block
   and this surplus into eventual coverage; `FiniteRay.lean` and
   `ListMixedBridge.lean` recover an eventual residue class in the
   original mixed sumset. No mixed Kneser theorem is assumed.
6. **Global lifting.** Each modular corrector from step 2 has uniformly
   bounded support. Use the robust progression from steps 4–5 after
   deleting exactly that support. Their disjoint union represents each
   sufficiently large integer. The checked endpoint is
   `Erdos338.erdos_338`.
7. **Variants.** Preserving ordinary basis status after every finite
   deletion implies modular completeness, proved with the surviving
   infinite residue classes. The exact-common-order version follows by
   selecting the least-order witnesses. The equality variant instead
   invokes the independent `Erdos338/Equality.lean` theorem and handles
   orders below two directly.


## Uniform bound in terms of ordinary order

The existence argument alone does not give a uniform numerical bound:
the modular corrector budget in its uniform-local step may depend on the
basis. The proof in `Full338.lean` supplies a separate route.

1. `HHPFinite.lean` makes its lower density constant explicit and uniform
   at ordinary rank h. `UniformPopularity.lean` forms a finite schedule of
   rank-dependent packing thresholds and numbers of copies, all depending
   only on h and that constant. At every sufficiently large scale some
   scheduled layer supplies enough prefix mass.
2. `RecurrentLayers.lean` chooses the first infinitely active layer and
   drops the earlier layers. The remaining mixed sumset has the required
   eventual count surplus. It contains an eventual progression, with no
   control needed yet on its modulus.
3. `ModulusShrink.lean` reduces the modulus using the recurrent layer's
   residue density and finite cyclic Kneser. Extra copies of that layer
   cover the generated subgroup of residues. The smaller modulus is
   bounded by the number of reserved copies.
4. `RecurrentLayers.lean` and `Full338.lean` lift the mixed representation
   through the disjoint-support packing schedule. The new modulus is
   small enough that it can pay for both the residue correctors and all
   prior chosen supports. Both the rank cost and new modulus are uniformly
   bounded by the fixed schedule.
5. `BoundedCatalogue.lean` uses modular completeness, already necessary
   for finite restricted order. A shortest residue corrector uses fewer
   labels than the reduced modulus, so it can be deleted during the
   progression lift and added back without collisions.

This is an explicit, fully checked qualitative uniform bound, not an
audit of the sharper growth rate in the separate paper.
