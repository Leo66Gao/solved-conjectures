# Magnetic rings: the exceptional fluxes

Supplement to Theorem 6 of the paper (the generic-support result). This
note gives the exact, rather than almost-everywhere, answer for a
nearest-neighbor ring. Let n ≥ 3, ζ = exp(2πi/n), and H = hT + conjugate(h)T⁻¹
with h any nonzero complex number. The overall size of h only rescales time.

If n has two different prime factors, the generic-support upper bound
proves that no nonzero translation has pretty good state transfer (PGST),
for **any** h. Suppose n = pᵃ, set K = Q(ζ), P = (1−ζ) in O = Z[ζ],
and write v for its normalized valuation v(1−ζ)=1. Write
η = conjugate(h)/(hζ). The only candidates are multiples of n/p. The
following classifies whether all p candidates work or just the identity:

1. If η ∉ K, all p candidates work.
2. If η ∈ K, let y₀ = 1+η unless η=−1, in which case take
   y₀ = ζ−ζ⁻¹. All p candidates work precisely when v(y₀) is odd.
   If v(y₀) is even, only the identity works.

For odd p the second test simplifies: all p work exactly when η is −1 in
the residue field Fₚ. The norm-one number η is a local unit, with residue
either +1 or −1. The statement at p=2 uses the valuation test as written.

**Proof.** The phase-relation test in the main paper says that the
translation n/p works iff p divides f′(1) for every integer polynomial
f with f(1)=0 and Re(h f(ζ))=0. The degree may be arbitrary, since
reducing modulo Xⁿ−1 does not change f(ζ), f(1), or f′(1) modulo n.
Write f=(X−1)g. Then f′(1)=g(1) reduces to g(ζ) modulo P, since
O/P=Fₚ. Consequently an obstruction is a y=g(ζ) in O of valuation 0
with Re(h(ζ−1)y)=0. This last equation is y = η conjugate(y).

A nonzero solution requires η∈K. Conversely y₀ above is always a
nonzero solution if η∈K: η conjugate(η)=1 and the exceptional choice
is nonzero purely imaginary. Every nonzero solution in K has the
form y₀r with nonzero r∈K⁺ (the real subfield), by division. Its
valuation is v(y₀) modulo 2: the rational prime p is totally ramified in
K and the real subfield K⁺ has index 2, so the local ramification index
of K/K⁺ is 2, and every element of K⁺ has even valuation. Conversely
t=(1−ζ)(1−ζ⁻¹)∈K⁺ has v(t)=2; powers of t realize every even
valuation. If v(y₀) is even we can multiply by t^{-v(y₀)/2} to produce
a solution of valuation zero. Multiplying by an integer prime to p to
clear any remaining denominator makes this solution integral, because P
is the unique prime of O above p (equivalently, factor the denominator
ideal away from P and multiply by suitable powers of the corresponding
rational primes). The resulting algebraic integer lies in O=Z[ζ], and hence is a value
g(ζ). There is an obstruction exactly in this case. The candidate group
has prime order, so failure at its generator eliminates all its nonzero
elements. The ramification facts used here also follow immediately from
the Eisenstein polynomial Φ_{pᵃ}(X+1) and multiplicativity of ramification
indices in the degree-two tower.

For odd p: conjugation is trivial modulo P. A unit solution would
force η≡1. Conversely if η≡1 then y₀=1+η has residue 2 and is
already a unit. This proves the simpler criterion.

**Examples and checks.** For odd prime powers, real h permits only identity,
while pure imaginary h admits all p targets (η≡−1). For n a power of
two ≥4 and h=1, η=ζ⁻¹ and v(1+ζ⁻¹)=1, so the antipode is reachable.
More generally if h∈K, a convenient alternative solution is
conjugate(h)(1+ζ⁻¹). Its valuation is v(h) for odd p and v(h)+1 for
p=2. In arbitrary phase h the classification is invariant under
h↦hζʲ: this changes η by ζ^{-2j}, and multiplies a solution by the local
unit ζ^{-j}. The test concerns limits in time, not good finite-time upper
bounds.

**Context.** For the unweighted real case see Pal–Bhattacharjya,
https://arxiv.org/abs/1607.03598; for the oriented prime case see
Cameron et al., https://arxiv.org/abs/1310.3885. The classification above
is not required for the exact unit-gain UPST theorem.
