import CatalogueResult
import FiniteRay
import ListMixedBridge
import MixedStable

/-!
# Erdős #338: the finite restricted-order criterion

This is a Lean formalization of the mathematical solution by
Shi-Qiang Chen, Quan-Hui Yang, and Lilu Zhao (arXiv:2611.33191, Theorem 2).
The order and restricted-order predicates match Formal Conjectures.
The equality variant uses the separate rank-two criterion.
-/

namespace Erdos338

open CatalogueAdapter Existence.Analytic

private theorem stableFamily : FiniteRay.StableFamily := by
  intro k A B hA hB den L hL
  exact MixedStable.mixed_progression_core A B hA hB den L hL

theorem mixedKneserRay : MixedKneserRay := by
  apply mixedKneserRay_of_fin
  intro k A B hA hB den
  exact FiniteRay.eventual_ray_of_stabilization stableFamily A B hA hB den

/-- Chen–Yang–Zhao's criterion: every residue modulo each positive
modulus occurs among finite subset sums of `A`. -/
def erdos_338.answer : Set ℕ → Prop := CatalogueAdapter.answer

/-- This is the exact existence biconditional of the public catalogue. -/
theorem erdos_338 : ∀ A : Set ℕ, (∃ h, HasOrder A h) →
    ((∃ t, HasRestrictedOrder A t) ↔ erdos_338.answer A) :=
  catalogue_of_mixed_ray mixedKneserRay

theorem erdos_338.variants.basis_after_finite_removal
    (A : Set ℕ) (robust : ∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) :
    ∃ t, HasRestrictedOrder A t :=
  basis_after_finite_removal_of_mixed_ray mixedKneserRay A robust

theorem erdos_338.variants.same_order_after_finite_removal (A : Set ℕ)
    (same : ∃ h : ℕ, ∀ F : Set ℕ, F.Finite → basisOrder (A \ F) = (h : ℕ∞)) :
    ∃ t, HasRestrictedOrder A t := by
  obtain ⟨h,hh⟩ := same
  exact erdos_338.variants.basis_after_finite_removal A
    (fun F hF => ⟨h, hasOrder_of_basisOrder_eq (hh F hF)⟩)

noncomputable def erdos_338.variants.eq_order.answer : Set ℕ → Prop :=
  CatalogueAdapter.equalityAnswer

theorem erdos_338.variants.eq_order (A : Set ℕ) (base : ∃ h, HasOrder A h) :
    restrictedOrder A = basisOrder A ↔ erdos_338.variants.eq_order.answer A :=
  CatalogueAdapter.equality_variant A base

#print axioms erdos_338
#print axioms erdos_338.variants.basis_after_finite_removal
#print axioms erdos_338.variants.same_order_after_finite_removal
#print axioms erdos_338.variants.eq_order

end Erdos338
