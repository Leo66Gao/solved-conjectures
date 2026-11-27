import CatalogueAdapter
import CollisionBridge
import DensityBridge
import Erdos335.Density

/-!
# Catalogue integration for Erdős #338
The modular condition and its equivalence to finite restricted order are due to
Chen, Yang and Zhao (arXiv:2611.33191, Theorem 2). The finite-deletion result is
their Theorem 1. This intermediate build isolates the mixed progression input.
-/

open scoped BigOperators
namespace Erdos338.CatalogueAdapter

open Erdos338.Existence.Analytic Erdos338.Existence.CollisionBridge

/-- Reconcile the prefix-count convention of the density library with
the positive prefix count used by the popularity proof. -/
theorem count_eq_hits (P : Set ℕ) (n : ℕ) :
    Erdos335.count P n = hits P n := by
  classical
  change Erdos335.count P n = hits (fun x => x ∈ P) n
  rw [← prefix_card]
  unfold Erdos335.count positivePrefix
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  change (1 ≤ x ∧ x ≤ n) ∧ P x ↔ x < n+1 ∧ 0<x ∧ P x
  constructor
  · rintro ⟨⟨h₁,h₂⟩,hp⟩; exact ⟨by omega,by omega,hp⟩
  · rintro ⟨h₁,h₂,hp⟩; exact ⟨⟨by omega,by omega⟩,hp⟩

theorem weighted_count_eq (ss : List (Set ℕ)) (n : ℕ) :
    (ss.map (fun P => Erdos335.count P n)).sum = weight ss n := by
  simp only [count_eq_hits,weight]
  rfl

/-- Once the named mixed progression theorem is supplied by the kernel,
no other nonstandard premise is needed for the exact catalogue statement. -/
theorem catalogue_of_mixed_ray (mixed : MixedKneserRay) :
    ∀ A : Set ℕ, (∃ h, HasOrder A h) →
      ((∃ t, HasRestrictedOrder A t) ↔ answer A) := by
  apply statement_from_list_sufficiency
  rintro A ⟨h,ho⟩ hc
  exact (headline_reduction ho hhpDensity mixed (collisionBound A)).mpr hc

theorem basis_after_finite_removal_of_mixed_ray (mixed : MixedKneserRay)
    (A : Set ℕ) (robust : ∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) :
    ∃ t, HasRestrictedOrder A t := by
  have ho : ∃ h, HasOrder A h := by simpa using robust ∅ Set.finite_empty
  apply (catalogue_of_mixed_ray mixed A ho).mpr
  apply answer_iff_list.mpr
  intro g hg
  apply Erdos338.Growth.completeMod_of_finite_removal (A := A) ?_ hg
  intro D
  obtain ⟨h,hh⟩ := robust (D.toFinset : Set ℕ) D.toFinset.finite_toSet
  refine ⟨h,?_⟩
  obtain ⟨N,hN⟩ := ordinary_iff_list.mp hh
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨xs,hxs,hs,hl⟩ := hN n hn
  refine ⟨xs,fun x hx => ?_,hs,hl⟩
  have h := hxs x hx
  exact ⟨h.1,by simpa using h.2⟩

#print axioms catalogue_of_mixed_ray
#print axioms basis_after_finite_removal_of_mixed_ray

end Erdos338.CatalogueAdapter
