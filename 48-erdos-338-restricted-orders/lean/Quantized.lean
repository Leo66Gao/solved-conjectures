import Samples
import Mathlib.Algebra.Order.Field.Basic

/-! A finite uniform accuracy (depending on k but not the basis, target,
or number of representations) suffices for each scalar ordinary observation.
This is not a claim of efficient sampling at high multiplicity.
-/
namespace Erdos338.Thinning
open Polynomial

private theorem sum_monomials_eval (F : List (List ℕ)) (x : ℚ) :
    (((F.map (fun w => (X : Poly)^w.toFinset.card)).sum).map (Int.castRingHom ℚ)).eval x =
       (F.map (fun w => x^w.toFinset.card)).sum := by
  induction F with
  | nil => simp
  | cons a t ih => simp [ih]

noncomputable def scaledNumerator (A : Set ℕ) (k n : ℕ) (i : Fin (k+1)) : ℕ :=
  ((fiber A k n).map (fun w => (i.val+1)^w.toFinset.card * (k+2)^(k-w.toFinset.card))).sum

private theorem scale_fiber (k : ℕ) (i : Fin (k+1)) (F : List (List ℕ))
    (hlen : ∀ w ∈ F, w.toFinset.card ≤ k) :
    (F.map (fun w => rate i ^ w.toFinset.card)).sum * (k+2 : ℚ)^k =
      (((F.map (fun w => (i.val+1)^w.toFinset.card * (k+2)^(k-w.toFinset.card))).sum : ℕ) : ℚ) := by
  induction F with
  | nil => simp
  | cons w t ih =>
    obtain ⟨hw,ht⟩ := List.forall_mem_cons.mp hlen
    simp only [List.map_cons,List.sum_cons,add_mul,ih ht,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one]
    congr 1
    have de : w.toFinset.card + (k-w.toFinset.card) = k := by omega
    have den : (k+2 : ℚ) ^ w.toFinset.card ≠ 0 := by positivity
    dsimp [rate]
    have deq : (k+2 : ℚ)^k = (k+2:ℚ)^w.toFinset.card * (k+2:ℚ)^(k-w.toFinset.card) := by
      rw [← pow_add,de]
    rw [div_pow, deq, ← mul_assoc, div_mul_cancel₀ _ den]

theorem observed_lattice (A : Set ℕ) (k n : ℕ) (i : Fin (k+1)) :
    observe A k n i * (k+2 : ℚ)^k = (scaledNumerator A k n i : ℚ) := by
  rw [observe,response_expansion,sum_monomials_eval]
  apply scale_fiber k i
  intro w hw
  rw [← ((mem_fiber A k n w).mp hw).1]
  exact List.toFinset_card_le _

/-- Distinct population-mean readings (across arbitrary bases and targets)
at the same panel coordinate are at least 1/(k+2)^k apart. -/
theorem separation (A B : Set ℕ) (k m n : ℕ) (i : Fin (k+1))
    (ltval : observe A k m i < observe B k n i) :
    observe A k m i + 1/(k+2:ℚ)^k ≤ observe B k n i := by
  let d : ℚ := (k+2:ℚ)^k
  have dp : 0 < d := by dsimp [d]; positivity
  have ht : observe A k m i * d < observe B k n i * d := mul_lt_mul_of_pos_right ltval dp
  have eA : observe A k m i * d = (scaledNumerator A k m i : ℚ) := observed_lattice _ _ _ _
  have eB : observe B k n i * d = (scaledNumerator B k n i : ℚ) := observed_lattice _ _ _ _
  rw [eA,eB] at ht
  have ord : scaledNumerator A k m i < scaledNumerator B k n i := by exact_mod_cast ht
  have hgap : (scaledNumerator A k m i : ℚ) + 1 ≤ scaledNumerator B k n i := by exact_mod_cast ord
  change observe A k m i + 1/d ≤ observe B k n i
  apply le_of_mul_le_mul_right _ dp
  rw [add_mul,div_mul_cancel₀ _ dp.ne', eA,eB]
  exact hgap

/-- Sub-lattice perturbations of actual ordinary means cannot alter any
reading. This is uniform in n, A, B, and the ordinary representation counts. -/
theorem same_observation_of_close (A B : Set ℕ) (k m n : ℕ) (i : Fin (k+1))
    (cl : |observe A k m i - observe B k n i| < 1/(k+2:ℚ)^k) :
    observe A k m i = observe B k n i := by
  have ranges := abs_lt.mp cl
  rcases lt_trichotomy (observe A k m i) (observe B k n i) with h|h|h
  · have := separation A B k m n i h; linarith
  · exact h
  · have := separation B A k n m i h; linarith

/-- A comparison/inference theorem for bases. Eventual closeness of ordinary
thinning means, at a precision depending only on the arity, transfers
restricted coverage in both directions without any witness correspondence. -/
theorem restrictedOrder_transfer (A B : Set ℕ) (h : ℕ)
    (close : ∃ N, ∀ n ≥ N, ∀ k ≤ h, ∀ i : Fin (k+1),
      |observe A k n i - observe B k n i| < 1/(k+2:ℚ)^k) :
    Erdos338.CatalogueAdapter.HasRestrictedOrder A h ↔
      Erdos338.CatalogueAdapter.HasRestrictedOrder B h := by
  obtain ⟨M,hM⟩ := close
  have same (n : ℕ) (hn : M≤n) (k : ℕ) (hk : k≤h) :
      observe A k n = observe B k n := funext fun i =>
        same_observation_of_close A B k n n i (hM n hn k hk i)
  rw [order_iff_fullResponse,order_iff_fullResponse,← panel_iff_response,← panel_iff_response]
  constructor
  · rintro ⟨N,hN⟩; refine ⟨max M N,fun n hn => ?_⟩
    obtain ⟨k,hk,ht⟩ := hN n (le_of_max_le_right hn)
    exact ⟨k,hk,by rwa [← same n (le_of_max_le_left hn) k hk]⟩
  · rintro ⟨N,hN⟩; refine ⟨max M N,fun n hn => ?_⟩
    obtain ⟨k,hk,ht⟩ := hN n (le_of_max_le_right hn)
    exact ⟨k,hk,by rwa [same n (le_of_max_le_left hn) k hk]⟩

#print axioms restrictedOrder_transfer
#print axioms observed_lattice
#print axioms separation
end Erdos338.Thinning
