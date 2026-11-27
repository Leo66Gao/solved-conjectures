import Thinning
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Basic

/-! # A finite panel of actual retention probabilities
The criterion below does not take a polynomial or a support list as input.
It compares the expected numbers of ordinary representations at k+1
fixed subunit retention rates against lower-degree predictions. -/
namespace Erdos338.Thinning
open Polynomial
open Erdos338.CatalogueAdapter

noncomputable def rate {k : ℕ} (i : Fin (k+1)) : ℚ := (i.val+1 : ℚ)/(k+2 : ℚ)

private theorem rate_injective {k : ℕ} : Function.Injective (@rate k) := by
  intro i j H
  apply Fin.val_injective
  have hd : (k+2 : ℚ) ≠ 0 := by positivity
  unfold rate at H
  have h := (div_left_inj' hd).mp H
  exact Nat.cast_injective (add_right_cancel h)

theorem rate_range {k : ℕ} (i : Fin (k+1)) : 0 < rate i ∧ rate i < 1 := by
  have H : (i.val : ℚ) < (k : ℚ) + 1 := by exact_mod_cast i.isLt
  have hd : (0:ℚ) < k+2 := by positivity
  constructor
  · unfold rate; positivity
  · unfold rate; rw [div_lt_one hd]
    linarith

noncomputable def observe (A : Set ℕ) (k n : ℕ) (i : Fin (k+1)) : ℚ :=
    ((response A k n).map (Int.castRingHom ℚ)).eval (rate i)

/-- The data are k+1 ordinary mean counts. The test is a finite linear
system of interpolation with degree strictly less than k. -/
def LowFit {k : ℕ} (reads : Fin (k+1) → ℚ) : Prop :=
    ∃ Q : ℚ[X], Q.degree < (k : WithBot ℕ) ∧ ∀ i, Q.eval (rate i) = reads i

theorem response_coeff_counts (A : Set ℕ) (k n j : ℕ) :
    (response A k n).coeff j =
    (((fiber A k n).countP (fun w => decide (w.toFinset.card = j)) : ℕ) : ℤ) := by
  rw [response_expansion,coeff_sum_powers]

private theorem panel_degree (A : Set ℕ) (k n : ℕ) :
    ((response A k n).map (Int.castRingHom ℚ)).natDegree ≤ k := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [Polynomial.coeff_map,response_coeff_counts]
  have cnt : (fiber A k n).countP (fun w => decide (w.toFinset.card=j)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro w hw
    have one := (mem_fiber A k n w).mp hw |>.1
    have two := List.toFinset_card_le w
    simp only [decide_eq_true_eq]
    omega
  simp [cnt]

theorem fit_iff (A : Set ℕ) (k n : ℕ) :
    LowFit (observe A k n) ↔ (response A k n).coeff k = 0 := by
  let P := (response A k n).map (Int.castRingHom ℚ)
  have ub : P.natDegree ≤ k := panel_degree A k n
  constructor
  · rintro ⟨Q,hQ,hr⟩
    have hQc : Q.natDegree ≤ k := Polynomial.natDegree_le_iff_degree_le.mpr hQ.le
    have he : Q=P := Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q P rate_injective hr (by simp; omega)
    have hz := (Polynomial.degree_lt_iff_coeff_zero Q k).mp hQ k le_rfl
    rw [he] at hz
    simpa [P,Polynomial.coeff_map] using hz
  · intro hz
    refine ⟨P,(Polynomial.degree_lt_iff_coeff_zero P k).mpr ?_, fun _ => rfl⟩
    intro j hj
    rcases eq_or_lt_of_le hj with rfl|hj'
    · simp [P,Polynomial.coeff_map,hz]
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp ub j hj'

def VisiblePanel (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, ∃ k ≤ h, ¬ LowFit (observe A k n)

theorem panel_iff_response (A : Set ℕ) (h : ℕ) : VisiblePanel A h ↔ FullResponse A h := by
  have obs (k n : ℕ) : ¬ LowFit (observe A k n) ↔ 0 < (response A k n).coeff k := by
    rw [fit_iff,response_coeff_counts]
    simp
  simp_rw [VisiblePanel,FullResponse,obs]

/-- Exact ordinary order h is the only hypothesis. On the right are only
fixed-rate mean ordinary counts and independent polynomial interpolation. -/
theorem equal_orders_iff_ordinary_thinning_panel (A : Set ℕ) (h : ℕ)
    (ordinary : HasOrder A h ∧ ∀ k<h, ¬ HasOrder A k) :
    (HasRestrictedOrder A h ∧ ∀ k<h, ¬ HasRestrictedOrder A k) ↔ VisiblePanel A h :=
  (exact_order_iff_fullResponse A h ordinary.1 ordinary.2).trans (panel_iff_response A h).symm

#print axioms equal_orders_iff_ordinary_thinning_panel
#print axioms fit_iff
#print axioms rate_range
end Erdos338.Thinning
