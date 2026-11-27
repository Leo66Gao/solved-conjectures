import CatalogueResult
import Mathlib.Tactic

/-! Ordinary set sums agree with the list formulation used by the
checked robust packing proof. -/
open scoped Pointwise

namespace Erdos338.Existence.Bounded
open Erdos338.Existence.Analytic

def fillsSet (ss : List (ℕ → Prop)) : Set ℕ := {n | Fills ss n}

theorem fillsSet_nil : fillsSet [] = {(0:ℕ)} := by rfl

theorem fillsSet_cons (P : ℕ → Prop) (ss : List (ℕ → Prop)) :
    fillsSet (P::ss) = ({x | P x} : Set ℕ) + fillsSet ss := by
  ext x
  change (∃ a b : ℕ, P a ∧ Fills ss b ∧ a+b=x) ↔ _
  exact ⟨fun ⟨a,b,ha,hb,h⟩ => ⟨a,ha,b,hb,h⟩,
    fun ⟨a,ha,b,hb,h⟩ => ⟨a,b,ha,hb,h⟩⟩

theorem fillsSet_append (ss tt : List (ℕ → Prop)) :
    fillsSet (ss++tt) = fillsSet ss + fillsSet tt := by
  induction ss with
  | nil =>
    rw [List.nil_append,fillsSet_nil]
    ext x
    constructor
    · intro hx
      exact ⟨0,by simp,x,hx,by simp⟩
    · rintro ⟨a,ha,b,hb,he⟩
      have ea : a=0 := by simpa using ha
      change a+b=x at he
      have be : b=x := by omega
      exact be ▸ hb
  | cons P ss ih =>
    rw [List.cons_append,fillsSet_cons,fillsSet_cons,ih,add_assoc]

theorem fills_repeated {C : Set ℕ} (c : ℕ → Set ℕ)
    (c0 : c 0 = {0}) (cs : ∀ i, c (i+1) = c i + C) (L : ℕ) :
    fillsSet (List.replicate L (fun n => n∈C)) = c L := by
  induction L with
  | zero => simpa only [List.replicate_zero,fillsSet_nil,c0]
  | succ L ih =>
    rw [List.replicate_succ,fillsSet_cons,ih,cs]
    change C+c L=c L+C
    rw [add_comm]

/-- Double-window activation yields a recurrent lower bound in unscaled prefix
lengths for the shrink lemma. -/
theorem dense_of_recurrent_activation {C : Set ℕ} {L : ℕ}
    (h : ∀ M : ℕ, ∃ n ≥ M, 6*n ≤ L*hits C (2*n)) :
    ∀ K : ℕ, ∃ N ≥ K, 3*N ≤ L*Erdos335.count C N := by
  intro K
  obtain ⟨n,hn,ha⟩ := h K
  have hc := Erdos338.CatalogueAdapter.count_eq_hits C (2*n)
  refine ⟨2*n, by omega, ?_⟩
  rw [hc]
  simpa [← Nat.mul_assoc] using ha

#print axioms fillsSet_append
#print axioms fills_repeated

end Erdos338.Existence.Bounded
