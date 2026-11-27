import HHPFinite
import RobustLayers

namespace Erdos338.Existence.Analytic

theorem prefixCount_eq_hits (P : Nat → Prop) (n : Nat) :
    (HHP.pref P n).card = hits P n := by
  classical
  induction n with
  | zero =>
    have empty : HHP.pref P 0 = ∅ := by
      ext x
      simp [HHP.mem_prefix] <;> omega
    rw [empty,Finset.card_empty]
    rfl
  | succ n ih =>
    rw [HHP.pref_card_succ,ih]
    rfl

theorem hhpDensity : HHPDensity := by
  intro A h ord
  obtain ⟨d,N,dp,hcount⟩ := HHP.positive_lower_density ord
  refine ⟨d,N,dp,?_⟩
  intro n hn
  exact (prefixCount_eq_hits (R A h) n) ▸ hcount n hn

theorem hhpDensity_uniform {A : ℕ → Prop} {h : ℕ}
    (ord : Erdos338.Growth.Mixed.OrdinaryAtMost A h) :
    ∃ N, ∀ n≥N, n ≤ HHP.densityFactor h * hits (R A h) n := by
  obtain ⟨N,hN⟩ := HHP.uniform_positive_lower_density ord
  exact ⟨N, fun n hn => (prefixCount_eq_hits (R A h) n) ▸ hN n hn⟩

#print axioms hhpDensity_uniform
#print axioms hhpDensity
end Erdos338.Existence.Analytic
