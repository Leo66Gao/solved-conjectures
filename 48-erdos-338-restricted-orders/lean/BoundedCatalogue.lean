import Erdos338Solution

/-! Uniform robust progressions imply the exact original boundedness variant. -/
namespace Erdos338.Boundedness

open CatalogueAdapter Growth

/-- Uniformly in A, a bounded-rank eventual progression robust to
deleting up to its modulus minus one labels. Bounds depend only on h. -/
def UniformProgressions : Prop :=
  ∀ h : ℕ, ∃ K B : ℕ, ∀ A : Set ℕ, HasOrder A h →
    ∃ a g N : ℕ, 0 < g ∧ g ≤ B ∧ RobustProgression A a g K N

theorem bounded_catalogue (progressions : UniformProgressions) :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h) := by
  classical
  choose K B hr using progressions
  refine ⟨fun h => K h + B h, ?_⟩
  intro A h hA finite
  obtain ⟨a,g,N,gpos,gb,prog⟩ := hr h A hA
  have comp : CompleteMod A g := (answer_iff_list.mp (necessity finite)) g gpos
  have small := (modCriterion_at_robust_class gpos prog).mp comp
  obtain ⟨n0, hn⟩ := small
  apply restricted_iff_list.mpr
  refine ⟨n0, fun n hn0 => ?_⟩
  obtain ⟨xs,nd,mem,sm,len⟩ := hn n hn0
  exact ⟨xs,nd,mem,sm,len.trans (by change K h+g-1 ≤ K h+B h; omega)⟩

#print axioms bounded_catalogue

end Erdos338.Boundedness
