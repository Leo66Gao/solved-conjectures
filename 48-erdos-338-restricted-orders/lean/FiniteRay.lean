import Compression
import MixedWindow

/-! From a stabilized long block to a full eventual arithmetic progression. -/
namespace Erdos338.FiniteRay

open Erdos338.MixedDyson Erdos338.Compression

/-- Precise interface of the simultaneous stabilization module. -/
def StableFamily : Prop :=
  ∀ (k : ℕ) (A : Set ℕ) (B : Fin k → Set ℕ),
    0 ∈ A → (∀ i, 0 ∈ B i) →
    (∃ K : ℕ, ∀ N ≥ K, 2*N ≤ mass A B N) →
    ∀ L : ℕ, 0<L → ∃ (C : Set ℕ) (D : Fin k → Set ℕ) (g u : ℕ),
      0<g ∧ 0∈C ∧ (∀i,0∈D i) ∧ (∀j<L,u+g*j∈C) ∧
      (∀ i x, x∈D i → g∣x) ∧
      (∃ K : ℕ,∀N≥K,7*N≤4*mass C D N) ∧ mixed C D ⊆ mixed A B

theorem eventual_ray_of_stabilization (stable : StableFamily)
    {k : ℕ} (A : Set ℕ) (B : Fin k → Set ℕ) (hA : 0 ∈ A)
    (hB : ∀ i, 0 ∈ B i) (den : ∃ K : ℕ, ∀ N ≥ K, 2*N ≤ mass A B N) :
    ∃ a g T : ℕ, 0<g ∧ ∀ n ≥ T, a+g*n ∈ mixed A B := by
  let L := 4*(k+1)
  have hL : 0<L := by dsimp [L]; omega
  obtain ⟨C,D,g,u,hg,hC,hD,blk,dvd,density,sub⟩ := stable k A B hA hB den L hL
  obtain ⟨E,F,a,v,_,hF,interval,edense,lift⟩ :=
    compress_stable_family C D g u L hg hC hD blk hL dvd density
  have weight : (Fintype.card (Fin k) : ℝ) ≤ ((5/4 : ℝ)-1)*L := by
    simp [L]
    push_cast
    linarith
  obtain ⟨T,cof⟩ := cofinite_of_one_long_block E F (γ := (3/2:ℝ)) (δ := (5/4:ℝ))
    (by norm_num) (by norm_num) edense hF L hL weight v interval
  exact ⟨a,g,T,hg,fun n hn => sub (lift n (cof n hn))⟩

#print axioms eventual_ray_of_stabilization
end Erdos338.FiniteRay
