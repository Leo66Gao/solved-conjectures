import MixedDyson
import DilationCount

/-! Compress a common divisor of the donor sets while retaining one
arithmetic progression of the receiver. -/

open scoped BigOperators
namespace Erdos338.Compression
open Erdos335 Erdos338.MixedDyson Erdos338.Dilation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem count_le_cutoff (P : Set ℕ) (N : ℕ) : count P N ≤ N := by
  classical
  unfold count
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem compress_stable_family (A : Set ℕ) (B : ι → Set ℕ) (g u L : ℕ)
    (hg : 0<g) (hA0 : 0 ∈ A) (hB0 : ∀ i, 0 ∈ B i)
    (hblock : ∀ j<L, u+g*j ∈ A) (hL : 0<L)
    (divisible : ∀ i x, x ∈ B i → g ∣ x)
    (den : ∃ K, ∀ N≥K, 7*N ≤ 4*mass A B N) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ) (a v : ℕ),
      0 ∈ C ∧ (∀ i, 0 ∈ D i) ∧ (∀ j<L, v+j ∈ C) ∧
      (∃ K, ∀ N≥K, (3/2 : ℝ)*N ≤ (mass C D N : ℝ)) ∧
      ∀ n ∈ mixed C D, a+g*n ∈ mixed A B := by
  by_cases one : g=1
  · subst g
    refine ⟨A,B,0,u,hA0,hB0,fun j hj => by simpa using hblock j hj,?_,?_⟩
    · obtain ⟨K,hK⟩ := den
      refine ⟨K,fun N hN => ?_⟩
      have aux : (7:ℝ)*N ≤ 4*(mass A B N : ℝ) := by exact_mod_cast hK N hN
      have nn : (0:ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    · intro n hn
      simpa using hn
  · have g2 : 2≤g := by omega
    let r := u%g
    let k := u/g
    have eu : r+g*k=u := Nat.mod_add_div u g
    have hu := hblock 0 hL
    have hex : ∃ z : ℕ, r+g*z ∈ A :=
      ⟨k,by rw [eu]; simpa using hu⟩
    classical
    let z := Nat.find hex
    have hz : r+g*z ∈ A := Nat.find_spec hex
    have hzle : z≤k := Nat.find_min' hex (by rw [eu]; simpa using hu)
    let C : Set ℕ := {x | r+g*(z+x) ∈ A}
    let D (i : ι) := compress g (B i)
    let a := r+g*z
    refine ⟨C,D,a,k-z,?_,?_,?_,?_,?_⟩
    · simpa [C] using hz
    · intro i
      simpa [D,compress] using hB0 i
    · intro j hj
      change r+g*(z+(k-z+j)) ∈ A
      have hh : z+(k-z+j)=k+j := by omega
      rw [hh,Nat.mul_add,← Nat.add_assoc,eu]
      exact hblock j hj
    · obtain ⟨K,hK⟩ := den
      refine ⟨K,fun N hN => ?_⟩
      have ge : 2*N≤g*N := Nat.mul_le_mul_right N g2
      have hkg : K≤g*N := by omega
      have hsum : (∑ i, count (D i) N) = ∑ i, count (B i) (g*N) := by
        apply Finset.sum_congr rfl
        intro i _
        exact count_compress_eq g (B i) N hg (divisible i)
      have hu := hK (g*N) hkg
      unfold mass at hu ⊢
      rw [← hsum] at hu
      have cx := count_le_cutoff A (g*N)
      have de : 3*N≤2*(count C N+∑ i,count (D i) N) := by omega
      have dr : (3:ℝ)*N≤2*((count C N : ℝ)+∑ i,(count (D i) N : ℝ)) := by exact_mod_cast de
      push_cast
      linarith
    · intro n hn
      obtain ⟨x,hx,y,hy,hs⟩ := hn
      refine ⟨r+g*(z+x),hx,fun i => g*y i,hy,?_⟩
      dsimp [a]
      rw [← Finset.mul_sum, ← hs]
      ring

#print axioms compress_stable_family
end Erdos338.Compression
