import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Uniform finite arithmetic progression in the additive box generated
by independently bounded multiples of a finite family of steps. -/

open scoped BigOperators
namespace Erdos338.Coin

theorem linear_combination {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℕ) :
    ∃ z : ι → ℤ, (∑ i ∈ s, (g i : ℤ)*z i) = (s.gcd g : ℕ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,by simp⟩
  | @insert a s hnot ih =>
    obtain ⟨z,hz⟩ := ih
    let u := Nat.gcdA (g a) (s.gcd g)
    let v := Nat.gcdB (g a) (s.gcd g)
    refine ⟨fun i => if i=a then u else z i*v, ?_⟩
    rw [Finset.sum_insert hnot,Finset.gcd_insert]
    simp only [if_pos rfl]
    have changeSum :
        (∑ i ∈ s, (g i : ℤ)*(if i=a then u else z i*v)) =
        (∑ i ∈ s, (g i : ℤ)*z i)*v := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have ne : i ≠ a := fun eq => hnot (eq ▸ hi)
      rw [if_neg ne, mul_assoc]
    rw [changeSum,hz]
    exact (Nat.gcd_eq_gcd_ab (g a) (s.gcd g)).symm

theorem progression_box {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℕ) (L : ℕ) :
    ∃ off cap : ℕ, ∀ j ≤ L, ∃ c : ι → ℕ,
      (∀ i ∈ s, c i ≤ cap) ∧ (∑ i ∈ s, c i*g i) = off+j*s.gcd g := by
  obtain ⟨z,hz⟩ := linear_combination s g
  let b (i : ι) := L*(z i).natAbs
  let cap := ∑ i ∈ s, 2*b i
  let off := ∑ i ∈ s, b i*g i
  refine ⟨off,cap,?_⟩
  intro j hj
  let cZ (i : ι) : ℤ := (b i : ℤ)+(j : ℤ)*z i
  have ja (i : ι) : (j:ℤ)*((z i).natAbs:ℤ) ≤ (b i:ℤ) := by
    dsimp [b]
    push_cast
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
  have nonneg (i : ι) : 0 ≤ cZ i := by
    have hh : -((z i).natAbs:ℤ) ≤ z i := by
      have t : -(z i) ≤ ((-(z i)).natAbs : ℤ) := Int.le_natAbs
      simpa only [Int.natAbs_neg,neg_le] using t
    have h := mul_le_mul_of_nonneg_left hh (Int.natCast_nonneg j)
    rw [mul_neg] at h
    have k := ja i
    dsimp [cZ]
    linarith
  let c (i : ι) := (cZ i).toNat
  have conv (i : ι) : (c i : ℤ) = cZ i := Int.toNat_of_nonneg (nonneg i)
  refine ⟨c,?_,?_⟩
  · intro i hi
    have hh : z i ≤ ((z i).natAbs:ℤ) := Int.le_natAbs
    have h := mul_le_mul_of_nonneg_left hh (Int.natCast_nonneg j)
    have k := ja i
    have bound : (c i : ℤ) ≤ (2*b i:ℕ) := by
      rw [conv]
      push_cast
      dsimp [cZ]
      linarith
    have cb : c i ≤ 2*b i := by exact_mod_cast bound
    exact cb.trans (Finset.single_le_sum (f := fun j => 2*b j) (fun _ _ => Nat.zero_le _) hi)
  · apply Nat.cast_injective (R := ℤ)
    dsimp [off]
    push_cast
    change (∑ i ∈ s, (c i : ℤ)*(g i : ℤ)) =
      (∑ i ∈ s, (b i : ℤ)*(g i : ℤ)) + (j : ℤ)*((s.gcd g : ℕ) : ℤ)
    simp only [conv,cZ,add_mul,Finset.sum_add_distrib]
    congr 1
    rw [← hz,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl

#print axioms progression_box
end Erdos338.Coin
