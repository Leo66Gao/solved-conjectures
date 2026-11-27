import Erdos335.Density
import Mathlib.Tactic

namespace Erdos338.Dilation
open scoped BigOperators

/-- Compress the zero residue by taking preimages under multiplication. -/
def compress (g : ℕ) (P : Set ℕ) : Set ℕ := {x | g*x ∈ P}

theorem count_compress_eq (g : ℕ) (P : Set ℕ) (N : ℕ) (hg : 0<g)
    (hdiv : ∀ x ∈ P, g ∣ x) :
    Erdos335.count (compress g P) N = Erdos335.count P (g*N) := by
  classical
  let C := (Finset.Icc 1 N).filter (· ∈ compress g P)
  let D := (Finset.Icc 1 (g*N)).filter (· ∈ P)
  change C.card=D.card
  have himage : C.image (g*·) = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨yr,hP⟩ := Finset.mem_filter.mp hy
      obtain ⟨yl,yu⟩ := Finset.mem_Icc.mp yr
      have yp : 0<y := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by have := Nat.mul_pos hg yp; omega,Nat.mul_le_mul_left g yu⟩,hP⟩
    · intro hx
      obtain ⟨xr,hP⟩ := Finset.mem_filter.mp hx
      obtain ⟨xl,xu⟩ := Finset.mem_Icc.mp xr
      obtain ⟨y,rfl⟩ := hdiv x hP
      have yl : 1≤y := by
        by_cases hy : y=0
        · simp [hy] at xl
        · omega
      have yu : y≤N := Nat.le_of_mul_le_mul_left xu hg
      exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨yl,yu⟩,hP⟩,rfl⟩
  rw [← himage]
  exact (Finset.card_image_of_injective _ (fun x y he => Nat.eq_of_mul_eq_mul_left hg he)).symm

theorem aggregate_count_compress (g : ℕ) (ss : List (Set ℕ)) (N : ℕ) (hg : 0<g)
    (divisible : ∀ P ∈ ss, ∀ x ∈ P, g ∣ x) :
    ((ss.map (compress g)).map (fun P => Erdos335.count P N)).sum =
    (ss.map (fun P => Erdos335.count P (g*N))).sum := by
  induction ss with
  | nil => rfl
  | cons P rest ih =>
    have dP := divisible P (by simp)
    have dr : ∀ Q∈rest, ∀ x ∈ Q, g ∣ x :=
      fun Q hQ => divisible Q (by simp [hQ])
    simp only [List.map_cons,List.sum_cons,count_compress_eq g P N hg dP,ih dr]

#print axioms count_compress_eq
#print axioms aggregate_count_compress
end Erdos338.Dilation
