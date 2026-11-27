import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Binary rank and saturation obstruction
This checks the finite-dimensional contradiction used by the dimension-23 packet,
once the packet's lattice feature vectors and quadratic form have been supplied.
-/
namespace Erdos23
open scoped BigOperators
abbrev F := ZMod 2

variable {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

private theorem one_one : (1 : F) + 1 = 0 := by decide

omit [FiniteDimensional F W] in
private theorem buildPairing {n : ℕ} (v : Fin n → W)
    (b : W →ₗ[F] W →ₗ[F] F) (l : W →ₗ[F] F)
    (lv : ∀ i, l (v i) = 1)
    (self : ∀ i, b (v i) (v i) = 0)
    (off : ∀ i j, i ≠ j → b (v i) (v j) = 1) :
    Function.Surjective (LinearMap.pi (fun i => b (v i) + l)) := by
  classical
  let T : W →ₗ[F] (Fin n → F) := LinearMap.pi (fun i => b (v i) + l)
  have Tv (j i : Fin n) : T (v j) i = if i = j then 1 else 0 := by
    change b (v i) (v j) + l (v j) = _
    rw [lv]
    split_ifs with h
    · subst j; rw [self,zero_add]
    · rw [off _ _ h,one_one]
  intro a
  refine ⟨∑ j, a j • v j,?_⟩
  change T _ = a
  ext i
  simp [map_sum, Finset.sum_apply, Tv]

theorem binary_rank_bound {n : ℕ} (v : Fin n → W)
    (b : W →ₗ[F] W →ₗ[F] F) (l : W →ₗ[F] F)
    (lv : ∀ i, l (v i) = 1)
    (self : ∀ i, b (v i) (v i) = 0)
    (off : ∀ i j, i ≠ j → b (v i) (v j) = 1) :
    n ≤ Module.finrank F W := by
  have h := LinearMap.finrank_le_finrank_of_surjective (buildPairing v b l lv self off)
  simpa [Module.finrank_pi] using h

omit [FiniteDimensional F W] in
private theorem qsum {n : ℕ} (v : Fin n → W) (Q : W → F)
    (b : W →ₗ[F] W →ₗ[F] F)
    (qzero : Q 0 = 0) (qadd : ∀ x y, Q (x+y) = Q x + Q y + b x y)
    (qv : ∀ i, Q (v i) = 0)
    (off : ∀ i j, i ≠ j → b (v i) (v j) = 1) (s : Finset (Fin n)) :
    Q (∑ i ∈ s, v i) = (s.card.choose 2 : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qzero]
  | @insert i s hi ih =>
    have hs : ∑ j ∈ s, b (v i) (v j) = (s.card : F) := by
      rw [Finset.sum_congr rfl (fun j hj => off _ _ (fun e => hi (by simpa [e] using hj)))]
      simp
    rw [Finset.sum_insert hi, qadd, qv, zero_add, ih, map_sum, hs, Finset.card_insert_of_notMem hi]
    have he : (s.card+1).choose 2 = s.card.choose 2 + s.card := by
      simpa [Nat.add_comm] using (Nat.choose_succ_succ s.card 1)
    rw [he,Nat.cast_add]

/-- If the number of features is at most n, the isotropic evaluation basis at
    saturation cannot have n ≡ 2 (mod 4), as witnessed by the pair-count cast. -/
theorem no_saturation {n : ℕ} (v : Fin n → W) (Q : W → F)
    (b : W →ₗ[F] W →ₗ[F] F) (l : W →ₗ[F] F) (e : W)
    (lv : ∀ i, l (v i) = 1) (le : l e = 0)
    (self : ∀ i, b (v i) (v i) = 0)
    (off : ∀ i j, i ≠ j → b (v i) (v j) = 1)
    (be : ∀ i, b (v i) e = 1)
    (qzero : Q 0 = 0) (qe : Q e = 0)
    (qadd : ∀ x y, Q (x+y) = Q x + Q y + b x y)
    (qv : ∀ i, Q (v i) = 0)
    (odd_pairs : (n.choose 2 : F) = 1)
    (dim : Module.finrank F W ≤ n) : False := by
  classical
  let T : W →ₗ[F] (Fin n → F) := LinearMap.pi (fun i => b (v i) + l)
  have onto : Function.Surjective T := buildPairing v b l lv self off
  have ranger : T.range = ⊤ := LinearMap.range_eq_top.mpr onto
  have rn : Module.finrank F (Fin n → F) = n := by simp
  have hsum := LinearMap.finrank_range_add_finrank_ker T
  rw [ranger,finrank_top,rn] at hsum
  have ker0 : Module.finrank F T.ker = 0 := by omega
  have inj : Function.Injective T := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp ker0)
  have both : T (∑ i, v i) = T e := by
    ext j
    have eP : T e j = 1 := by change b (v j) e + l e = 1; rw [be,le,add_zero]
    rw [eP,map_sum,Finset.sum_apply]
    calc
      _ = T (v j) j := by
        apply Finset.sum_eq_single j
        · intro k _ hk
          change b (v j) (v k) + l (v k) = 0
          rw [lv,off _ _ (Ne.symm hk),one_one]
        · simp
      _ = 1 := by
        change b (v j) (v j) + l (v j) = 1
        rw [self,lv,zero_add]
  have se := inj both
  have Qs := qsum v Q b qzero qadd qv off Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin] at Qs
  rw [se,qe,odd_pairs] at Qs
  exact zero_ne_one Qs

/-- Numerical dimension cap supplied by the lattice proof. No positivity
    of the polar form over F₂ is required. -/
theorem dimension23_count_certificate (h r : ℕ) (hh : h ≤ 23) (hr : r ≤ 22) :
    2+h+r+r.choose 2 ≤ 278 := by
  have hc : r.choose 2 ≤ 231 := (Nat.choose_mono 2 hr).trans (by decide)
  omega

end Erdos23
