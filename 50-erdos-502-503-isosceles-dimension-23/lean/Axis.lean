import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! The center and two poles construction on actual inner-product vectors. -/
namespace Erdos23
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def sqDist (x y : V) : ℝ := ⟪x-y,x-y⟫_ℝ

private theorem sqDist_symm (x y : V) : sqDist x y = sqDist y x := by
  unfold sqDist
  rw [show y-x = -(x-y) by abel, inner_neg_left, inner_neg_right, neg_neg]

private theorem sqDist_formula (x y : V) :
    sqDist x y = ⟪x,x⟫_ℝ + ⟪y,y⟫_ℝ - 2*⟪x,y⟫_ℝ := by
  unfold sqDist
  rw [inner_sub_left,inner_sub_right,inner_sub_right,real_inner_comm x y]
  ring

def Axial {ι : Type*} (p : ι → V) (v : V) : ι ⊕ Fin 3 → V
  | .inl i => p i
  | .inr j => if j.val=0 then 0 else if j.val=1 then v else -v

def Iso3 (a b c : V) : Prop :=
  sqDist a b = sqDist a c ∨ sqDist a b = sqDist b c ∨ sqDist a c = sqDist b c

private theorem isosceles_of_two {a b c : V} {u w : ℝ}
    (hab : sqDist a b=u ∨ sqDist a b=w) (hac : sqDist a c=u ∨ sqDist a c=w)
    (hbc : sqDist b c=u ∨ sqDist b c=w) : Iso3 a b c := by
  unfold Iso3
  rcases hab with hab|hab <;> rcases hac with hac|hac <;> rcases hbc with hbc|hbc <;>
    simp [hab,hac,hbc]

private theorem isosceles_rotate (a b c : V) : Iso3 a b c → Iso3 b c a := by
  unfold Iso3
  rw [sqDist_symm b a,sqDist_symm c a]
  aesop

/-- For a spherical two-distance family, adding its center and two opposite
norm-matched poles in an orthogonal direction produces an isosceles family. -/
theorem isosceles_axial {ι : Type*} (p : ι → V) (v : V) (r a b : ℝ)
    (hcore : ∀ i, ⟪p i,p i⟫_ℝ = r) (hpole : ⟪v,v⟫_ℝ = r)
    (orth : ∀ i, ⟪p i,v⟫_ℝ = 0)
    (two : ∀ i j, i ≠ j → sqDist (p i) (p j) = a ∨ sqDist (p i) (p j) = b) :
    ∀ i j k : ι ⊕ Fin 3, i ≠ j → i ≠ k → j ≠ k →
      Iso3 (Axial p v i) (Axial p v j) (Axial p v k) := by
  intro i j k hij hik hjk
  have nCore : ∀ i, ‖p i‖ ^ 2 = r := fun i => by simpa using hcore i
  have nPole : ‖v‖ ^ 2 = r := by simpa using hpole
  have dh (i : ι) (j : Fin 3) : sqDist (p i) (Axial p v (.inr j)) =
      if j.val=0 then r else 2*r := by
    fin_cases j <;>
      simp [Axial,sqDist_formula,nCore,nPole,orth,inner_neg_right] <;> ring
  have da (j k : Fin 3) (ne : j ≠ k) :
      sqDist (Axial p v (.inr j)) (Axial p v (.inr k)) =
      if j.val=0 ∨ k.val=0 then r else 4*r := by
    fin_cases j <;> fin_cases k <;>
      simp [Axial,sqDist_formula,nPole,inner_neg_left] at ne ⊢ <;> ring
  have cc (x y : ι) (z : Fin 3) :
      Iso3 (Axial p v (.inl x)) (Axial p v (.inl y)) (Axial p v (.inr z)) := by
    apply Or.inr ∘ Or.inr
    change sqDist (p x) (Axial p v (.inr z)) = sqDist (p y) (Axial p v (.inr z))
    rw [dh,dh]
  have cp (x : ι) (y z : Fin 3) (ne : y ≠ z) :
      Iso3 (Axial p v (.inl x)) (Axial p v (.inr y)) (Axial p v (.inr z)) := by
    unfold Iso3
    change sqDist (p x) (Axial p v (.inr y)) = sqDist (p x) (Axial p v (.inr z)) ∨
      sqDist (p x) (Axial p v (.inr y)) = sqDist (Axial p v (.inr y)) (Axial p v (.inr z)) ∨
      sqDist (p x) (Axial p v (.inr z)) = sqDist (Axial p v (.inr y)) (Axial p v (.inr z))
    rw [dh,dh,da _ _ ne]
    fin_cases y <;> fin_cases z <;> simp at ne ⊢
  rcases i with i|i <;> rcases j with j|j <;> rcases k with k|k
  · exact isosceles_of_two (two i j (fun h => hij (congrArg Sum.inl h)))
      (two i k (fun h => hik (congrArg Sum.inl h))) (two j k (fun h => hjk (congrArg Sum.inl h)))
  · exact cc i j k
  · exact isosceles_rotate _ _ _ (cc k i j)
  · exact cp i j k (fun h => hjk (congrArg Sum.inr h))
  · exact isosceles_rotate _ _ _ (isosceles_rotate _ _ _ (cc j k i))
  · exact isosceles_rotate _ _ _ (isosceles_rotate _ _ _ (cp j k i (fun h => hik (congrArg Sum.inr h.symm))))
  · exact isosceles_rotate _ _ _ (cp k i j (fun h => hij (congrArg Sum.inr h)))
  · exact isosceles_of_two
      (by rw [da _ _ (fun h => hij (congrArg Sum.inr h))]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl)
      (by rw [da _ _ (fun h => hik (congrArg Sum.inr h))]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl)
      (by rw [da _ _ (fun h => hjk (congrArg Sum.inr h))]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl)


theorem axial_injective {ι : Type*} (p : ι → V) (v : V) (r : ℝ)
    (hr : 0 < r) (hcore : ∀ i, ⟪p i,p i⟫_ℝ = r) (hpole : ⟪v,v⟫_ℝ = r)
    (orth : ∀ i, ⟪p i,v⟫_ℝ = 0) (inj : Function.Injective p) :
    Function.Injective (Axial p v) := by
  intro x y he
  have sep (i : ι) (j : Fin 3) : p i ≠ Axial p v (.inr j) := by
    intro h
    fin_cases j
    · have hz : p i = 0 := by simpa [Axial] using h
      have hn := hcore i
      rw [hz,inner_zero_left] at hn
      exact (ne_of_gt hr) hn.symm
    · have hz : p i = v := by simpa [Axial] using h
      have ho := orth i
      rw [hz,hpole] at ho
      exact (ne_of_gt hr) ho
    · have hz : p i = -v := by simpa [Axial] using h
      have ho := orth i
      rw [hz,inner_neg_left,hpole] at ho
      linarith
  rcases x with i|i <;> rcases y with j|j
  · exact congrArg Sum.inl (inj he)
  · exact (sep i j he).elim
  · exact (sep j i he.symm).elim
  · have nPole : ‖v‖ ^ 2 = r := by simpa using hpole
    have H := congrArg (fun z => ⟪z,v⟫_ℝ) he
    fin_cases i <;> fin_cases j <;> simp [Axial,nPole,inner_neg_left] at H ⊢ <;> linarith

theorem sqDist_eq_dist_sq (x y : V) : sqDist x y = dist x y ^ 2 := by
  simp [sqDist,dist_eq_norm]

theorem axial_278_of_275 (p : Fin 275 → V) (v : V) (r a b : ℝ)
    (hr : 0 < r) (hcore : ∀ i, ⟪p i,p i⟫_ℝ = r) (hpole : ⟪v,v⟫_ℝ = r)
    (orth : ∀ i, ⟪p i,v⟫_ℝ = 0) (pinj : Function.Injective p)
    (two : ∀ i j, i ≠ j → sqDist (p i) (p j) = a ∨ sqDist (p i) (p j) = b) :
    ∃ f : Fin 278 ↪ V, ∀ i j k, i ≠ j → i ≠ k → j ≠ k → Iso3 (f i) (f j) (f k) := by
  let e : Fin 278 ≃ Fin 275 ⊕ Fin 3  := (finSumFinEquiv : Fin 275 ⊕ Fin 3 ≃ Fin (275+3)).symm
  let f : Fin 275 ⊕ Fin 3 ↪ V := ⟨Axial p v, axial_injective p v r hr hcore hpole orth pinj⟩
  refine ⟨e.toEmbedding.trans f, ?_⟩
  intro i j k hi hj hk
  exact isosceles_axial p v r a b hcore hpole orth two _ _ _
    (fun h => hi (e.injective h)) (fun h => hj (e.injective h)) (fun h => hk (e.injective h))

#print axioms isosceles_axial
#print axioms axial_278_of_275
end Erdos23
