import Erdos335.DysonCounting
import Mathlib.Tactic

/-! Simultaneous zero-based Dyson counting for a finite list of right-hand
summands. One finite shift step can service all of them at once. -/
open scoped Pointwise BigOperators
open Erdos335
namespace Erdos338.MixedDyson
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixed (A : Set ℕ) (B : ι → Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b : ι → ℕ, (∀ i, b i ∈ B i) ∧ a + ∑ i, b i = n}

def Budget (A : Set ℕ) (B : ι → Set ℕ) (δ : ℝ) (k : ℕ) : Prop :=
  ∀ x : ℕ, δ * (x + 1 : ℕ) ≤
    (prefixCount A (x + 1) : ℝ) + ∑ i, (count (B i) (x - k) : ℝ)

def ClosedBelow (A : Set ℕ) (B : ι → Set ℕ) (k : ℕ) : Prop :=
  ∀ i, ∀ b ∈ B i, ∀ a ∈ A, a < k → b + a ∈ A

theorem mixed_update_subset (A : Set ℕ) (B : ι → Set ℕ) (i : ι) (e : ℕ) :
    mixed (dysonLeft A (B i) e) (Function.update B i (dysonRight A (B i) e)) ⊆ mixed A B := by
  intro n hn
  obtain ⟨a, ha, b, hb, hsum⟩ := hn
  have hb' : b i ∈ dysonRight A (B i) e := by simpa using hb i
  obtain ⟨a', ha', bi, hbi, hab⟩ := dyson_sum_subset A (B i) e
    ⟨a,ha,b i,hb',rfl⟩
  refine ⟨a', ha', Function.update b i bi, ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst j; simpa
    · simpa [Function.update_of_ne h] using hb j
  · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    rw [Finset.sdiff_singleton_eq_erase]
    change a' + bi = a + b i at hab
    omega

theorem budget_update {A : Set ℕ} {B : ι → Set ℕ} {δ : ℝ} {k : ℕ} (i : ι)
    (hk : k ∈ A) (hz : 0 ∈ B i) (h : Budget A B δ k) :
    Budget (dysonLeft A (B i) k) (Function.update B i (dysonRight A (B i) k)) δ k := by
  intro x
  let f (j : ι) := (count (Function.update B i (dysonRight A (B i) k) j) (x - k) : ℝ)
  have herase : ∑ j ∈ Finset.univ.erase i, f j = ∑ j ∈ Finset.univ.erase i, (count (B j) (x-k) : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hfi : f i = count (dysonRight A (B i) k) (x - k) := by simp [f]
  change _ ≤ _ + ∑ j, f j
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i), herase, hfi]
  have hold := h x
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hold
  have hinv := dyson_count0_invariant A (B i) k x hk hz
  have hinvR : (prefixCount (dysonLeft A (B i) k) (x+1) : ℝ) +
      count (dysonRight A (B i) k) (x-k) =
      prefixCount A (x+1) + count (B i) (x-k) := by exact_mod_cast hinv
  linarith

/-- At a fixed left anchor, do a Dyson step on every specified right slot.
All other slots can be left unchanged. -/
theorem transform_finset (A : Set ℕ) (B : ι → Set ℕ) (δ : ℝ) (k : ℕ)
    (hzB : ∀ i, 0 ∈ B i) (hk : k ∈ A)
    (hb : Budget A B δ k) (hcl : ClosedBelow A B k) (T : Finset ι) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ), A ⊆ C ∧ (∀ i, D i ⊆ B i) ∧
      (∀ a ≤ k, a ∈ C ↔ a ∈ A) ∧ (∀ i, 0 ∈ D i) ∧ mixed C D ⊆ mixed A B ∧
      Budget C D δ k ∧ ClosedBelow C D k ∧
      (∀ i ∈ T, ∀ b ∈ D i, b+k ∈ C) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨A,B, Set.Subset.rfl, fun _ => Set.Subset.rfl, fun _ _ => Iff.rfl, hzB,
                     Set.Subset.rfl, hb, hcl, by simp⟩
  | @insert i T hi ih =>
    obtain ⟨C,D,hAC,hDB,hbelow,hD0,hsub,hbud,hclos,hdone⟩ := ih
    have hkC := hAC hk
    let E := dysonLeft C (D i) k
    let F := Function.update D i (dysonRight C (D i) k)
    have hCE : C ⊆ E := subset_dysonLeft _ _ _
    have hFD (j : ι) : F j ⊆ D j := by
      by_cases h : j = i
      · subst j; simpa [F] using dysonRight_subset C (D i) k
      · simp [F,Function.update_of_ne h]
    have hEC (a : ℕ) (ha : a ≤ k) : a ∈ E ↔ a ∈ C := dysonLeft_mem_iff_of_le hkC ha
    refine ⟨E,F,hAC.trans hCE,fun j => (hFD j).trans (hDB j),
      fun a ha => (hEC a ha).trans (hbelow a ha), ?_,
      (mixed_update_subset C D i k).trans hsub, budget_update i hkC (hD0 i) hbud, ?_, ?_⟩
    · intro j
      by_cases h : j = i
      · subst j; simpa [F] using zero_mem_dysonRight hkC (hD0 i)
      · simpa [F,Function.update_of_ne h] using hD0 j
    · intro j b hb a ha haj
      exact hCE (hclos j b (hFD j hb) a ((hEC a haj.le).1 ha) haj)
    · intro j hj b hb
      rcases Finset.mem_insert.mp hj with rfl | hT
      · have hh : b ∈ dysonRight C (D j) k := by simpa [F] using hb
        exact hCE hh.2
      · exact hCE (hdone j hT b (hFD j hb))

/-- Simultaneous strengthening of all right prefix cutoffs. -/
theorem budget_succ {A : Set ℕ} {B : ι → Set ℕ} {δ : ℝ} {k : ℕ}
    (hI : Budget A B δ k)
    (hII : ∀ i, ∀ b ∈ B i, ∀ a ∈ A, a ≤ k → b+a ∈ A) :
    Budget A B δ (k+1) := by
  classical
  intro x
  by_cases hx : x ≤ k
  · simpa [Nat.sub_eq_zero_of_le hx, Nat.sub_eq_zero_of_le (show x ≤ k+1 by omega), count_zero]
      using hI x
  · let t := x-k
    have htpos : 0 < t := by dsimp [t]; omega
    have htx : t+k=x := by dsimp [t]; omega
    have hcut : x-(k+1) = t-1 := by dsimp [t]; omega
    by_cases htB : ∃ i, t ∈ B i
    · obtain ⟨i,hi⟩ := htB
      have hbase := hI k
      simp [count_zero] at hbase
      have hprev := hI (t-1)
      rw [show t-1+1=t by omega] at hprev
      have hblock := prefixCount_translated_block_le A t k (fun a ha hak => hII i t hi a ha hak)
      rw [htx] at hblock
      have hblockR : (prefixCount A t : ℝ) + prefixCount A (k+1) ≤
          prefixCount A (x+1) := by exact_mod_cast hblock
      have hmono : (∑ j, (count (B j) (t-1-k) : ℝ)) ≤
          ∑ j, (count (B j) (t-1) : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact_mod_cast count_mono_cutoff (B j) (Nat.sub_le (t-1) k)
      have hindex : (x+1 : ℕ) = t + (k+1) := by omega
      rw [hcut,hindex]
      rw [hindex] at hblockR
      push_cast at *
      nlinarith
    · have hcount (j : ι) : count (B j) (x-k) = count (B j) (x-(k+1)) := by
        have ht : t=t-1+1 := by omega
        change count (B j) t = _
        rw [ht, count_succ, ← ht]
        rw [hcut]
        simp [show t ∉ B j from fun h => htB ⟨j,h⟩]
      simpa [hcount] using hI x

theorem advance {A : Set ℕ} {B : ι → Set ℕ} {δ : ℝ}
    (hA : 0 ∈ A) (hB : ∀ i, 0 ∈ B i) (hI : Budget A B δ 0) (k : ℕ) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ), 0 ∈ C ∧ (∀ i, 0 ∈ D i) ∧ mixed C D ⊆ mixed A B ∧
      Budget C D δ k ∧ ClosedBelow C D k := by
  classical
  induction k with
  | zero => exact ⟨A,B,hA,hB,Set.Subset.rfl,hI,by simp [ClosedBelow]⟩
  | succ k ih =>
    obtain ⟨C,D,hC,hD,hsub,hbud,hclos⟩ := ih
    by_cases hk : k ∈ C
    · obtain ⟨E,F,hCE,_,_,hF,hEF,hbud',hclos',hdone⟩ :=
        transform_finset C D δ k hD hk hbud hclos Finset.univ
      have hall (i : ι) (b : ℕ) (hb : b ∈ F i) (a : ℕ) (ha : a ∈ E) (h : a ≤ k) : b+a ∈ E := by
        rcases eq_or_lt_of_le h with rfl | hlt
        · exact hdone i (Finset.mem_univ i) b hb
        · exact hclos' i b hb a ha hlt
      exact ⟨E,F,hCE hC,hF,hEF.trans hsub,budget_succ hbud' hall,
        fun i b hb a ha hh => hall i b hb a ha (by omega)⟩
    · have hall (i : ι) (b : ℕ) (hb : b ∈ D i) (a : ℕ) (ha : a ∈ C) (h : a ≤ k) : b+a ∈ C := by
        rcases eq_or_lt_of_le h with rfl | hlt
        · exact (hk ha).elim
        · exact hclos i b hb a ha hlt
      exact ⟨C,D,hC,hD,hsub,budget_succ hbud hall,
        fun i b hb a ha hh => hall i b hb a ha (by omega)⟩

theorem mixed_prefix_density {A : Set ℕ} {B : ι → Set ℕ} {δ : ℝ}
    (hA : 0 ∈ A) (hB : ∀ i, 0 ∈ B i) (hi : Budget A B δ 0) (N : ℕ) :
    δ * (N + 1 : ℕ) ≤ (prefixCount (mixed A B) (N+1) : ℝ) := by
  have ⟨C,D,_,hD,hsub,hbud,_⟩ := advance hA hB hi (N+1)
  have hC : C ⊆ mixed C D := fun c hc => ⟨c,hc,fun _ => 0,hD,by simp⟩
  have hN := hbud N
  simp [show N-(N+1)=0 by omega, count_zero] at hN
  have hh : (prefixCount C (N+1) : ℝ) ≤ prefixCount (mixed A B) (N+1) := by
    exact_mod_cast prefixCount_mono_set (hC.trans hsub) (N+1)
  simpa only [Nat.cast_add, Nat.cast_one] using hN.trans hh

noncomputable def mass (A : Set ℕ) (B : ι → Set ℕ) (N : ℕ) : ℕ :=
  count A N + ∑ i, count (B i) N

def Extend (A : Set ℕ) (B : ι → Set ℕ) (C : Set ℕ) (D : ι → Set ℕ) : Prop :=
  A ⊆ C ∧ (∀ i, D i ⊆ B i) ∧ (∀ i, 0 ∈ D i) ∧
    mixed C D ⊆ mixed A B ∧ ∃ M : ℕ, ∀ N, mass A B N ≤ mass C D N + M

private theorem extend_refl {A : Set ℕ} {B : ι → Set ℕ} (hB : ∀ i, 0 ∈ B i) :
    Extend A B A B :=
  ⟨Set.Subset.rfl, fun _ => Set.Subset.rfl, hB, Set.Subset.rfl, 0, by simp⟩

private theorem Extend.trans {A C E : Set ℕ} {B D F : ι → Set ℕ}
    (h : Extend A B C D) (hh : Extend C D E F) : Extend A B E F := by
  obtain ⟨h1,h2,_,h3,M,h4⟩ := h
  obtain ⟨h5,h6,h7,h8,T,h9⟩ := hh
  refine ⟨h1.trans h5, fun i => (h6 i).trans (h2 i), h7, h8.trans h3, M+T, ?_⟩
  intro N
  have x := h4 N; have y := h9 N
  omega

theorem extend_step {A : Set ℕ} {B : ι → Set ℕ} (hB : ∀ i, 0 ∈ B i)
    {e : ℕ} (he : e ∈ A) (hA : 0 ∈ A) (i : ι) :
    Extend A B (dysonLeft A (B i) e) (Function.update B i (dysonRight A (B i) e)) := by
  classical
  have hd0 := zero_mem_dysonRight he (hB i)
  have hc0 := zero_mem_dysonLeft (B := B i) (e := e) hA
  refine ⟨subset_dysonLeft _ _ _, ?_, ?_, mixed_update_subset A B i e,e,?_⟩
  · intro j
    by_cases h : j=i
    · subst j; simpa using dysonRight_subset A (B i) e
    · simp [Function.update_of_ne h]
  · intro j
    by_cases h : j=i
    · subst j; simpa using hd0
    · simpa [Function.update_of_ne h] using hB j
  · intro N
    have h := dyson_prefix_error A (B i) e (N+1)
    rw [prefixCount_succ_eq_count, prefixCount_succ_eq_count, prefixCount_succ_eq_count,
      prefixCount_succ_eq_count] at h
    simp only [hc0,hd0,hA,hB, ite_true, Nat.cast_add, Nat.cast_one] at h
    have hnat : count A N + count (B i) N ≤
        count (dysonLeft A (B i) e) N + count (dysonRight A (B i) e) N + e := by
      have hreal := (abs_le.mp h).1
      exact_mod_cast (show (count A N : ℝ) + count (B i) N ≤
        count (dysonLeft A (B i) e) N + count (dysonRight A (B i) e) N + e by linarith)
    let f (j : ι) := count (Function.update B i (dysonRight A (B i) e) j) N
    have herase : ∑ j ∈ Finset.univ.erase i, f j = ∑ j ∈ Finset.univ.erase i, count (B j) N := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [f, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    unfold mass
    change _ ≤ _ + (∑ j, f j) + _
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i), herase]
    rw [← Finset.sum_erase_add Finset.univ (fun j => count (B j) N) (Finset.mem_univ i)]
    have hfi : f i = count (dysonRight A (B i) e) N := by simp [f]
    rw [hfi]
    omega

theorem cover_anchor {A : Set ℕ} {B : ι → Set ℕ} (hA : 0 ∈ A) (hB : ∀ i, 0 ∈ B i)
    {e : ℕ} (he : e ∈ A) (T : Finset ι) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ), Extend A B C D ∧ ∀ i ∈ T, ∀ b ∈ D i, b+e ∈ C := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨A,B,extend_refl hB,by simp⟩
  | @insert i T hi ih =>
    obtain ⟨C,D,h,hold⟩ := ih
    have step := extend_step h.2.2.1 (h.1 he) (h.1 hA) i
    refine ⟨_,_,h.trans step,?_⟩
    intro j hj b hb
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have hb' : b ∈ dysonRight C (D j) e := by simpa using hb
      exact step.1 hb'.2
    · exact step.1 (hold j hj b (step.2.1 j hb))

theorem cover_initial {A : Set ℕ} {B : ι → Set ℕ} (hA : 0 ∈ A) (hB : ∀ i, 0 ∈ B i)
    (L : ℕ) (hL : ∀ j < L, j ∈ A) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ), Extend A B C D ∧
      ∀ i, ∀ b ∈ D i, ∀ j < L, b+j ∈ C := by
  induction L with
  | zero => exact ⟨A,B,extend_refl hB,by simp⟩
  | succ L ih =>
    obtain ⟨C,D,h,hold⟩ := ih fun j hj => hL j (by omega)
    have he : L ∈ C := h.1 (hL L (by omega))
    obtain ⟨E,F,h',hnew⟩ := cover_anchor (h.1 hA) h.2.2.1 he Finset.univ
    refine ⟨E,F,h.trans h',?_⟩
    intro i b hb j hj
    rcases eq_or_lt_of_le (show j ≤ L by omega) with rfl | hj'
    · exact hnew i (Finset.mem_univ i) b hb
    · exact h'.1 (hold i b (h'.2.1 i hb) j hj')

#print axioms mixed_prefix_density
#print axioms cover_initial
end Erdos338.MixedDyson
