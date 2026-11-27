import ResidueCore
import Mathlib.Tactic

namespace Erdos338.Structural.ResidueCore.Examples
open Erdos338.CatalogueAdapter

def Sparse (b : Bool) : Set ℕ := {x | x = 1 ∨ (b = true ∧ x = 6) ∨
  ∃ j : ℕ, x = 5 * 10^j + 4}

def B (b : Bool) : Set ℕ := {x | x % 5 = 0 ∨ x ∈ Sparse b}

private theorem sparse_mod {b : Bool} {x : ℕ} (hx : x ∈ Sparse b) :
    x % 5 = 1 ∨ x % 5 = 4 := by
  rcases hx with rfl | ⟨_,rfl⟩ | ⟨j,rfl⟩ <;> omega

private theorem core (b : Bool) : ∀ a, a % 5 = 0 → a ∈ B b :=
  fun _ ha => Or.inl ha

private theorem outside_eq (b : Bool) : Outside (B b) 5 0 = Sparse b := by
  ext x
  change ((x % 5 = 0 ∨ x ∈ Sparse b) ∧ x % 5 ≠ 0) ↔ x ∈ Sparse b
  exact ⟨fun ⟨h,h'⟩ => h.resolve_left h',
    fun h => ⟨Or.inr h, fun e => by rcases sparse_mod h with z|z <;> omega⟩⟩

private theorem pow_lower (M : ℕ) : M + 10 ≤ (10:ℕ)^(M+1) := by
  induction M with
  | zero => decide
  | succ j ih => rw [pow_succ]; omega

private theorem rank_escape (b : Bool) {h : ℕ} (hh : h ≤ 4) :
    Escapes (Outside (B b) 5 0) 5 h := by
  rw [outside_eq]
  intro r hr M
  let X := (10:ℕ)^(M+1)
  have hX : M+10 ≤ X := pow_lower M
  refine ⟨30*X+r,by omega,by omega,?_⟩
  rintro ⟨xs,hl,hm,hs⟩
  have lim : ∀ x ∈ xs, x ≤ 5*X+4 := by
    intro x hx
    rcases hm x hx with rfl | ⟨_,rfl⟩ | ⟨j,rfl⟩
    · omega
    · omega
    · by_cases h' : j ≤ M+1
      · have hh' : (10:ℕ)^j ≤ X := Nat.pow_le_pow_right (by decide) h'
        omega
      · have hh' : 10*X ≤ (10:ℕ)^j := by
          rw [Nat.mul_comm, ←pow_succ]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        have hb := List.le_sum_of_mem hx
        rw [hs] at hb
        omega
  have hb : xs.sum ≤ xs.length * (5*X+4) := by
    clear hs hl
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := lim x (by simp)
      have h' := ih (fun y hy => hm y (by simp [hy])) (fun y hy => lim y (by simp [hy]))
      simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  have hb' := Nat.mul_le_mul_right (5*X+4) (show xs.length ≤ 4 by omega)
  omega

private theorem one (b : Bool) : Supplies (Outside (B b) 5 0) 5 1 1 := by
  rw [outside_eq]
  exact ⟨{1},by decide,by simp [Sparse]⟩

private theorem twoOnes : Supplies (Outside (B true) 5 0) 5 1 2 := by
  rw [outside_eq]
  refine ⟨{1,6},by decide,?_⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [Sparse]

private theorem fours (b : Bool) : Supplies (Outside (B b) 5 0) 5 4 3 := by
  rw [outside_eq]
  refine ⟨{9,54,504},by decide,?_⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨Or.inr (Or.inr ⟨0,by decide⟩),by decide⟩
  · exact ⟨Or.inr (Or.inr ⟨1,by decide⟩),by decide⟩
  · exact ⟨Or.inr (Or.inr ⟨2,by decide⟩),by decide⟩

private theorem supplies_le {S : Set ℕ} {q r i j : ℕ}
    (h : i ≤ j) : Supplies S q r j → Supplies S q r i := by
  rintro ⟨s,hs,hm⟩
  exact ⟨s,h.trans hs,hm⟩

private theorem available {b : Bool} {r : ℕ}
    (h : Supplies (Outside (B b) 5 0) 5 r 1) : r = 1 ∨ r = 4 := by
  rw [outside_eq] at h
  obtain ⟨s,hs,hm⟩ := h
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  exact (hm x hx).2 ▸ sparse_mod (hm x hx).1

private theorem not_twoOnes : ¬ Supplies (Outside (B false) 5 0) 5 1 2 := by
  rw [outside_eq]
  rintro ⟨s,hs,hm⟩
  have small : s ⊆ {1} := by
    intro x hx
    have ⟨hx',hmod⟩ := hm x hx
    rcases hx' with rfl | ⟨he,_⟩ | ⟨i,rfl⟩
    · simp
    · cases he
    · omega
  have hc := Finset.card_le_card small
  simp at hc
  omega

private theorem zeroProfile (b d : Bool) (h : ℕ) (hh : 1 ≤ h) :
    Profile (Outside (B b) 5 0) 5 0 h 0 d :=
  ⟨1,[],by decide,by simpa,by simp,fun _ _ => ⟨∅,by simp,by simp⟩,by decide⟩

private theorem repeatedProfile (b d : Bool) (h r w l : ℕ)
    (hh : 1+l ≤ h) (hm : (List.replicate l w).sum % 5 = r)
    (one : Supplies (Outside (B b) 5 0) 5 w 1)
    (cap : d = true → Supplies (Outside (B b) 5 0) 5 w l) :
    Profile (Outside (B b) 5 0) 5 0 h r d := by
  refine ⟨1,List.replicate l w,by decide,by simpa,?_,?_,by simpa using hm⟩
  · intro u hu
    have e : u = w := List.eq_of_mem_replicate hu
    exact e.symm ▸ one
  · intro hd u
    by_cases e : u = w
    · subst u
      simpa using cap hd
    · have ez : (List.replicate l w).count u = 0 :=
        List.count_eq_zero_of_not_mem (fun hm => e (List.eq_of_mem_replicate hm))
      exact ⟨∅,by simp [ez],by simp⟩

private theorem profiles_ord (b : Bool) (r : ℕ) (hr : r < 5) :
    Profile (Outside (B b) 5 0) 5 0 3 r false := by
  interval_cases r
  · exact zeroProfile b false 3 (by decide)
  · exact repeatedProfile b false 3 1 1 1 (by decide) (by decide) (one b) (by simp)
  · exact repeatedProfile b false 3 2 1 2 (by decide) (by decide) (one b) (by simp)
  · exact repeatedProfile b false 3 3 4 2 (by decide) (by decide)
      (supplies_le (by decide) (fours b)) (by simp)
  · exact repeatedProfile b false 3 4 4 1 (by decide) (by decide)
      (supplies_le (by decide) (fours b)) (by simp)

private theorem profiles_strict (r : ℕ) (hr : r < 5) :
    Profile (Outside (B false) 5 0) 5 0 4 r true := by
  interval_cases r
  · exact zeroProfile false true 4 (by decide)
  · exact repeatedProfile false true 4 1 1 1 (by decide) (by decide) (one _) (fun _ => one _)
  · exact repeatedProfile false true 4 2 4 3 (by decide) (by decide)
      (supplies_le (by decide) (fours _)) (fun _ => fours _)
  · exact repeatedProfile false true 4 3 4 2 (by decide) (by decide)
      (supplies_le (by decide) (fours _)) (fun _ => supplies_le (by decide) (fours _))
  · exact repeatedProfile false true 4 4 4 1 (by decide) (by decide)
      (supplies_le (by decide) (fours _)) (fun _ => supplies_le (by decide) (fours _))

private theorem profiles_equal (r : ℕ) (hr : r < 5) :
    Profile (Outside (B true) 5 0) 5 0 3 r true := by
  interval_cases r
  · exact zeroProfile true true 3 (by decide)
  · exact repeatedProfile true true 3 1 1 1 (by decide) (by decide) (one _) (fun _ => one _)
  · exact repeatedProfile true true 3 2 1 2 (by decide) (by decide) (one _) (fun _ => twoOnes)
  · exact repeatedProfile true true 3 3 4 2 (by decide) (by decide)
      (supplies_le (by decide) (fours _)) (fun _ => supplies_le (by decide) (fours _))
  · exact repeatedProfile true true 3 4 4 1 (by decide) (by decide)
      (supplies_le (by decide) (fours _)) (fun _ => supplies_le (by decide) (fours _))

private theorem no_ord_small (b : Bool) (h : ℕ) (hh : h < 3) :
    ¬ Profile (Outside (B b) 5 0) 5 0 h 2 false := by
  rintro ⟨k,xs,hk,hl,hm,_,hs⟩
  cases xs with
  | nil => simp at hs
  | cons a xs =>
    have ha := available (hm a (by simp))
    cases xs with
    | nil => simp at hs; omega
    | cons b xs => simp at hl; omega

private theorem no_dist_small (h : ℕ) (hh : h < 4) :
    ¬ Profile (Outside (B false) 5 0) 5 0 h 2 true := by
  rintro ⟨k,xs,hk,hl,hm,hcap,hs⟩
  cases xs with
  | nil => simp at hs
  | cons a xs =>
    have ha := available (hm a (by simp))
    cases xs with
    | nil => simp at hs; omega
    | cons b xs =>
      have hb := available (hm b (by simp))
      cases xs with
      | nil =>
        simp at hs
        have eqs : a=1 ∧ b=1 := by omega
        obtain ⟨rfl,rfl⟩ := eqs
        exact not_twoOnes (by simpa using hcap rfl 1)
      | cons c xs => simp at hl; omega

theorem example_ordinary (b : Bool) : basisOrder (B b) = (3 : ℕ∞) := by
  change (⨅ (n : ℕ) (_ : HasOrder (B b) n), (n : ℕ∞)) = ((3 : ℕ) : ℕ∞)
  rw [least_budget_iff]
  constructor
  · apply (ordinary_iff_finite_profile (by decide) (by decide) (core b) (rank_escape b (by decide))).mpr
    exact profiles_ord b
  · intro h hh H
    have E := rank_escape b (by omega : h ≤ 4)
    exact no_ord_small b h hh
      ((ordinary_iff_finite_profile (by decide) (by decide) (core b) E).mp H 2 (by decide))

theorem example_strict : restrictedOrder (B false) = (4 : ℕ∞) := by
  change (⨅ (n : ℕ) (_ : HasRestrictedOrder (B false) n), (n : ℕ∞)) = ((4 : ℕ) : ℕ∞)
  rw [least_budget_iff]
  constructor
  · apply (restricted_iff_finite_profile (by decide) (by decide) (core _) (rank_escape _ (by decide))).mpr
    exact profiles_strict
  · intro h hh H
    have E := rank_escape false (by omega : h ≤ 4)
    exact no_dist_small h hh
      ((restricted_iff_finite_profile (by decide) (by decide) (core _) E).mp H 2 (by decide))

theorem example_equal : restrictedOrder (B true) = (3 : ℕ∞) := by
  exact (equal_orders_iff_finite_profile (example_ordinary true) (by decide) (by decide)
    (core _) (rank_escape _ (by decide))).mpr profiles_equal


theorem example_same_tail : ∀ x ≥ 7, x ∈ B false ↔ x ∈ B true := by
  intro x hx
  change (x % 5 = 0 ∨ x = 1 ∨ (false = true ∧ x = 6) ∨ ∃ j : ℕ, x = 5*10^j+4) ↔
    (x % 5 = 0 ∨ x = 1 ∨ (true = true ∧ x = 6) ∨ ∃ j : ℕ, x = 5*10^j+4)
  have h1 : x ≠ 1 := by omega
  have h6 : x ≠ 6 := by omega
  simp [h1,h6]

theorem example_nonperiodic (b : Bool) :
    ¬ ∃ p > 0, ∃ N, ∀ x ≥ N, x ∈ B b ↔ x+p ∈ B b := by
  rintro ⟨p,hp,N,per⟩
  let j := N+p+1
  let X := (10:ℕ)^j
  have hX : N+p+10 ≤ X := pow_lower (N+p)
  let n := 5*X+4
  have hN : N ≤ n := by dsimp [n]; omega
  have hn : n ∈ B b := Or.inr (Or.inr (Or.inr ⟨j,rfl⟩))
  have H (k : ℕ) : n+k*p ∈ B b := by
    induction k with
    | zero => simpa
    | succ k ih =>
      rw [Nat.succ_mul, ←Nat.add_assoc]
      exact (per _ (hN.trans (Nat.le_add_right n (k*p)))).mp ih
  rcases H 5 with hx | hx
  · dsimp [n] at hx
    omega
  · rcases hx with hx | ⟨_,hx⟩ | ⟨i,hi⟩
    · dsimp [n] at hx; omega
    · dsimp [n] at hx; omega
    · by_cases h : i ≤ j
      · have hl : (10:ℕ)^i ≤ X := Nat.pow_le_pow_right (by decide) h
        dsimp [n] at hi
        omega
      · have hl : 10*X ≤ (10:ℕ)^i := by
          rw [Nat.mul_comm, ←pow_succ]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        dsimp [n] at hi
        omega

end Erdos338.Structural.ResidueCore.Examples
