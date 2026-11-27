import MixedDyson
import Erdos335.WindowEstimates

/-! Normalization for mixed sums of finitely many (possibly finite) summands.
When the joint prefix slope exceeds one, the first good window starts in a donor.
This eliminates the single-summand first-window correction; shifting each donor
costs at most one unit. -/
open scoped BigOperators
open Erdos335
namespace Erdos338.MixedDyson
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem find_window (A : Set ℕ) (B : ι → Set ℕ) {γ : ℝ}
    (ev : ∃ K : ℕ, ∀ N ≥ K, γ * N ≤ (mass A B N : ℝ)) :
    ∃ s : ℕ, 0 < s ∧ (∀ N ≥ s, γ * N ≤ (mass A B N : ℝ)) ∧
      (mass A B (s - 1) : ℝ) ≤ γ * (s - 1 : ℕ) := by
  classical
  let P (s : ℕ) := 0 < s ∧ ∀ N ≥ s, γ * N ≤ (mass A B N : ℝ)
  obtain ⟨K,hK⟩ := ev
  have hex : ∃ s, P s := ⟨max 1 K, by omega, fun N hN => hK N (by omega)⟩
  let s := Nat.find hex
  obtain ⟨hs,ha⟩ := Nat.find_spec hex
  refine ⟨s,hs,ha,?_⟩
  by_cases h : s=1
  · simp [h,mass,count_zero]
  by_contra! hg
  have hp : P (s-1) := by
    refine ⟨by omega, fun N hN => ?_⟩
    rcases eq_or_lt_of_le hN with rfl | hh
    · exact hg.le
    · exact ha N (by omega)
  exact Nat.find_min hex (by dsimp [s]; omega) hp

private theorem donor_at_window (A : Set ℕ) (B : ι → Set ℕ) {s : ℕ} (hs : 0 < s)
    {γ : ℝ} (hγ : 1 < γ) (hat : γ*s ≤ (mass A B s : ℝ))
    (hprev : (mass A B (s-1) : ℝ) ≤ γ * (s-1 : ℕ)) : ∃ i, s ∈ B i := by
  classical
  by_contra! he
  have hA := count_succ A (s-1)
  rw [show s-1+1=s by omega] at hA
  have hAL : count A s ≤ count A (s-1)+1 := by split at hA <;> omega
  have hB (i : ι) : count (B i) s = count (B i) (s-1) := by
    have h := count_succ (B i) (s-1)
    rw [show s-1+1=s by omega] at h
    simpa only [he i, ite_false,add_zero] using h
  have hm : mass A B s ≤ mass A B (s-1)+1 := by
    simp only [mass,hB]; omega
  have hmR : (mass A B s : ℝ) ≤ (mass A B (s-1) : ℝ) + 1 := by exact_mod_cast hm
  rw [Nat.cast_sub hs, Nat.cast_one] at hprev
  nlinarith

private theorem window_bound (A : Set ℕ) (B : ι → Set ℕ) {s : ℕ} (hs : 0 < s)
    {γ : ℝ} (ha : ∀ N ≥ s, γ*N ≤ (mass A B N : ℝ))
    (hp : (mass A B (s-1) : ℝ) ≤ γ*(s-1 : ℕ)) (N : ℕ) :
    γ*(N+1 : ℕ) ≤ (prefixCount (tailShift A s) (N+1) : ℝ) +
      ∑ i, (prefixCount (tailShift (B i) s) (N+1) : ℝ) := by
  have hsum :
      prefixCount (tailShift A s) (N+1) + (∑ i, prefixCount (tailShift (B i) s) (N+1)) +
      mass A B (s-1) = mass A B (s+N) := by
    unfold mass
    have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset ι)) rfl
      (fun i _ => prefixCount_tailShift_eq_window (B i) hs N)
    rw [Finset.sum_add_distrib] at hh
    have h := prefixCount_tailShift_eq_window A hs N
    omega
  have hsumR : (prefixCount (tailShift A s) (N+1) : ℝ) +
      (∑ i, (prefixCount (tailShift (B i) s) (N+1) : ℝ)) + mass A B (s-1) =
      (mass A B (s+N) : ℝ) := by exact_mod_cast hsum
  have hatt := ha (s+N) (by omega)
  rw [Nat.cast_sub hs,Nat.cast_one] at hp
  push_cast at hatt ⊢
  nlinarith

/-- A donor shift bounding an arbitrary positive prefix window, even if no donor
element exceeds the window's left endpoint (in which case choose zero). -/
private theorem donor_shift (B : Set ℕ) (h0 : 0 ∈ B) (s : ℕ) :
    ∃ t ∈ B, ∀ N, prefixCount (tailShift B s) (N+1) ≤ count (tailShift B t) N + 1 := by
  classical
  by_cases h : ∃ t : ℕ, t ∈ B ∧ s ≤ t
  · obtain ⟨ht,hst⟩ := Nat.find_spec h
    exact ⟨Nat.find h,ht,prefixCount_tailShift_le_count_first B hst ht
      (fun n hn hsn => Nat.find_min' h ⟨hn,hsn⟩)⟩
  · refine ⟨0,h0,fun N => ?_⟩
    have hzp : prefixCount (tailShift B s) (N+1) = 0 := by
      unfold prefixCount
      rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
      intro n _ hn
      exact h ⟨n+s, hn, by omega⟩
    omega

/-- A sufficiently long covered interval forces the mixed set to be cofinite.
No infinitude, individual density, or independent liminf hypotheses on the
donors are needed. -/
theorem cofinite_of_cover (A : Set ℕ) (B : ι → Set ℕ) {γ : ℝ} (hγ : 1 < γ)
    (hden : ∃ N0 : ℕ, ∀ n ≥ N0, γ*n ≤ (mass A B n : ℝ))
    (hB : ∀ i, 0 ∈ B i) (L : ℕ) (hL : 0 < L)
    (hblock : ∀ i, ∀ b ∈ B i, ∀ j < L, b+j ∈ A)
    (hweight : (Fintype.card ι : ℝ) ≤ (γ-1)*L) :
    ∃ T : ℕ, ∀ n ≥ T, n ∈ mixed A B := by
  classical
  obtain ⟨s,hs,ha,hp⟩ := find_window A B hden
  obtain ⟨i,hi⟩ := donor_at_window A B hs hγ (ha s le_rfl) hp
  have hinit (j : ℕ) (hj : j < L) : j ∈ tailShift A s := by
    change j+s ∈ A
    simpa only [Nat.add_comm] using hblock i s hi j hj
  choose t ht htN using fun i => donor_shift (B i) (hB i) s
  have hD0 (i : ι) : 0 ∈ tailShift (B i) (t i) := by simpa [tailShift] using ht i
  have hI : Budget (tailShift A s) (fun i => tailShift (B i) (t i)) 1 0 := by
    intro N
    simp only [one_mul,Nat.sub_zero]
    by_cases hsmall : N+1 ≤ L
    · have hleft := prefixCount_full_block (tailShift A s) 0 L
          (by simpa using hinit) (N+1) hsmall
      simp [prefixCount] at hleft
      have hlow : (N+1 : ℕ) ≤ prefixCount (tailShift A s) (N+1) := by
        change _ ≤ ((Finset.range _).filter _).card
        omega
      have hR : ((N+1 : ℕ) : ℝ) ≤ prefixCount (tailShift A s) (N+1) := by exact_mod_cast hlow
      exact le_add_of_le_of_nonneg hR (by positivity)
    · have hbig : (L : ℝ) ≤ (N+1 : ℕ) := by exact_mod_cast (show L ≤ N+1 by omega)
      have hcost := mul_le_mul_of_nonneg_left hbig (by linarith : 0 ≤ γ-1)
      have hsum : (∑ i, (prefixCount (tailShift (B i) s) (N+1) : ℝ)) ≤
          ∑ i, ((count (tailShift (B i) (t i)) N : ℝ)+1) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast htN i N
      rw [Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hsum
      have hw := window_bound A B hs ha hp N
      nlinarith
  have hfull : mixed (tailShift A s) (fun i => tailShift (B i) (t i)) = Set.univ := by
    apply eq_univ_of_full_prefixCount
    intro N
    cases N with
    | zero => simp [prefixCount]
    | succ N => simpa using mixed_prefix_density (hinit 0 hL) hD0 hI N
  refine ⟨s+∑ i, t i, fun n hn => ?_⟩
  have hx : n-(s+∑ i, t i) ∈ mixed (tailShift A s) (fun i => tailShift (B i) (t i)) := by
    rw [hfull]; trivial
  obtain ⟨a,ha',b,hb,he⟩ := hx
  refine ⟨a+s,ha',fun i => b i+t i, hb, ?_⟩
  rw [Finset.sum_add_distrib]
  omega

/-- Stable passage through a bounded prefix-count loss. -/
theorem slope_of_bounded_loss {f g : ℕ → ℕ} {γ δ : ℝ} (hδ : δ < γ) (M : ℝ)
    (hfg : ∀ N, (f N : ℝ) ≤ (g N : ℝ)+M)
    (hf : ∃ K : ℕ, ∀ N ≥ K, γ*N ≤ (f N : ℝ)) :
    ∃ K : ℕ, ∀ N ≥ K, δ*N ≤ (g N : ℝ) := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨T,hT⟩ := exists_nat_ge (M/(γ-δ))
  refine ⟨max K T, fun N hN => ?_⟩
  have hN' : (T : ℝ) ≤ N := by exact_mod_cast (show T ≤ N by omega)
  have hM := (div_le_iff₀ (by linarith : 0 < γ-δ)).mp (hT.trans hN')
  have hh := hK N (by omega); have hhh := hfg N
  nlinarith

/-- One left-hand block is enough: choosing a lower slope absorbs the finite
cost of normalization, including all the preliminary Dyson steps. -/
theorem cofinite_of_one_long_block (A : Set ℕ) (B : ι → Set ℕ) {γ δ : ℝ}
    (hδ : 1 < δ) (hδγ : δ < γ)
    (hden : ∃ K : ℕ, ∀ N ≥ K, γ*N ≤ (mass A B N : ℝ))
    (hB : ∀ i, 0 ∈ B i) (L : ℕ) (hL : 0 < L)
    (hweight : (Fintype.card ι : ℝ) ≤ (δ-1)*L)
    (u : ℕ) (hblock : ∀ j < L, u+j ∈ A) :
    ∃ T : ℕ, ∀ n ≥ T, n ∈ mixed A B := by
  classical
  let A' := tailShift A u
  have hinit (j : ℕ) (hj : j < L) : j ∈ A' := by
    change j+u ∈ A
    simpa only [Nat.add_comm] using hblock j hj
  obtain ⟨C,D,hCD,hcov⟩ := cover_initial (hinit 0 hL) hB L hinit
  obtain ⟨_,_,hD0,hsub,M,hM⟩ := hCD
  have hc (N : ℕ) : (mass A B N : ℝ) ≤ (mass C D N : ℝ) + ((u : ℝ)+2+M) := by
    have h := (abs_le.mp (count_tailShift_error A u N)).1
    have hcmp : (mass A' B N : ℝ) ≤ (mass C D N : ℝ) + M := by exact_mod_cast hM N
    have hraw : (mass A B N : ℝ) ≤ (mass A' B N : ℝ) + ((u : ℝ)+2) := by
      simp only [mass,Nat.cast_add,Nat.cast_sum,A']
      linarith
    linarith
  have hCden := slope_of_bounded_loss hδγ _ hc hden
  obtain ⟨T,hT⟩ := cofinite_of_cover C D hδ hCden hD0 L hL hcov hweight
  refine ⟨u+T, fun n hn => ?_⟩
  obtain ⟨a,ha,b,hb,hs⟩ := hsub (hT (n-u) (by omega))
  exact ⟨a+u,ha,b,hb,by omega⟩

/-- Arbitrarily long left-hand blocks plus a joint mixed prefix slope greater
than one imply cofiniteness, including in the presence of finite donors. -/
theorem cofinite_of_long_blocks (A : Set ℕ) (B : ι → Set ℕ) {γ : ℝ}
    (hγ : 1 < γ)
    (hden : ∃ K : ℕ, ∀ N ≥ K, γ*N ≤ (mass A B N : ℝ))
    (hB : ∀ i, 0 ∈ B i) (hblocks : ∀ L : ℕ, ∃ u : ℕ, ∀ j < L, u+j ∈ A) :
    ∃ T : ℕ, ∀ n ≥ T, n ∈ mixed A B := by
  let δ := (1+γ)/2
  have hd : 1 < δ := by dsimp [δ]; linarith
  obtain ⟨k,hk⟩ := exists_nat_ge ((Fintype.card ι : ℝ)/(δ-1))
  obtain ⟨u,hu⟩ := hblocks (k+1)
  refine cofinite_of_one_long_block A B hd (by dsimp [δ]; linarith) hden hB (k+1)
    (by omega) ?_ u hu
  have hh := (div_le_iff₀ (by linarith : 0 < δ-1)).mp hk
  push_cast
  nlinarith

#print axioms cofinite_of_cover
#print axioms cofinite_of_long_blocks
end Erdos338.MixedDyson
