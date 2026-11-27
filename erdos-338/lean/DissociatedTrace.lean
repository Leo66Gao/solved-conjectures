import StructuralTrace

/-! Dissociated Minkowski traces. The coefficient bound is fixed in advance;
there is no relation-length bound. The digit uniqueness condition only asks
about arithmetic inside one individual permanent cell. -/
open Filter
open scoped BigOperators
namespace Erdos338.SparseTrace
open CatalogueAdapter

def DigitUnique (M : ℕ) (S : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (∀ x ∈ F, x ∈ S) →
  ∀ f g : ℕ → ℕ, (∀ x ∈ F, f x ≤ M ∧ g x ≤ M) →
  (∑ x ∈ F, f x * x) = (∑ x ∈ F, g x * x) →
  ∀ x ∈ F, f x = g x

/-- Every element strictly dominates every finite smaller positive digit sum. -/
theorem weighted_domination {M : ℕ} {S : Set ℕ}
    (hs : Sparse (fun x => (M+1)*x) S) {z : ℕ} (hz : 0 < z) (hzS : z ∈ S)
    (F : Finset ℕ) (hf : ∀ x ∈ F, 0 < x ∧ x ∈ S ∧ x < z)
    (f : ℕ → ℕ) (hm : ∀ x ∈ F, f x ≤ M) : ∑ x ∈ F, f x*x < z := by
  classical
  generalize he : F.card = n
  induction n using Nat.strong_induction_on generalizing F z with
  | h n ih =>
    by_cases heF : F.Nonempty
    · let a := F.max' heF
      have ha : a ∈ F := Finset.max'_mem _ _
      have ⟨ha0,haS,haz⟩ := hf a ha
      have hR (x : ℕ) (hx : x ∈ F.erase a) : 0 < x ∧ x ∈ S ∧ x < a := by
        obtain ⟨hn,hx⟩ := Finset.mem_erase.mp hx
        exact ⟨(hf x hx).1,(hf x hx).2.1,lt_of_le_of_ne (Finset.le_max' F x hx) hn⟩
      have card : (F.erase a).card < n := by rw [← he]; exact Finset.card_erase_lt_of_mem ha
      have tail := ih _ card ha0 haS _ hR (fun x hx => hm x (Finset.mem_of_mem_erase hx)) rfl
      have gap := hs a haS z hzS haz
      have hi := Nat.mul_le_mul_right a (hm a ha)
      change (M+1)*a < z at gap
      rw [Nat.add_mul, one_mul] at gap
      rw [← Finset.sum_erase_add _ _ ha]
      omega
    · have h := Finset.not_nonempty_iff_eq_empty.mp heF
      simp [h,hz]

/-- Arbitrarily long bounded-coefficient relations inside one separated
positive column are trivial. -/
theorem sparse_digit_unique {M : ℕ} {S : Set ℕ}
    (positive : ∀ x ∈ S, 0 < x) (hs : Sparse (fun x => (M+1)*x) S) :
    DigitUnique M S := by
  classical
  intro F hF f g hm sm
  generalize he : F.card = n
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases heF : F.Nonempty
    · let a := F.max' heF
      have ha : a ∈ F := Finset.max'_mem _ _
      have haS := hF a ha
      have ha0 := positive a haS
      let R := F.erase a
      have hR (x : ℕ) (hx : x ∈ R) : 0 < x ∧ x ∈ S ∧ x < a := by
        obtain ⟨hn,hx⟩ := Finset.mem_erase.mp hx
        exact ⟨positive x (hF x hx),hF x hx,lt_of_le_of_ne (Finset.le_max' F x hx) hn⟩
      have lf := weighted_domination hs ha0 haS R hR f (fun x hx => (hm _ (Finset.mem_of_mem_erase hx)).1)
      have lg := weighted_domination hs ha0 haS R hR g (fun x hx => (hm _ (Finset.mem_of_mem_erase hx)).2)
      have eq : (∑ x ∈ R, f x*x) + f a*a = (∑ x ∈ R, g x*x) + g a*a := by
        unfold R
        simpa only [Finset.sum_erase_add _ _ ha] using sm
      have digit : f a = g a := by
        rcases lt_trichotomy (f a) (g a) with l|e|r
        · have p := Nat.mul_le_mul_right a (Nat.succ_le_of_lt l)
          rw [Nat.succ_mul] at p
          omega
        · exact e
        · have p := Nat.mul_le_mul_right a (Nat.succ_le_of_lt r)
          rw [Nat.succ_mul] at p
          omega
      rw [digit] at eq
      have tail := Nat.add_right_cancel eq
      have hc : R.card < n := by rw [← he]; exact Finset.card_erase_lt_of_mem ha
      have H := ih _ hc R (fun x hx => hF _ (Finset.mem_of_mem_erase hx))
        (fun x hx => hm _ (Finset.mem_of_mem_erase hx)) tail rfl
      intro x hx
      by_cases e : x = a
      · exact e ▸ digit
      · exact H x (Finset.mem_erase.mpr ⟨e,hx⟩)
    · exact fun _ hx => (heF ⟨_,hx⟩).elim

private theorem positive_rank {A : Set ℕ} {h : ℕ} (H : HasRestrictedOrder A h) :
    HasRestrictedOrder {n | n ∈ A ∧ 0 < n} h := by
  apply H.mono
  rintro n ⟨U,hU,hc,sm⟩
  refine ⟨U.erase 0,?_,(Finset.card_le_card (Finset.erase_subset _ _)).trans hc,?_⟩
  · intro x hx
    obtain ⟨hn,hx⟩ := Finset.mem_erase.mp hx
    exact ⟨hU _ hx,Nat.pos_of_ne_zero hn⟩
  · by_cases hz : 0 ∈ U
    · simpa using ((Finset.sum_erase_add U (fun x => x) hz).trans sm)
    · simpa [Finset.erase_eq_of_notMem hz] using sm

/-- Ordinary rectangles whose cells are positive and have unique
bounded-coefficient subset sums of every finite length. -/
def DigitTrace (A : Set ℕ) (h M : ℕ) : Prop :=
  ∀ T : Set ℕ, Unbounded T →
    ∃ (k : ℕ) (_ : k ≤ h) (B : Fin k → Set ℕ),
      (∀ i, B i ⊆ A) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, DigitUnique M (B i)) ∧ Unbounded (T ∩ box B)

theorem restricted_iff_digit_trace (A : Set ℕ) (h M : ℕ) :
    HasRestrictedOrder A h ↔ DigitTrace A h M := by
  constructor
  · intro hr T hT
    obtain ⟨k,hk,B,hBA,hd,hs,hb⟩ :=
      (restricted_iff_sparse_trace _ _).mp (positive_rank hr) T hT (fun x => (M+1)*x)
    refine ⟨k,hk,B,(fun i _ hx => (hBA i hx).1),hd,(fun i => ?_),hb⟩
    exact sparse_digit_unique (fun _ hx => (hBA i hx).2) (hs i)
  · intro hd
    classical
    rw [HasRestrictedOrder, eventually_atTop]
    by_contra! ne
    let T := (hit A h)ᶜ
    have hu : Unbounded T := by
      intro N
      obtain ⟨n,hn,ne⟩ := ne (N+1)
      refine ⟨n,by omega,?_⟩
      change ¬ ∃ S : Finset ℕ, _
      push Not
      exact ne
    obtain ⟨k,hk,B,ba,ds,_,hb⟩ := hd T hu
    obtain ⟨n,_,hne,f,hf,sm⟩ := hb 0
    have inj : Function.Injective f := by
      intro i j e
      by_contra hij
      exact Set.disjoint_left.mp (ds i j hij) (hf i) (e ▸ hf j)
    apply hne
    refine ⟨Finset.univ.image f,?_,?_,?_⟩
    · rintro _ hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ba i (hf i)
    · exact le_trans Finset.card_image_le (by simpa using hk)
    · simpa [Finset.sum_image (s:=Finset.univ) (f:=fun x => x)
        (fun _ _ _ _ eq => inj eq)] using sm

theorem equal_orders_iff_digit_trace {A : Set ℕ} {h : ℕ} (ord : basisOrder A = (h : ℕ∞))
    (M : ℕ) : restrictedOrder A = basisOrder A ↔ DigitTrace A h M :=
  (equal_orders_iff_sparse_trace ord).trans
    ((restricted_iff_sparse_trace A h).symm.trans (restricted_iff_digit_trace A h M))

/-- A countable menu of globally fixed trace sets cannot pass every infinite
target test unless a finite initial menu already covers a tail. In particular
the uncountable T-dependent choice in the unrestricted trace criterion cannot
in general be replaced by a guessed countable list of thin rectangles. -/
theorem simultaneous_escape (C : ℕ → Set ℕ)
    (miss : ∀ j N : ℕ, ∃ n > N, ∀ i ≤ j, n ∉ C i) :
    ∃ T : Set ℕ, Unbounded T ∧ ∀ j, ∃ N, ∀ n > N, n ∈ T → n ∉ C j := by
  classical
  choose t ht avoid using fun j => miss j j
  refine ⟨Set.range t, fun N => ⟨t N, ht N, N, rfl⟩, ?_⟩
  intro j
  refine ⟨(Finset.range j).sup t, ?_⟩
  rintro _ hn ⟨i,rfl⟩
  by_cases hi : j ≤ i
  · exact avoid i _ hi
  · have bound := Finset.le_sup (f:=t) (Finset.mem_range.mpr (Nat.lt_of_not_ge hi))
    omega

#print axioms simultaneous_escape
#print axioms sparse_digit_unique
#print axioms equal_orders_iff_digit_trace
end Erdos338.SparseTrace
