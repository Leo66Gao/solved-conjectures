import CatalogueAdapter
import Mathlib.Algebra.Polynomial.Coeff

/-! # Ordinary representation response to random thinning
The public invariant `response` uses ordinary representation counts on
subsets of [0,n], not a query to any distinct-summand solver. Its Bernstein
expectation is defined recursively by independent keep/drop decisions.
The support/cardinality only enters the *proof* of its response law.
-/
namespace Erdos338.Thinning
open Polynomial
open Erdos338.CatalogueAdapter

def words (alph : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k+1 => alph.flatMap (fun a => (words alph k).map (a :: ·))

theorem mem_words {b : List ℕ} {k : ℕ} {w : List ℕ} :
    w ∈ words b k ↔ w.length = k ∧ ∀ a ∈ w, a ∈ b := by
  induction k generalizing w with
  | zero => cases w <;> simp [words]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons a l =>
      simp only [words, List.mem_flatMap, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨x,hx,t,ht,rfl,rfl⟩
        obtain ⟨hl, hb⟩ := ih.mp ht
        exact ⟨hl, by simpa [hx] using hb⟩
      · rintro ⟨hl, hb⟩
        have hb' := List.forall_mem_cons.mp hb
        exact ⟨a, hb'.1, l, ih.mpr ⟨hl, hb'.2⟩, rfl, rfl⟩

/-- Finite list of ordered ordinary representations of exact arity k. -/
noncomputable def fiber (A : Set ℕ) (k n : ℕ) : List (List ℕ) := by
  classical
  exact (words (List.range (n+1)) k).filter (fun l => decide (l.sum = n ∧ ∀ a ∈ l, a ∈ A))

theorem mem_fiber (A : Set ℕ) (k n : ℕ) (l : List ℕ) :
    l ∈ fiber A k n ↔ l.length = k ∧ l.sum = n ∧ ∀ a ∈ l, a ∈ A := by
  classical
  simp only [fiber, List.mem_filter, decide_eq_true_eq, mem_words]
  constructor
  · rintro ⟨⟨hh,_⟩,hr⟩; exact ⟨hh,hr⟩
  · rintro ⟨hl,hs,ha⟩
    refine ⟨⟨hl,?_⟩,hs,ha⟩
    intro x hx
    have := List.le_sum_of_mem hx
    apply List.mem_range.mpr
    omega

abbrev Poly := Polynomial ℤ

noncomputable def mean : List ℕ → (Finset ℕ → Poly) → Finset ℕ → Poly
  | [], f, S => f S
  | x :: l, f, S => (1-X) * mean l f (S.erase x) + X * mean l f S

private theorem mean_add (l : List ℕ) (f g : Finset ℕ → Poly) (S : Finset ℕ) :
    mean l (fun s => f s + g s) S = mean l f S + mean l g S := by
  induction l generalizing S with
  | nil => rfl
  | cons x l ih => simp only [mean, ih, mul_add]; ac_rfl

private theorem mean_zero (l : List ℕ) (S : Finset ℕ) :
    mean l (fun _ => 0) S = 0 := by induction l generalizing S <;> simp_all [mean]

noncomputable def survives (T S : Finset ℕ) : Poly := if T ⊆ S then 1 else 0

theorem mean_survives (T : Finset ℕ) (l : List ℕ) (hl : l.Nodup) (S : Finset ℕ) :
    mean l (survives T) S =
      if T ⊆ S then X ^ (T ∩ l.toFinset).card else 0 := by
  induction l generalizing S with
  | nil => simp [mean, survives]
  | cons x l ih =>
    obtain ⟨hn,hl⟩ := List.nodup_cons.mp hl
    simp only [mean, ih hl, List.toFinset_cons, Finset.subset_erase]
    by_cases hT : T ⊆ S
    · by_cases hx : x ∈ T
      · have hx' : x ∉ T ∩ l.toFinset := by simp [hn]
        simp [hT,hx,Finset.inter_insert_of_mem hx,Finset.card_insert_of_notMem hx', pow_succ',mul_comm]
      · simp only [hT,hx,not_false_eq_true,and_self,ite_true,Finset.inter_insert_of_notMem hx]
        rw [sub_mul, one_mul, sub_add_cancel]
    · simp [hT]

/-- An ordinary count, i.e. sum of one for each surviving ordered tuple.
The indicator here requires membership, not pairwise distinctness. -/
noncomputable def ordinaryPanel (F : List (List ℕ)) (S : Finset ℕ) : Poly :=
  (F.map (fun w => survives w.toFinset S)).sum

private theorem filtered_panel (F : List (List ℕ)) (S : Finset ℕ) :
    ordinaryPanel F S = ((F.filter (fun w => decide (w.toFinset ⊆ S))).length : Poly) := by
  induction F with
  | nil => simp [ordinaryPanel]
  | cons w l ih =>
    by_cases hs : w.toFinset ⊆ S
    · change survives w.toFinset S + ordinaryPanel l S = _
      simp [hs,survives,ih,add_comm]
    · change survives w.toFinset S + ordinaryPanel l S = _
      simp [hs,survives,ih]

/-- A mask-reading algorithm needs only the ordinary count on its retained
subbasis. This identity points to the actual observable. -/
theorem ordinaryPanel_restriction (A : Set ℕ) (k n : ℕ) (S : Finset ℕ) :
    ordinaryPanel (fiber A k n) S = ((fiber (A ∩ (S : Set ℕ)) k n).length : Poly) := by
  classical
  rw [filtered_panel]
  suffices (fiber A k n).filter (fun w => decide (w.toFinset ⊆ S)) =
      fiber (A ∩ (S : Set ℕ)) k n by rw [this]
  unfold fiber
  rw [List.filter_filter]
  apply List.filter_congr
  intro w _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq,Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hS,hn,hA⟩
    exact ⟨hn,fun x hx => ⟨hA x hx,hS (List.mem_toFinset.mpr hx)⟩⟩
  · rintro ⟨hn,hAS⟩
    exact ⟨fun x hx => (hAS x (List.mem_toFinset.mp hx)).2,hn,fun x hx => (hAS x hx).1⟩

/-- The ordinary representation response polynomial: exact mean over independent
retention of each input integer with symbolic probability X. -/
noncomputable def response (A : Set ℕ) (k n : ℕ) : Poly :=
  mean (List.range (n+1)) (ordinaryPanel (fiber A k n)) (Finset.range (n+1))

private theorem mean_panel (F : List (List ℕ)) (l : List ℕ) (S : Finset ℕ) :
    mean l (ordinaryPanel F) S =
      (F.map (fun w => mean l (survives w.toFinset) S)).sum := by
  induction F with
  | nil => exact mean_zero l S
  | cons w F ih =>
    change mean l (fun t => survives w.toFinset t + ordinaryPanel F t) S = _
    rw [mean_add, ih]; rfl

theorem response_expansion (A : Set ℕ) (k n : ℕ) :
    response A k n = ((fiber A k n).map (fun w => (X : Poly)^w.toFinset.card)).sum := by
  classical
  unfold response
  rw [mean_panel]
  congr 1
  apply List.map_congr_left
  intro w hw
  obtain ⟨_, hs, _⟩ := (mem_fiber A k n w).mp hw
  have sub : w.toFinset ⊆ Finset.range (n+1) := by
    intro a ha
    have := List.le_sum_of_mem (List.mem_toFinset.mp ha)
    apply Finset.mem_range.mpr
    omega
  simp [mean_survives _ _ List.nodup_range _, sub, List.toFinset_range, Finset.inter_eq_left.mpr sub]

private theorem card_eq_len (w : List ℕ) : w.toFinset.card = w.length ↔ w.Nodup := by
  induction w with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a ∈ l
    · have h := List.toFinset_card_le l
      simp [ha, Finset.insert_eq_of_mem (List.mem_toFinset.mpr ha)]
      omega
    · simpa [ha, Finset.card_insert_of_notMem (show a ∉ l.toFinset by simpa)] using ih

theorem coeff_sum_powers (F : List (List ℕ)) (j : ℕ) :
    ((F.map (fun w => (X : Poly)^w.toFinset.card)).sum).coeff j =
      ((F.countP (fun w => decide (w.toFinset.card = j)) : ℕ) : ℤ) := by
  induction F with
  | nil => simp
  | cons w l ih =>
    by_cases hh : j=w.toFinset.card
    · subst j; simp [ih, Polynomial.coeff_X_pow, add_comm]
    · simp [hh, Ne.symm hh, ih, Polynomial.coeff_X_pow]

theorem coeff_pos_iff (A : Set ℕ) (k n : ℕ) :
    0 < (response A k n).coeff k ↔
      ∃ w : List ℕ, w.length=k ∧ w.sum=n ∧ (∀ x ∈ w, x∈A) ∧ w.Nodup := by
  rw [response_expansion, coeff_sum_powers]
  simp only [Int.natCast_pos, List.countP_pos_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨l,hm,hs⟩
    obtain ⟨hl,hev,hA⟩ := (mem_fiber A k n l).mp hm
    exact ⟨l,hl,hev,hA,(card_eq_len l).mp (hs.trans hl.symm)⟩
  · rintro ⟨l,hl,hev,hA,hnd⟩
    exact ⟨l,(mem_fiber A k n l).mpr ⟨hl,hev,hA⟩,(card_eq_len l).mpr hnd |>.trans hl⟩

/-- Only the thinning of ordinary fibers is queried. Different arities are
not padded with repeated zero: the top-coefficient test is made separately. -/
def FullResponse (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, ∃ k ≤ h, 0 < (response A k n).coeff k

theorem order_iff_fullResponse (A : Set ℕ) (h : ℕ) :
    HasRestrictedOrder A h ↔ FullResponse A h := by
  rw [restricted_iff_list]
  constructor
  · rintro ⟨N, hp⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨l,hnd,ha,hs,hk⟩ := hp n hn
    exact ⟨l.length,hk,(coeff_pos_iff A l.length n).mpr ⟨l,rfl,hs,ha,hnd⟩⟩
  · rintro ⟨N, hp⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k,hk,ht⟩ := hp n hn
    obtain ⟨l,hl,hs,ha,hnd⟩ := (coeff_pos_iff A k n).mp ht
    exact ⟨l,hnd,ha,hs,hl ▸ hk⟩

theorem exact_order_iff_fullResponse (A : Set ℕ) (h : ℕ)
    (_hb : HasOrder A h) (least : ∀ k < h, ¬ HasOrder A k) :
    (HasRestrictedOrder A h ∧ ∀ k < h, ¬ HasRestrictedOrder A k) ↔ FullResponse A h := by
  refine ⟨fun H => (order_iff_fullResponse A h).mp H.1, fun hs => ⟨(order_iff_fullResponse A h).mpr hs, ?_⟩⟩
  intro k hk hR
  apply least k hk
  apply ordinary_iff_list.mpr
  obtain ⟨N,ht⟩ := restricted_iff_list.mp hR
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨w,_,ha,hw,hh⟩ := ht n hn
  exact ⟨w,ha,hw,hh⟩

#print axioms exact_order_iff_fullResponse
#print axioms response_expansion
end Erdos338.Thinning
