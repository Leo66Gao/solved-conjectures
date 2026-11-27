import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Finite incidence estimates in Chen–Yang–Zhao, Theorem 2, Lemma 3.
All subsets below are finite. No density or Kneser assertion is imported. -/

open scoped BigOperators
namespace Erdos338.Popularity

/-- For one fixed target, stripping a specified label from one side
injects pairs on that side into the smaller-sumset. -/
theorem fixed_sum_fiber
    (T : Finset (ℕ × ℕ)) (F : ℕ → Finset ℕ) (E : Finset ℕ) (n a : ℕ)
    (hs : ∀ p ∈ T, p.1 + p.2 = n)
    (strip : ∀ p ∈ T, a ∈ F p.1 → a ≤ p.1 ∧ p.1 - a ∈ E) :
    (T.filter fun p => a ∈ F p.1).card ≤ E.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 - a)
  · intro p hp
    obtain ⟨hpT, hpF⟩ := Finset.mem_filter.mp hp
    exact (strip p hpT hpF).2
  · intro p hp q hq eq
    obtain ⟨hpT, hpF⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqT, hqF⟩ := Finset.mem_filter.mp hq
    have hp1 := (strip p hpT hpF).1
    have hq1 := (strip q hqT hqF).1
    have hp2 := hs p hpT
    have hq2 := hs q hqT
    change p.1 - a = q.1 - a at eq
    apply Prod.ext <;> omega

/-- If each prescribed label hits at most `e` pairs per side, a hitting
set `V` accounts for at most `2 * |V| * e` distinct pairs. -/
theorem fixed_sum_cover (T : Finset (ℕ × ℕ)) (F : ℕ → Finset ℕ)
    (V : Finset ℕ) (e : ℕ)
    (cover : ∀ p ∈ T, ∃ a ∈ V, a ∈ F p.1 ∨ a ∈ F p.2)
    (left : ∀ a ∈ V, (T.filter fun p => a ∈ F p.1).card ≤ e)
    (right : ∀ a ∈ V, (T.filter fun p => a ∈ F p.2).card ≤ e) :
    T.card ≤ 2 * V.card * e := by
  classical
  revert T
  induction V using Finset.induction_on with
  | empty =>
    intro T hc _ _
    have hz : T = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      obtain ⟨a,ha,_⟩ := hc p hp
      simp at ha)
    simp [hz]
  | @insert a V hnot ih =>
    intro T hc hl hr
    let L := T.filter fun p => a ∈ F p.1
    let R := T.filter fun p => a ∈ F p.2
    let U := T.filter fun p => a ∉ F p.1 ∧ a ∉ F p.2
    have ht : T ⊆ (L ∪ R) ∪ U := by
      intro p hp
      by_cases h₁ : a ∈ F p.1 <;> by_cases h₂ : a ∈ F p.2 <;>
        simp [L,R,U,hp,h₁,h₂]
    have hUsub : U ⊆ T := fun _ hp => (Finset.mem_filter.mp hp).1
    have hUL : ∀ b, (U.filter fun p => b ∈ F p.1) ⊆ T.filter fun p => b ∈ F p.1 :=
      fun b p hp => Finset.mem_filter.mpr ⟨hUsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have hUR : ∀ b, (U.filter fun p => b ∈ F p.2) ⊆ T.filter fun p => b ∈ F p.2 :=
      fun b p hp => Finset.mem_filter.mpr ⟨hUsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have hb : U.card ≤ 2 * V.card * e := by
      apply ih U
      · intro p hp
        obtain ⟨_,h₁,h₂⟩ := Finset.mem_filter.mp hp
        obtain ⟨b,hb,hb'⟩ := hc p (hUsub hp)
        rcases Finset.mem_insert.mp hb with rfl|hv
        · exact False.elim (hb'.elim h₁ h₂)
        · exact ⟨b,hv,hb'⟩
      · exact fun b hb => (Finset.card_le_card (hUL b)).trans (hl b (Finset.mem_insert_of_mem hb))
      · exact fun b hb => (Finset.card_le_card (hUR b)).trans (hr b (Finset.mem_insert_of_mem hb))
    calc
      T.card ≤ ((L∪R)∪U).card := Finset.card_le_card ht
      _ ≤ (L∪R).card + U.card := Finset.card_union_le _ _
      _ ≤ (L.card+R.card) + U.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (e+e)+2*V.card*e := Nat.add_le_add (Nat.add_le_add
        (hl a (Finset.mem_insert_self a V)) (hr a (Finset.mem_insert_self a V))) hb
      _ = 2 * (insert a V).card * e := by
        rw [Finset.card_insert_of_notMem hnot, Nat.mul_add, Nat.add_mul]
        omega

/-- Greedy finite matching with a uniform bound on each conflict neighborhood.
The result is a family of pairwise disjoint supports, not just an estimate
on the number of pairs. -/
theorem packing_from_conflict_budget
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (H : α → Finset β) (B q : ℕ) (T : Finset α)
    (nonempty : ∀ x ∈ T, (H x).Nonempty)
    (budget : ∀ x ∈ T, (T.filter fun y => ¬ Disjoint (H x) (H y)).card ≤ B)
    (many : B*q < T.card) :
    ∃ U : Finset α, U ⊆ T ∧ U.card = q+1 ∧
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → Disjoint (H x) (H y) := by
  classical
  induction q generalizing T with
  | zero =>
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by simpa using many)
    refine ⟨{x}, by simpa using hx, by simp, ?_⟩
    simp
  | succ q ih =>
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt many)
    let R := T.filter (fun y => ¬ Disjoint (H x) (H y))
    let S := T.filter (fun y => Disjoint (H x) (H y))
    have hs : S ⊆ T := fun _ hy => (Finset.mem_filter.mp hy).1
    have ht : T ⊆ R ∪ S := by
      intro y hy
      by_cases hd : Disjoint (H x) (H y) <;> simp [R,S,hy,hd]
    have hr : R.card ≤ B := budget x hx
    have hd := (Finset.card_le_card ht).trans (Finset.card_union_le R S)
    have more : B*q < S.card := by rw [Nat.mul_succ] at many; omega
    obtain ⟨U,hU,hu,huDisj⟩ := ih S
      (fun y hy => nonempty y (hs hy))
      (fun y hy => (Finset.card_le_card (fun z hz =>
        Finset.mem_filter.mpr ⟨hs (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)).trans
          (budget y (hs hy))) more
    have notx : x ∉ U := by
      intro hxu
      have hd' := (Finset.mem_filter.mp (hU hxu)).2
      obtain ⟨a,ha⟩ := nonempty x hx
      exact Finset.disjoint_left.mp hd' ha ha
    refine ⟨insert x U, Finset.insert_subset_iff.mpr ⟨hx,hU.trans hs⟩, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem notx,hu]
    · intro u hu' v hv hne
      rcases Finset.mem_insert.mp hu' with rfl|hUm <;>
        rcases Finset.mem_insert.mp hv with rfl|hVm
      · exact (hne rfl).elim
      · exact (Finset.mem_filter.mp (hU hVm)).2
      · exact ((Finset.mem_filter.mp (hU hUm)).2).symm
      · exact huDisj u hUm v hVm hne

/-- CYZ's constant for a fixed-target collection with bounded fibers per side.
The resulting supports are unions of the two representations. -/
theorem fixed_sum_packing_from_fibers
    (T : Finset (ℕ × ℕ)) (F : ℕ → Finset ℕ) (r e q : ℕ)
    (bounds : ∀ p ∈ T, (F p.1).card ≤ r ∧ (F p.2).card ≤ r)
    (nonempty : ∀ p ∈ T, (F p.1 ∪ F p.2).Nonempty)
    (left : ∀ a, (T.filter fun p => a ∈ F p.1).card ≤ e)
    (right : ∀ a, (T.filter fun p => a ∈ F p.2).card ≤ e)
    (many : 4*r*e*q < T.card) :
    ∃ U : Finset (ℕ × ℕ), U ⊆ T ∧ U.card = q+1 ∧
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → Disjoint (F x.1 ∪ F x.2) (F y.1 ∪ F y.2) := by
  classical
  apply packing_from_conflict_budget
    (fun p : ℕ × ℕ => F p.1 ∪ F p.2) (4*r*e) q T nonempty ?_ many
  intro x hx
  let V := F x.1 ∪ F x.2
  let R := T.filter (fun y => ¬Disjoint V (F y.1 ∪ F y.2))
  have rs : R ⊆ T := fun _ hy => (Finset.mem_filter.mp hy).1
  have cover : ∀ p ∈ R, ∃ a ∈ V, a ∈ F p.1 ∨ a ∈ F p.2 := by
    intro p hp
    have hn := (Finset.mem_filter.mp hp).2
    rw [Finset.disjoint_left] at hn
    push_neg at hn
    obtain ⟨a,ha,hp⟩ := hn
    exact ⟨a,ha,Finset.mem_union.mp hp⟩
  have le : V.card ≤ r+r := (Finset.card_union_le _ _).trans
    (Nat.add_le_add (bounds x hx).1 (bounds x hx).2)
  calc
    R.card ≤ 2 * V.card * e := fixed_sum_cover R F V e cover
      (fun a _ => (Finset.card_le_card (Finset.filter_subset_filter _ rs)).trans (left a))
      (fun a _ => (Finset.card_le_card (Finset.filter_subset_filter _ rs)).trans (right a))
    _ ≤ 2*(r+r)*e := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ le)
    _ = 4*r*e := by rw [← Nat.two_mul r, ← Nat.mul_assoc]

/-- A finite subset-sumset up to target `N`, at bounded rank. -/
noncomputable def restrictedPrefix (A : Set ℕ) (r N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N+1)).filter fun x =>
    ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ (∑ a ∈ S, a) = x

private theorem mem_restrictedPrefix {A : Set ℕ} {r N x : ℕ} :
    x ∈ restrictedPrefix A r N ↔ x ≤ N ∧
      ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ (∑ a ∈ S, a) = x := by
  classical
  simp [restrictedPrefix, Nat.lt_succ_iff]

/-- Deleting a specified summand gives a point in the smaller prefix sumset. -/
theorem strip_witness
    {A : Set ℕ} {r N x a : ℕ} {s : Finset ℕ}
    (hx : x ≤ N) (hs : ∀ z ∈ s, z ∈ A) (hr : s.card ≤ r)
    (hm : (∑ z ∈ s, z) = x) (ha : a ∈ s) :
    a ≤ x ∧ x-a ∈ restrictedPrefix A (r-1) N := by
  have ea := s.add_sum_erase id ha
  change a + (∑ z ∈ s.erase a, z) = (∑ z ∈ s, z) at ea
  rw [hm] at ea
  have cd := Finset.card_erase_add_one ha
  refine ⟨by omega, mem_restrictedPrefix.mpr ⟨by omega,s.erase a,?_,by omega,by omega⟩⟩
  exact fun z hz => hs z (Finset.mem_of_mem_erase hz)

/-- Unconditioned label incidence for the global collision estimate. -/
theorem global_incidence
    (X : Finset ℕ) (F : ℕ → Finset ℕ) (E : Finset ℕ) (a : ℕ)
    (strip : ∀ x ∈ X, a ∈ F x → a ≤ x ∧ x-a ∈ E) :
    (X.filter fun x => a ∈ F x).card ≤ E.card := by
  apply Finset.card_le_card_of_injOn (fun x : ℕ => x-a)
  · intro x hx
    obtain ⟨hX,hF⟩ := Finset.mem_filter.mp hx
    exact (strip x hX hF).2
  · intro x hx y hy he
    obtain ⟨hX,hF⟩ := Finset.mem_filter.mp hx
    obtain ⟨hY,hG⟩ := Finset.mem_filter.mp hy
    have hx' := (strip x hX hF).1
    have hy' := (strip y hY hG).1
    change x-a=y-a at he
    omega

/-- Global good-pair count: any pair of supports that intersect consumes
at least one of the at most r labels in the first support and at most e
choices on the right. -/
theorem global_noncollision_count
    (X : Finset ℕ) (F : ℕ → Finset ℕ) (r e : ℕ)
    (rank : ∀ x ∈ X, (F x).card ≤ r)
    (few : ∀ a, (X.filter fun x => a ∈ F x).card ≤ e) :
    X.card * X.card ≤
      ((X ×ˢ X).filter fun p => Disjoint (F p.1) (F p.2)).card + X.card*r*e := by
  classical
  let B (x : ℕ) := X.filter fun y => ¬Disjoint (F x) (F y)
  let P := (X ×ˢ X).filter fun p => Disjoint (F p.1) (F p.2)
  have allBad (x : ℕ) : (B x).card ≤ (F x).card*e := by
    refine (Finset.card_le_card ?_).trans
      (Finset.card_biUnion_le_card_mul (F x) (fun a => X.filter (fun y => a ∈ F y)) e
        (fun a _ => few a))
    intro y hy
    obtain ⟨hyX,h⟩ := Finset.mem_filter.mp hy
    rw [Finset.disjoint_left] at h
    push_neg at h
    obtain ⟨a,ha,ha'⟩ := h
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hyX,ha'⟩⟩
  let row (x : ℕ) := (B x).image fun y => (x,y)
  have rb : ∀ x ∈ X, (row x).card ≤ r*e := by
    intro x hx
    exact Finset.card_image_le.trans ((allBad x).trans (Nat.mul_le_mul_right e (rank x hx)))
  have bound := Finset.card_biUnion_le_card_mul X row (r*e) rb
  have incl : X ×ˢ X ⊆ P ∪ X.biUnion row := by
    intro p hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    by_cases hab : Disjoint (F p.1) (F p.2)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hab⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p.1, hx, ?_⟩)
      exact Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨hy,hab⟩, rfl⟩
  calc
    X.card*X.card = (X ×ˢ X).card := (Finset.card_product X X).symm
    _ ≤ (P ∪ X.biUnion row).card := Finset.card_le_card incl
    _ ≤ P.card + (X.biUnion row).card := Finset.card_union_le ..
    _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.add_le_add_left bound _

#print axioms strip_witness
#print axioms global_noncollision_count
#print axioms packing_from_conflict_budget
#print axioms fixed_sum_packing_from_fibers
#print axioms fixed_sum_fiber
#print axioms fixed_sum_cover
end Erdos338.Popularity
