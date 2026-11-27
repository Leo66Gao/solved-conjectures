import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-! The duplicate-repair step from §5.1 of the final-audit manuscript.
The proof decreases the deficit in the number of occupied labels. -/
namespace Erdos338.Fringe

/-- A midpoint admits a fresh replacement outside every forbidden set of the required size. -/
def Fresh (A : ℕ → Prop) (h a : ℕ) : Prop :=
  ∀ F : Finset ℕ, F.card ≤ h - 2 →
    ∃ b c, A b ∧ A c ∧ b ≠ c ∧ b ∉ F ∧ c ∉ F ∧ b+c = a+a

/-- Pairwise disjoint symmetric pairs certify the midpoint property. -/
theorem fresh_of_disjoint {A : ℕ → Prop} {h a : ℕ}
    (P : Finset (ℕ × ℕ)) (many : h - 2 < P.card)
    (valid : ∀ p ∈ P, A p.1 ∧ A p.2 ∧ p.1 ≠ p.2 ∧ p.1+p.2 = a+a)
    (disjoint : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    Fresh A h a := by
  classical
  intro F hF
  by_contra hn
  have hit : ∀ p ∈ P, p.1 ∈ F ∨ p.2 ∈ F := by
    intro p hp
    by_contra hh
    push_neg at hh
    obtain ⟨h1,h2,hne,hs⟩ := valid p hp
    exact hn ⟨p.1,p.2,h1,h2,hne,hh.1,hh.2,hs⟩
  let pick : ℕ × ℕ → ℕ := fun p => if p.1 ∈ F then p.1 else p.2
  have sub : P.image pick ⊆ F := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rcases hit p hp with ha | hb
    · simp [pick, ha]
    · by_cases ha : p.1 ∈ F <;> simp [pick,ha,hb]
  have inject : Set.InjOn pick ↑P := by
    intro p hp q hq he
    by_contra hne
    obtain ⟨d₁,d₂,d₃,d₄⟩ := disjoint p hp q hq hne
    by_cases h1 : p.1 ∈ F <;> by_cases h2 : q.1 ∈ F <;>
      simp_all [pick]
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inject] at hc
  omega

theorem repair {A : ℕ → Prop} {h : ℕ} (s : Multiset ℕ)
    (hs : s.card ≤ h) (memA : ∀ x ∈ s, A x)
    (repeatFresh : ∀ x, 1 < s.count x → Fresh A h x) :
    ∃ t : Multiset ℕ, t.card = s.card ∧ (∀ x ∈ t, A x) ∧ t.Nodup ∧ t.sum = s.sum := by
  classical
  generalize hm : h - s.toFinset.card = d
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
    by_cases hd : s.Nodup
    · exact ⟨s,rfl,memA,hd,rfl⟩
    · rw [Multiset.nodup_iff_count_le_one] at hd
      push_neg at hd
      obtain ⟨a,ha⟩ := hd
      let u := (s.erase a).erase a
      have ha₁ : a ∈ s := Multiset.count_pos.mp (by omega)
      have ha₂ : a ∈ s.erase a := by
        apply Multiset.count_pos.mp
        rw [Multiset.count_erase_self]
        omega
      have eqs : a ::ₘ a ::ₘ u = s := by
        dsimp [u]
        rw [Multiset.cons_erase ha₂, Multiset.cons_erase ha₁]
      have hc : u.card + 2 = s.card := by
        simpa using congrArg Multiset.card eqs
      obtain ⟨b,c,hb,hcA,hbc,hbU,hcU,hweight⟩ :=
        repeatFresh a ha u.toFinset (by
          have := u.toFinset_card_le
          omega)
      let v := b ::ₘ c ::ₘ u
      have cardv : v.card = s.card := by simp [v]; omega
      have sumv : v.sum = s.sum := by
        rw [← eqs]
        simp [v, Multiset.sum_cons]
        omega
      have sub : ∀ x ∈ u, x ∈ s := by
        intro x hx
        rw [← eqs]
        simp [hx]
      have memv : ∀ x ∈ v, A x := by
        intro x hx
        simp only [v, Multiset.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact hb
        · exact hcA
        · exact memA x (sub x hx)
      have repv : ∀ x, 1 < v.count x → Fresh A h x := by
        intro x hx
        have hb0 : b ∉ u := by simpa using hbU
        have hc0 : c ∉ u := by simpa using hcU
        by_cases xb : x = b
        · subst x
          simp [v, Multiset.count_cons_of_ne hbc, Multiset.count_eq_zero_of_not_mem hb0] at hx
        by_cases xc : x = c
        · subst x
          simp [v, Multiset.count_cons_of_ne hbc.symm, Multiset.count_eq_zero_of_not_mem hc0] at hx
        change 1 < (b ::ₘ c ::ₘ u).count x at hx
        rw [Multiset.count_cons_of_ne xb, Multiset.count_cons_of_ne xc] at hx
        apply repeatFresh x
        rw [← eqs]
        have i := Multiset.count_le_count_cons x a u
        have j := Multiset.count_le_count_cons x a (a ::ₘ u)
        omega
      have old : s.toFinset.card ≤ u.toFinset.card + 1 := by
        rw [← eqs, Multiset.toFinset_cons, Multiset.toFinset_cons, Finset.insert_idem]
        exact Finset.card_insert_le _ _
      have new : v.toFinset.card = u.toFinset.card + 2 := by
        change (b ::ₘ c ::ₘ u).toFinset.card = _
        rw [Multiset.toFinset_cons, Multiset.toFinset_cons]
        have hh : b ∉ insert c u.toFinset := by simp [hbc, hbU]
        rw [Finset.card_insert_of_not_mem hh, Finset.card_insert_of_not_mem hcU]
      have vc := v.toFinset_card_le
      have smaller : h - v.toFinset.card < d := by omega
      obtain ⟨t,ht,hmA,hn,hsum⟩ := ih _ smaller v (cardv ▸ hs) memv repv rfl
      exact ⟨t, ht.trans cardv, hmA, hn, hsum.trans sumv⟩

end Erdos338.Fringe
