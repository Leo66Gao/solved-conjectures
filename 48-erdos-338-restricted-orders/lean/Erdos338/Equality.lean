import Erdos338.Pair
import Erdos338.Fringe
import Erdos338.Blockers

namespace Erdos338

/-- A good label has sufficiently many distinct, oriented symmetric pairs. -/
def Good (A : ℕ → Prop) (h a : ℕ) : Prop :=
  ∃ P : Finset (ℕ × ℕ), h - 2 < P.card ∧
    ∀ p ∈ P, A p.1 ∧ A p.2 ∧ p.1 < p.2 ∧ p.1+p.2 = a+a

noncomputable def fringe (A : ℕ → Prop) (h a : ℕ) : Bool := by
  classical
  exact decide (¬ Good A h a)

theorem fresh_of_good {A : ℕ → Prop} {h a : ℕ} (hg : Good A h a) :
    Fringe.Fresh A h a := by
  obtain ⟨P, hP, hv⟩ := hg
  refine Fringe.fresh_of_disjoint P hP (fun p hp => ?_) ?_
  · obtain ⟨b,c,bc,he⟩ := hv p hp
    exact ⟨b,c,ne_of_lt bc,he⟩
  · rintro ⟨p₁,p₂⟩ hp ⟨q₁,q₂⟩ hq hn
    obtain ⟨_,_,lp,ep⟩ := hv (p₁,p₂) hp
    obtain ⟨_,_,lq,eq⟩ := hv (q₁,q₂) hq
    dsimp at lp ep lq eq ⊢
    have ord : p₁ < p₂ ∧ q₁ < q₂ := ⟨lp,lq⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro e
      have e₂ : p₂ = q₂ := by omega
      exact hn (by simp [e,e₂])
    · omega
    · omega
    · intro e
      have e₁ : p₁ = q₁ := by omega
      exact hn (by simp [e,e₁])

theorem canonical_repair (A : ℕ → Prop) (h : ℕ) : Pair.Repair A (fringe A h) h := by
  classical
  intro xs hl hA hclean
  have hmem : ∀ x ∈ (xs : Multiset ℕ), A x := by simpa [Pair.All] using hA
  have hrep : ∀ x, 1 < (xs : Multiset ℕ).count x → Fringe.Fresh A h x := by
    intro x hx
    apply fresh_of_good
    by_contra hn
    have hf : fringe A h x = true := by simp [fringe, hn]
    have hc := (List.nodup_iff_count_le_one.mp hclean) x
    rw [List.count_filter (by exact hf)] at hc
    rw [Multiset.coe_count] at hx
    omega
  obtain ⟨v,hv,hvA,hvN,hvS⟩ := Fringe.repair (↑xs : Multiset ℕ) hl hmem hrep
  obtain ⟨ys,rfl⟩ := Quot.exists_rep v
  have heq : ys.length = xs.length := by simpa using hv
  exact ⟨ys, heq ▸ hl, by simpa [Pair.All] using hvA, by simpa using hvN, by simpa using hvS⟩

/-- Unconditional pointwise version of the ZIP's exact rank-two criterion,
with automatically selected canonical fringe. -/
theorem canonical_pair_criterion (A : ℕ → Prop) {h n : ℕ} (hh : 2 ≤ h) :
    Pair.Restricted A h n ↔ ∃ u, Pair.Cert A (fringe A h) h (h%2) (h/2) n u := by
  apply Pair.pair_criterion hh (by omega) (canonical_repair A h)

/-- The canonical virtual-support criterion is also equivalent to actual
restricted coverage, with no arithmetic repair hypothesis left over. -/
theorem canonical_blocker_criterion (A : ℕ → Prop) (l r : Blockers.Shape) (n : ℕ) :
    let h := Blockers.leaves l + Blockers.leaves r
    let B : ℕ → Prop := fun x => fringe A h x = true
    Pair.Restricted A h n ↔
      ∃ i j X Y, i+j=n ∧ Blockers.summary A B l (Blockers.leaves r) i X ∧
        Blockers.summary A B r (Blockers.leaves l) j Y ∧ Blockers.Disj X Y := by
  dsimp
  let h := Blockers.leaves l + Blockers.leaves r
  let B : ℕ → Prop := fun x => fringe A h x = true
  change Pair.Restricted A h n ↔ _
  rw [← Blockers.split_exact A B l r n]
  constructor
  · rintro ⟨xs,hl,hA,hN,hS⟩
    exact ⟨xs,hl,hS,hA,Blockers.fringeDistinct_of_nodup B hN⟩
  · rintro ⟨xs,hl,hS,hA,hf⟩
    have hc : Pair.Clean (fringe A h) xs := by
      apply List.nodup_iff_count_le_one.mpr
      intro x
      by_cases hb : fringe A h x = true
      · rw [List.count_filter hb]
        exact (Blockers.fringeDistinct_iff_counts B xs).mp hf x hb
      · have eqz : (xs.filter (fringe A h)).count x = 0 := by
          apply List.count_eq_zero_of_not_mem
          intro hm
          exact hb (List.mem_filter.mp hm).2
        omega
    obtain ⟨ys,yl,ya,yN,yS⟩ := canonical_repair A h xs hl hA hc
    exact ⟨ys,yl,ya,yN,yS.trans hS⟩

def Ordinary (A : ℕ → Prop) (h n : ℕ) : Prop :=
  ∃ xs : List ℕ, xs.length ≤ h ∧ Pair.All A xs ∧ xs.sum = n

def Cofinite (p : ℕ → Prop) : Prop := ∃ N, ∀ n ≥ N, p n

/-- At ordinary order h, the restricted order agrees iff the canonical
criterion accepts all sufficiently large targets. The least-rank part is
automatic from containment of restricted in ordinary representations. -/
theorem equal_order_iff_canonical (A : ℕ → Prop) {h : ℕ} (hh : 2 ≤ h)
    (least : ∀ k < h, ¬ Cofinite (Ordinary A k)) :
    (Cofinite (Pair.Restricted A h) ∧ ∀ k < h, ¬ Cofinite (Pair.Restricted A k)) ↔
      Cofinite (fun n => ∃ u, Pair.Cert A (fringe A h) h (h%2) (h/2) n u) := by
  constructor
  · rintro ⟨⟨N,hN⟩,_⟩
    exact ⟨N,fun n hn => (canonical_pair_criterion A hh).1 (hN n hn)⟩
  · rintro ⟨N,hN⟩
    refine ⟨⟨N,fun n hn => (canonical_pair_criterion A hh).2 (hN n hn)⟩,?_⟩
    rintro k hk ⟨M,hM⟩
    apply least k hk
    refine ⟨M,fun n hn => ?_⟩
    obtain ⟨ys,hl,hA,_,hs⟩ := hM n hn
    exact ⟨ys,hl,hA,hs⟩

/-- The expanded nonrecursive sumset identity of Theorem 7.2. -/
theorem canonical_sumset_identity (A : ℕ → Prop) {h n : ℕ} (hh : 2 ≤ h) :
    Pair.Restricted A h n ↔ Pair.SumsetRHS A (fringe A h) h (h/2) (h%2) n :=
  Pair.rank_two_sumset_identity hh (by omega) (canonical_repair A h)

/-- The full equality criterion on the doubled fringe footprint. -/
theorem equal_order_iff_footprint (A : ℕ → Prop) {h : ℕ} (hh : 2 ≤ h)
    (base : Cofinite (Ordinary A h))
    (least : ∀ k < h, ¬ Cofinite (Ordinary A k)) :
    (Cofinite (Pair.Restricted A h) ∧ ∀ k < h, ¬ Cofinite (Pair.Restricted A k)) ↔
      ∃ N, ∀ n ≥ N, Pair.Footprint A (fringe A h) h n →
        Pair.SumsetRHS A (fringe A h) h (h/2) (h%2) n := by
  have ht := Pair.tail_footprint_iff (m := h/2) (e := h%2) hh (by omega)
    (canonical_repair A h) base
  constructor
  · exact fun ⟨hr,_⟩ => ht.mp hr
  · intro hf
    refine ⟨ht.mpr hf,?_⟩
    rintro k hk ⟨M,hM⟩
    apply least k hk
    refine ⟨M,fun n hn => ?_⟩
    obtain ⟨ys,hl,hA,_,hs⟩ := hM n hn
    exact ⟨ys,hl,hA,hs⟩

/-- The manuscript criterion written solely with canonically oriented
reflected alternatives, for the original convention of positive summands. -/
theorem canonical_reflected_identity (A : ℕ → Prop) {h n : ℕ} (hh : 2 ≤ h)
    (positive : ∀ x, A x → 0 < x) :
    Pair.Restricted A h n ↔ Pair.ReflectedRHS A (fringe A h) h (h/2) (h%2) n :=
  Pair.rank_two_reflected_identity hh positive (canonical_repair A h)

/-- Erdős–Graham item (iii): at exact ordinary order, eventual acceptance
on the fringe footprint is necessary and sufficient for equality. -/
theorem equal_order_iff_reflected_footprint (A : ℕ → Prop) {h : ℕ} (hh : 2 ≤ h)
    (positive : ∀ x, A x → 0 < x) (base : Cofinite (Ordinary A h))
    (least : ∀ k < h, ¬ Cofinite (Ordinary A k)) :
    (Cofinite (Pair.Restricted A h) ∧ ∀ k < h, ¬ Cofinite (Pair.Restricted A k)) ↔
      ∃ N, ∀ n ≥ N, Pair.Footprint A (fringe A h) h n →
        Pair.ReflectedRHS A (fringe A h) h (h/2) (h%2) n := by
  have ht := Pair.tail_reflected_footprint_iff hh positive (canonical_repair A h) base
  constructor
  · exact fun ⟨hr,_⟩ => ht.mp hr
  · intro hf
    refine ⟨ht.mpr hf,?_⟩
    rintro k hk ⟨M,hM⟩
    apply least k hk
    refine ⟨M,fun n hn => ?_⟩
    obtain ⟨ys,hl,hA,_,hs⟩ := hM n hn
    exact ⟨ys,hl,hA,hs⟩

/-- The canonical midpoint data supply the local deletion theorem as well. -/
theorem canonical_fresh (A : ℕ → Prop) (h : ℕ) : Pair.GoodFresh A (fringe A h) h := by
  classical
  intro a _ hf E hE
  have hg : Good A h a := by simpa [fringe] using hf
  obtain ⟨b,c,hb,hc,hbc,hbE,hcE,hw⟩ :=
    fresh_of_good hg E.toFinset (E.toFinset_card_le.trans hE)
  exact ⟨b,c,hb,hc,hbc,by simpa using hbE,by simpa using hcE,hw⟩

theorem canonical_immune_iff_deletions (A : ℕ → Prop) {h s : ℕ} (hh : 2 ≤ h)
    (positive : ∀ x, A x → 0 < x) :
    Pair.Immune A (fringe A h) h s ↔ ∀ E : List ℕ,
      Pair.All (fun x => fringe A h x = true) E → E.length ≤ h-2 →
      Pair.Restricted (Pair.After A E) 2 s :=
  Pair.immune_exact hh positive (canonical_fresh A h)

end Erdos338
