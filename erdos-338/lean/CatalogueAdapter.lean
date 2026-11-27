import Erdos338.Growth
import Erdos338.Equality
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Adapter to Formal Conjectures #338

The two order predicates below use the catalogue's exact propositions,
with a separate namespace so they can be tested independently of the
catalogue's placeholder solution. The unconditional lemma proves the
necessity direction of Chen–Yang–Zhao, arXiv:2611.33191, Theorem 2.
The packaged equivalence explicitly requires its remaining sufficiency
argument; this file does not assert or assume a new axiom.
-/

open Filter
open scoped BigOperators

namespace Erdos338.CatalogueAdapter

def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

/-- Answer of Chen–Yang–Zhao. Writing residues as integers `r < q`
is equivalent to quantifying over the cyclic group of order `q`. -/
def answer (A : Set ℕ) : Prop :=
  ∀ q r : ℕ, r < q → ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧
    (∑ x ∈ S, x) % q = r

theorem ordinary_iff_list {A : Set ℕ} {h : ℕ} :
    HasOrder A h ↔ Growth.Mixed.OrdinaryAtMost A h := by
  unfold HasOrder Growth.Mixed.OrdinaryAtMost
  rw [Filter.eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    obtain ⟨s, hs, hc, hsum⟩ := hN m hm
    obtain ⟨l, rfl⟩ := Quotient.exists_rep s
    exact ⟨l, hs, by simpa using hsum, by simpa using hc⟩
  · rintro ⟨N,hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    obtain ⟨l, hl, hsum, hc⟩ := hN m hm
    exact ⟨(l : Multiset ℕ), hl, by simpa using hc, by simpa using hsum⟩

private theorem finset_toList_sum (s : Finset ℕ) :
    s.toList.sum = ∑ x ∈ s, x := by
  exact s.sum_toList

private theorem nodup_list_toFinset_sum (l : List ℕ) (hl : l.Nodup) :
    ∑ x ∈ l.toFinset, x = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, htl⟩ := List.nodup_cons.mp hl
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using ha), List.sum_cons, ih htl]

theorem restricted_iff_list {A : Set ℕ} {t : ℕ} :
    HasRestrictedOrder A t ↔ Growth.RestrictedAtMost A t := by
  unfold HasRestrictedOrder Growth.RestrictedAtMost
  rw [Filter.eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    obtain ⟨s, hs, hc, hsum⟩ := hN m hm
    exact ⟨s.toList, s.nodup_toList, fun x hx => hs x (by simpa using hx),
      (finset_toList_sum s).trans hsum, by simpa using hc⟩
  · rintro ⟨N,hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    obtain ⟨l, nd, hl, hsum, hc⟩ := hN m hm
    exact ⟨l.toFinset, fun x hx => hl x (by simpa using hx),
      by rwa [List.toFinset_card_of_nodup nd], (nodup_list_toFinset_sum l nd).trans hsum⟩

theorem answer_iff_list {A : Set ℕ} :
    answer A ↔ ∀ q, 0 < q → Growth.CompleteMod A q := by
  constructor
  · intro h q _ r hr
    obtain ⟨s, hs, he⟩ := h q r hr
    exact ⟨s.toList, s.nodup_toList, fun x hx => hs x (by simpa using hx),
      by rwa [finset_toList_sum]⟩
  · intro h q r hr
    obtain ⟨l, nd, hl, he⟩ := h q (Nat.zero_lt_of_lt hr) r hr
    exact ⟨l.toFinset, fun x hx => hl x (by simpa using hx),
      by rwa [nodup_list_toFinset_sum l nd]⟩

theorem necessity {A : Set ℕ} (ht : ∃ t, HasRestrictedOrder A t) : answer A := by
  obtain ⟨t, ht⟩ := ht
  exact answer_iff_list.mpr fun _ hq =>
    Growth.completeMod_of_restricted hq (restricted_iff_list.mp ht)

/-- This tests the exact final proposition and the representation bridge.
It is intentionally conditional on the unformalized analytic sufficiency. -/
theorem statement_from_list_sufficiency
    (sufficient : ∀ A : Set ℕ, (∃ h, Growth.Mixed.OrdinaryAtMost A h) →
      (∀ q, 0 < q → Growth.CompleteMod A q) → ∃ t, Growth.RestrictedAtMost A t) :
    ∀ A : Set ℕ, (∃ h, HasOrder A h) → ((∃ t, HasRestrictedOrder A t) ↔ answer A) := by
  intro A h
  refine ⟨necessity, fun ha => ?_⟩
  obtain ⟨k,hk⟩ := h
  obtain ⟨t,ht⟩ := sufficient A ⟨k,ordinary_iff_list.mp hk⟩ (answer_iff_list.mp ha)
  exact ⟨t,restricted_iff_list.mpr ht⟩

noncomputable def basisOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (h : ℕ) (_ : HasOrder A h), (h : ℕ∞)

noncomputable def restrictedOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)

private theorem inf_eq_nat_iff (p : ℕ → Prop) (h : ℕ) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = (h : ℕ∞) ↔
      p h ∧ ∀ k < h, ¬ p k := by
  classical
  have ofmin : ∀ h : ℕ, p h → (∀ k < h, ¬p k) →
      (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = (h : ℕ∞) := by
    intro h hh hl
    apply le_antisymm
    · exact iInf_le_of_le h (iInf_le_of_le hh le_rfl)
    · refine le_iInf fun k => le_iInf fun hk => ENat.natCast_le_natCast.mpr ?_
      exact Nat.le_of_not_gt fun hkh => hl k hkh hk
  constructor
  · intro he
    by_cases hp : ∃ n, p n
    · have hpmin := Nat.find_spec hp
      have hmin : ∀ k < Nat.find hp, ¬ p k :=
        fun k hk hpk => Nat.not_le_of_gt hk (Nat.find_min' hp hpk)
      have e : Nat.find hp = h := by simpa using (ofmin _ hpmin hmin).symm.trans he
      exact e ▸ ⟨hpmin, hmin⟩
    · have top : (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = ⊤ := by
        apply top_unique
        exact le_iInf fun k => le_iInf fun hk => (hp ⟨k,hk⟩).elim
      exact (ENat.natCast_ne_top h (he.symm.trans top)).elim
  · rintro ⟨hh,hl⟩
    exact ofmin h hh hl

private theorem ordinary_iff_cofinite {A : Set ℕ} {h : ℕ} :
    HasOrder A h ↔ Cofinite (Ordinary A h) := by
  rw [ordinary_iff_list]
  constructor <;> rintro ⟨N,hN⟩ <;> refine ⟨N, fun n hn => ?_⟩
  · obtain ⟨xs, ha, sm, len⟩ := hN n hn
    exact ⟨xs,len,ha,sm⟩
  · obtain ⟨xs, len, ha, sm⟩ := hN n hn
    exact ⟨xs,ha,sm,len⟩

private theorem restricted_iff_cofinite {A : Set ℕ} {h : ℕ} :
    HasRestrictedOrder A h ↔ Cofinite (Pair.Restricted A h) := by
  rw [restricted_iff_list]
  constructor <;> rintro ⟨N,hN⟩ <;> refine ⟨N, fun n hn => ?_⟩
  · obtain ⟨xs,nd,ha,sm,len⟩ := hN n hn
    exact ⟨xs,len,ha,nd,sm⟩
  · obtain ⟨xs,len,ha,nd,sm⟩ := hN n hn
    exact ⟨xs,nd,ha,sm,len⟩

/-- The existing quantitative-criterion proof also transfers to the
catalogue's least orders, rather than requiring an externally supplied rank. -/
noncomputable def equalityAnswer (A : Set ℕ) : Prop :=
  ∀ h : ℕ, basisOrder A = (h : ℕ∞) → 2 ≤ h →
    ∃ N, ∀ n ≥ N, Pair.Footprint A (fringe A h) h n →
      Pair.SumsetRHS A (fringe A h) h (h/2) (h%2) n

theorem equality_variant (A : Set ℕ) (base : ∃ h, HasOrder A h) :
    restrictedOrder A = basisOrder A ↔ equalityAnswer A := by
  classical
  let h := Nat.find base
  have ord : HasOrder A h := Nat.find_spec base
  have least : ∀ k < h, ¬HasOrder A k :=
    fun k hk hpk => Nat.not_le_of_gt hk (Nat.find_min' base hpk)
  have eh : basisOrder A = (h : ℕ∞) := (inf_eq_nat_iff _ _).mpr ⟨ord,least⟩
  have rleast : ∀ k < h, ¬HasRestrictedOrder A k := by
    intro k hk hr
    apply least k hk
    apply ordinary_iff_list.mpr
    obtain ⟨N,hN⟩ := restricted_iff_list.mp hr
    exact ⟨N, fun n hn => by
      obtain ⟨xs,_,ha,sm,len⟩ := hN n hn
      exact ⟨xs,ha,sm,len⟩⟩
  have eqAt : restrictedOrder A = basisOrder A ↔ HasRestrictedOrder A h := by
    rw [eh, restrictedOrder, inf_eq_nat_iff]
    exact and_iff_left rleast
  by_cases hh : 2 ≤ h
  · have hc := equal_order_iff_footprint A hh (ordinary_iff_cofinite.mp ord)
      (fun k hk hk' => least k hk (ordinary_iff_cofinite.mpr hk'))
    have bridge : HasRestrictedOrder A h ↔ ∃ N, ∀ n ≥ N,
         Pair.Footprint A (fringe A h) h n →
           Pair.SumsetRHS A (fringe A h) h (h/2) (h%2) n :=
      ⟨fun hr => hc.mp ⟨restricted_iff_cofinite.mp hr,
          fun k hk hr' => rleast k hk (restricted_iff_cofinite.mpr hr')⟩,
       fun hp => restricted_iff_cofinite.mpr (hc.mpr hp).1⟩
    exact eqAt.trans (bridge.trans ⟨fun hp k ek _ => by
      have e : h = k := by simpa using eh.symm.trans ek
      subst k
      exact hp, fun hp => hp h eh hh⟩)
  · have short : HasRestrictedOrder A h := by
      apply restricted_iff_list.mpr
      obtain ⟨N,hN⟩ := ordinary_iff_list.mp ord
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨xs,ha,sm,len⟩ := hN n hn
      refine ⟨xs, ?_, ha, sm, len⟩
      cases xs with
      | nil => simp
      | cons a tl =>
        cases tl with
        | nil => simp
        | cons b tl => simp at len; omega
    refine ⟨fun _ k ek hk => ?_, fun _ => eqAt.mpr short⟩
    have e : h = k := by simpa using eh.symm.trans ek
    exact (hh (e.symm ▸ hk)).elim

/-- At a finite exact order, the corresponding at-most representation property holds. -/
theorem hasOrder_of_basisOrder_eq {A : Set ℕ} {h : ℕ}
    (eq : basisOrder A = (h : ℕ∞)) : HasOrder A h :=
  ((inf_eq_nat_iff _ _).mp eq).1

/-- Existence of a finite restricted order in the catalogue's least-order notation. -/
theorem restrictedOrder_ne_top_iff (A : Set ℕ) :
    restrictedOrder A ≠ ⊤ ↔ ∃ t, HasRestrictedOrder A t := by
  constructor
  · intro h
    by_contra no
    apply h
    change (⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)) = ⊤
    exact top_unique (le_iInf fun t => le_iInf fun H => (no ⟨t,H⟩).elim)
  · rintro ⟨t,ht⟩ he
    have b : restrictedOrder A ≤ (t : ℕ∞) :=
      iInf_le_of_le t (iInf_le_of_le ht le_rfl)
    exact ENat.natCast_ne_top t (top_unique (he ▸ b))

/-- The fixed-exact-order finite-removal variant follows from the variant
that permits a different ordinary order for each finite deletion. -/
theorem stableDeletion_of_variable
    (general : ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) →
       ∃ t, HasRestrictedOrder A t)
    (A : Set ℕ) (h : ℕ)
    (stable : ∀ F : Set ℕ, F.Finite → basisOrder (A \ F) = (h : ℕ∞)) :
    restrictedOrder A ≠ ⊤ :=
  (restrictedOrder_ne_top_iff A).mpr <|
    general A (fun F f => ⟨h, hasOrder_of_basisOrder_eq (stable F f)⟩)

#print axioms stableDeletion_of_variable
#print axioms equality_variant
#print axioms necessity
#print axioms statement_from_list_sufficiency
end Erdos338.CatalogueAdapter
