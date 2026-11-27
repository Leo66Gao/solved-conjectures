import StructuralTrace
import ResidueCore

namespace Erdos338.SparseTrace
open CatalogueAdapter Filter

private theorem nodup_sum (xs : List ℕ) (nd : xs.Nodup) :
    ∑ x ∈ xs.toFinset, x = xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha,hnd⟩ := List.nodup_cons.mp nd
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using ha), List.sum_cons, ih hnd]

private theorem restrictedList_to_hit {A : Set ℕ} {h n : ℕ}
    (H : Pair.Restricted A h n) : n ∈ hit A h := by
  obtain ⟨xs,lh,mem,nd,sm⟩ := H
  refine ⟨xs.toFinset,fun x hx => mem x (List.mem_toFinset.mp hx),?_,
    (nodup_sum xs nd).trans sm⟩
  rwa [List.toFinset_card_of_nodup nd]

/-- Although no pair information is needed, the old doubled-fringe
localization still limits the global probes that must be checked. -/
theorem equal_orders_iff_anchored_fringe_trace {A : Set ℕ} {h : ℕ}
    (ord : basisOrder A = (h : ℕ∞)) :
    restrictedOrder A = basisOrder A ↔
      ∀ T : Set ℕ, Unbounded T → (∀ n ∈ T, Pair.Footprint A (fringe A h) h n) →
        ∀ g : ℕ → ℕ, AnchoredTraceAt A h T g := by
  constructor
  · intro eq T hT _ g
    exact (equal_orders_iff_anchored_trace ord).mp eq T hT g
  · intro H
    have H' := (Erdos338.Structural.ResidueCore.least_budget_iff _ _).mp ord
    obtain ⟨M,hM⟩ := ordinary_iff_list.mp H'.1
    have R : HasRestrictedOrder A h := by
      rw [HasRestrictedOrder, eventually_atTop]
      by_contra! miss
      let T : Set ℕ := {n | M ≤ n ∧ n ∉ hit A h}
      have hT : Unbounded T := by
        intro N
        obtain ⟨n,hn,nb⟩ := miss (max M (N+1))
        have hN : N < n := by omega
        refine ⟨n,hN,by omega,?_⟩
        change ¬ ∃ S : Finset ℕ, _
        push Not
        exact nb
      have onFoot : ∀ n ∈ T, Pair.Footprint A (fringe A h) h n := by
        rintro n ⟨hn,hnh⟩
        obtain ⟨xs,hm,sm,hl⟩ := hM n hn
        exact Pair.defect_in_footprint (canonical_repair A h) ⟨xs,hl,hm,sm⟩
          (fun hr => hnh (restrictedList_to_hit hr))
      obtain ⟨n,_,hn,hitn⟩ := (unbounded_hits_iff_anchored_trace id).mpr (H T hT onFoot id) 0
      exact hn.2 hitn
    exact (equal_orders_iff_sparse_trace ord).mpr ((restricted_iff_sparse_trace A h).mp R)

end Erdos338.SparseTrace
