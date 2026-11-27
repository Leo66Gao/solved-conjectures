import Full338

/-! Companion audit, not a revision of the checked package.
This transports the already-proved at-most equality from the catalogue
to the manuscript's reflected data, removing zero uniformly. -/
namespace Erdos338.ReflectedCatalogueAudit
open CatalogueAdapter

def pos (A : Set ℕ) : Set ℕ := {x | 0 < x ∧ x ∈ A}

private theorem sum_dropZeros (xs : List ℕ) :
    (xs.filter (fun x => decide (0<x))).sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | zero => simp [List.sum_cons,ih]
    | succ x => simp [List.sum_cons,ih]

theorem ordinary_pos_iff (A : Set ℕ) (h : ℕ) :
    HasOrder (pos A) h ↔ HasOrder A h := by
  rw [ordinary_iff_list, ordinary_iff_list]
  constructor
  · rintro ⟨N,H⟩
    exact ⟨N,fun n hn => by
      obtain ⟨xs,ha,hs,hl⟩ := H n hn
      exact ⟨xs,fun x hx => (ha x hx).2,hs,hl⟩⟩
  · rintro ⟨N,H⟩
    refine ⟨N,fun n hn => ?_⟩
    obtain ⟨xs,ha,hs,hl⟩ := H n hn
    refine ⟨xs.filter (fun x => decide (0<x)), ?_,
      (sum_dropZeros xs).trans hs, (List.length_filter_le _ _).trans hl⟩
    intro x hx
    obtain ⟨hm,hp⟩ := List.mem_filter.mp hx
    exact ⟨of_decide_eq_true hp,ha x hm⟩

theorem restricted_pos_iff (A : Set ℕ) (h : ℕ) :
    HasRestrictedOrder (pos A) h ↔ HasRestrictedOrder A h := by
  rw [restricted_iff_list, restricted_iff_list]
  constructor
  · rintro ⟨N,H⟩
    exact ⟨N,fun n hn => by
      obtain ⟨xs,hd,ha,hs,hl⟩ := H n hn
      exact ⟨xs,hd,fun x hx => (ha x hx).2,hs,hl⟩⟩
  · rintro ⟨N,H⟩
    refine ⟨N,fun n hn => ?_⟩
    obtain ⟨xs,hd,ha,hs,hl⟩ := H n hn
    refine ⟨xs.filter (fun x => decide (0<x)), hd.sublist List.filter_sublist, ?_,
      (sum_dropZeros xs).trans hs, (List.length_filter_le _ _).trans hl⟩
    intro x hx
    obtain ⟨hm,hp⟩ := List.mem_filter.mp hx
    exact ⟨of_decide_eq_true hp,ha x hm⟩

private theorem order_pos (A : Set ℕ) : basisOrder (pos A) = basisOrder A := by
  unfold basisOrder
  congr 1
  funext h
  rw [propext (ordinary_pos_iff A h)]

private theorem restricted_order_pos (A : Set ℕ) :
    restrictedOrder (pos A) = restrictedOrder A := by
  unfold restrictedOrder
  congr 1
  funext h
  rw [propext (restricted_pos_iff A h)]

/-- The actual manuscript RHS with its positive-input convention, adapted
to arbitrary subsets of ℕ and arbitrary finite exact ordinary order. -/
noncomputable def reflectedAnswer (A : Set ℕ) : Prop :=
  ∀ h : ℕ, basisOrder A = (h : ℕ∞) → 2 ≤ h →
    ∃ N, ∀ n ≥ N, Pair.Footprint (pos A) (fringe (pos A) h) h n →
      Pair.ReflectedRHS (pos A) (fringe (pos A) h) h (h/2) (h%2) n

theorem equality_variant_reflected (A : Set ℕ) (base : ∃ h, HasOrder A h) :
    restrictedOrder A = basisOrder A ↔ reflectedAnswer A := by
  have base' : ∃ h, HasOrder (pos A) h := by
    obtain ⟨h, H⟩ := base
    exact ⟨h,(ordinary_pos_iff A h).mpr H⟩
  rw [← restricted_order_pos A, ← order_pos A]
  refine (equality_variant (pos A) base').trans ?_
  have positive : ∀ x, pos A x → 0 < x := fun _ hx => hx.1
  unfold equalityAnswer reflectedAnswer
  constructor
  · intro old h eq hh
    obtain ⟨N,H⟩ := old h ((order_pos A).trans eq) hh
    exact ⟨N,fun n hn foot => (Pair.sumset_rhs_iff_reflected_rhs hh positive).mp (H n hn foot)⟩
  · intro new h eq hh
    obtain ⟨N,H⟩ := new h ((order_pos A).symm.trans eq) hh
    exact ⟨N,fun n hn foot => (Pair.sumset_rhs_iff_reflected_rhs hh positive).mpr (H n hn foot)⟩

theorem existing_answer_iff_reflected (A : Set ℕ) (base : ∃ h, HasOrder A h) :
    erdos_338.variants.eq_order.answer A ↔ reflectedAnswer A :=
  (erdos_338.variants.eq_order A base).symm.trans (equality_variant_reflected A base)

#print axioms equality_variant_reflected
#print axioms existing_answer_iff_reflected

end Erdos338.ReflectedCatalogueAudit
