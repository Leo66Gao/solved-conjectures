import BoundedCatalogue
import BoundedGlue
import RecurrentLayers
import ModulusShrink
import DensityBridge

/-!
# Uniform boundedness in Erdős #338

The numerical bound here is explicit but not the sharp paper estimate.
Together with `Erdos338Solution`, this checks the catalogue statements
for all of the original parts of the problem.
-/

open scoped Pointwise

namespace Erdos338.Existence.Bounded
open Erdos338.Existence.Analytic Erdos338.Growth Erdos338.CatalogueAdapter

private theorem list_le_sum_of_mem {a : ℕ} {xs : List ℕ} (hx : a∈xs) :
    a≤xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons b xs ih =>
    rcases List.mem_cons.mp hx with h | h
    · rw [h,List.sum_cons]; omega
    · have := ih h
      rw [List.sum_cons]; omega

/-- The finite popularity schedule bounds both parameters independently of the basis. -/
theorem uniform_robust : Erdos338.Boundedness.UniformProgressions := by
  intro h
  let d := HHP.densityFactor h
  let E := schedule h d 0
  refine ⟨scheduleCost E, (E.map Entry.L).sum, ?_⟩
  intro A hA
  have hd : 0<d := HHP.densityFactor_pos h
  have hList := ordinary_iff_list.mp hA
  obtain ⟨onset,hDensity⟩ := hhpDensity_uniform hList
  have ev : EventualActive A E := active_eventually A h d onset hd hDensity
  obtain ⟨pre,e,tail,hs,recur,stable⟩ := recurrent_suffix_of_eventual A E ev
  let donors := (expand (e::tail)).map (Pack A)
  let S := fillsSet donors
  let C : Set ℕ := {n | Pack A e.layer n}
  have allZeros : ∀ P ∈ donors, P 0 := pack_map_zero A (expand (e::tail))
  have density : ∃ K : ℕ, ∀ n≥K, 2*n≤weight donors n :=
    eventual_weight_of_active A (e::tail) stable
  obtain ⟨a,m,T,hm,hS⟩ := Erdos338.mixedKneserRay donors allZeros density
  have h0 : 0∈C := pack_zero A e.layer
  have coD : ∀ K, ∃ N≥K, 3*N≤e.L*Erdos335.count C N :=
    dense_of_recurrent_activation recur
  obtain ⟨g,N,hg,hgL,hr⟩ := Erdos338.Shrink.shrink_eventual_ray
    S C m a T e.L hm h0 hS coD
  have eMem : e∈E := by rw [hs]; simp
  have gsmall : g≤e.L := by omega
  have modBound : g≤(E.map Entry.L).sum := gsmall.trans
    (list_le_sum_of_mem (List.mem_map.mpr ⟨e,eMem,rfl⟩))
  refine ⟨a,g,N,hg,modBound,?_⟩
  intro delete _ _ hdel n hn modEq
  obtain ⟨s,hsS,c,hcC,eq⟩ := hr n hn modEq
  have hh : fillsSet (List.replicate e.L (Pack A e.layer)) = Erdos338.Shrink.copies C e.L :=
    fills_repeated (fun L => Erdos338.Shrink.copies C L) rfl (fun _ => rfl) e.L
  have hcf : Fills ((List.replicate e.L e.layer).map (Pack A)) c := by
    rw [List.map_replicate]
    change c ∈ fillsSet (List.replicate e.L (Pack A e.layer))
    rwa [hh]
  have hsf : Fills ((expand (e::tail)).map (Pack A)) s := hsS
  obtain ⟨xs,nd,mem,avo,sm,len⟩ := safe_reserve_lift h d hd pre e tail hs hcf hsf delete
    (hdel.le.trans gsmall)
  change s+c=n at eq
  exact ⟨xs,nd,mem,avo,by omega,len⟩

#print axioms uniform_robust
end Erdos338.Existence.Bounded

namespace Erdos338
open CatalogueAdapter

theorem erdos_338.variants.bounded_by_order :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h) :=
  Boundedness.bounded_catalogue Existence.Bounded.uniform_robust

#print axioms erdos_338.variants.bounded_by_order

end Erdos338
