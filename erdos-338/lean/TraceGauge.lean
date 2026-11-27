import StructuralTrace
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos338.SparseTrace
open CatalogueAdapter Filter
open scoped BigOperators

noncomputable def prefixSet (C : Set ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Iic x).filter (· ∈ C)

private theorem mem_prefix {C : Set ℕ} {x a : ℕ} : a ∈ prefixSet C x ↔ a ≤ x ∧ a ∈ C := by
  classical
  simp [prefixSet]

/-- A finite ordinary rectangular sumset from a subset of arbitrarily
slow prescribed counting growth must hit every unbounded probe. -/
def GaugeTraceProperty (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ (T : Set ℕ), Unbounded T → ∀ (f : ℕ → ℕ), Tendsto f atTop atTop →
    ∃ (k : ℕ) (_ : k ≤ h) (B : Fin k → Set ℕ),
      (∀ i, B i ⊆ A) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ᶠ x in atTop, (prefixSet (⋃ i, B i) x).card ≤ f x) ∧ Unbounded (T ∩ box B)

private theorem cap_of_sparse {C : Set ℕ} {f g : ℕ → ℕ} {h x : ℕ}
    (hs : Sparse g C) (hf : h ≤ f x) (hg : ∀ u < x+1, g u < x → h*(u+2) ≤ f x) :
    h * (prefixSet C x).card ≤ f x := by
  classical
  let s := prefixSet C x
  by_cases hn : s.card ≤ 1
  · exact (Nat.mul_le_mul_left h hn).trans (by simpa using hf)
  have hh : s.Nonempty := Finset.card_pos.mp (by omega)
  let v := s.max' hh
  have hv : v ∈ s := s.max'_mem hh
  let t := s.erase v
  have ht' : t.card = s.card - 1 := Finset.card_erase_of_mem hv
  have ht : t.Nonempty := Finset.card_pos.mp (by omega)
  let u := t.max' ht
  have hu : u ∈ t := t.max'_mem ht
  have hus : u ∈ s := (Finset.mem_erase.mp hu).2
  have huv : u < v := lt_of_le_of_ne (s.le_max' _ hus) (Finset.mem_erase.mp hu).1
  have hvx := (mem_prefix.mp hv).1
  have hug := hs u (mem_prefix.mp hus).2 v (mem_prefix.mp hv).2 huv
  have hfx := hg u (by omega) (by omega)
  have hcard : t.card ≤ u+1 := by
    have hsub : t ⊆ Finset.range (u+1) := fun a ha =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (t.le_max' _ ha))
    simpa using Finset.card_le_card hsub
  exact (Nat.mul_le_mul_left h (show s.card ≤ u+2 by omega)).trans hfx

theorem trace_implies_gauge (A : Set ℕ) (h : ℕ) (H : TraceProperty A h) :
    GaugeTraceProperty A h := by
  classical
  intro T hT f hf
  have thresh (u : ℕ) : ∃ g : ℕ, ∀ x ≥ g, h*(u+2) ≤ f x :=
    eventually_atTop.mp (tendsto_atTop.mp hf (h*(u+2)))
  choose g hg using thresh
  obtain ⟨k,hk,B,hA,hD,hS,hU⟩ := H T hT g
  refine ⟨k,hk,B,hA,hD,?_,hU⟩
  have eventualH : ∀ᶠ x in atTop, h ≤ f x := tendsto_atTop.mp hf h
  filter_upwards [eventualH] with x hx
  let S (i : Fin k) := prefixSet (B i) x
  have hu : prefixSet (⋃ i, B i) x = Finset.univ.biUnion S := by
    ext a
    simp only [mem_prefix,Set.mem_iUnion,Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨ha, i, hi⟩
      exact ⟨i,mem_prefix.mpr ⟨ha,hi⟩⟩
    · rintro ⟨i,hi⟩
      exact ⟨(mem_prefix.mp hi).1,i,(mem_prefix.mp hi).2⟩
  rw [hu]
  by_cases hz : h = 0
  · have : k = 0 := by omega
    subst k
    simp [S]
  have hh : 0 < h := by omega
  have each (i : Fin k) : (S i).card ≤ f x / h := by
    apply (Nat.le_div_iff_mul_le hh).mpr
    rw [Nat.mul_comm]
    exact cap_of_sparse (hS i) hx fun u _ hu => hg u x (by omega)
  calc
    (Finset.univ.biUnion S).card ≤ ∑ i : Fin k, (S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin k, f x / h := Finset.sum_le_sum fun i _ => each i
    _ = k * (f x / h) := by simp
    _ ≤ h * (f x / h) := Nat.mul_le_mul_right _ hk
    _ ≤ f x := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _

private theorem finite_of_box {A : Set ℕ} {k : ℕ} {B : Fin k → Set ℕ}
    (hBA : ∀ i, B i ⊆ A) (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j)) {n : ℕ}
    (hn : n ∈ box B) :
    ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ k ∧ ∑ x ∈ S, x = n := by
  obtain ⟨f,hf,hs⟩ := hn
  have inj : Function.Injective f := by
    intro i j e
    by_contra h
    exact (Set.disjoint_left.mp (hd i j h)) (hf i) (e ▸ hf j)
  refine ⟨Finset.univ.image f,?_,by simpa using (Finset.card_image_le :
    (Finset.univ.image f).card ≤ (Finset.univ : Finset (Fin k)).card),?_⟩
  · rintro _ hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hBA i (hf i)
  · simpa [Finset.sum_image (s:=Finset.univ) (f:=fun x => x)
        (fun _ _ _ _ eq => inj eq)] using hs

theorem gauge_implies_restricted (A : Set ℕ) (h : ℕ) (H : GaugeTraceProperty A h) :
    HasRestrictedOrder A h := by
  rw [HasRestrictedOrder, eventually_atTop]
  by_contra! bad
  let T : Set ℕ := {n | ¬ ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧
    S.card ≤ h ∧ ∑ x ∈ S, x = n}
  have hu : Unbounded T := by
    intro N
    obtain ⟨n,hn,hbad⟩ := bad (N+1)
    refine ⟨n,by omega,?_⟩
    change ¬ ∃ S : Finset ℕ, _
    push Not
    exact hbad
  obtain ⟨k,hk,B,hA,hD,_,hU⟩ := H T hu id tendsto_id
  obtain ⟨n,_,hn,hn'⟩ := hU 0
  obtain ⟨S,hm,hc,hs⟩ := finite_of_box hA hD hn'
  exact hn ⟨S,hm,hc.trans hk,hs⟩

theorem restricted_iff_gauge_trace (A : Set ℕ) (h : ℕ) :
    HasRestrictedOrder A h ↔ GaugeTraceProperty A h :=
  ⟨fun H => trace_implies_gauge A h ((restricted_iff_sparse_trace A h).mp H),
    gauge_implies_restricted A h⟩

theorem equal_orders_iff_gauge_trace {A : Set ℕ} {h : ℕ}
    (ord : basisOrder A = (h : ℕ∞)) :
    restrictedOrder A = basisOrder A ↔ GaugeTraceProperty A h :=
  (equal_orders_iff_sparse_trace ord).trans
    ⟨trace_implies_gauge A h,fun H =>
      (restricted_iff_sparse_trace A h).mp (gauge_implies_restricted A h H)⟩

/-- A consequence stated without any colors or distinct sums: each escaping
set meets an ordinary h-fold prefix-thin sumset on an escaping subsequence. -/
theorem thin_ordinary_trace {A : Set ℕ} {h : ℕ}
    (ord : basisOrder A = (h : ℕ∞)) (eq : restrictedOrder A = basisOrder A)
    {T : Set ℕ} (hT : Unbounded T) {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    ∃ C ⊆ A, (∀ᶠ x in atTop, (prefixSet C x).card ≤ f x) ∧
      Unbounded (T ∩ {n | Erdos338.Ordinary C h n}) := by
  obtain ⟨k,hk,B,hA,hD,hg,hU⟩ := (equal_orders_iff_gauge_trace ord).mp eq T hT f hf
  let C := ⋃ i, B i
  have hB (i : Fin k) : B i ⊆ C := fun a ha => Set.mem_iUnion.mpr ⟨i,ha⟩
  refine ⟨C, ?_,hg,?_⟩
  · intro a ha
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
    exact hA i hi
  · intro N
    obtain ⟨n,hn,hTn,nB⟩ := hU N
    obtain ⟨S,hS,hc,hs⟩ := finite_of_box hB hD nB
    exact ⟨n,hn,hTn,S.toList,by simpa using hc.trans hk,
      fun x hx => hS x (by simpa using hx),S.sum_toList.trans hs⟩

end Erdos338.SparseTrace
