import MixedDyson
import RobustLayers

/-! Bridge from a finite indexed family of integer sets and a parametric
arithmetic progression to the exact local-to-global proof's list interface.
Distinct slots are not required to be distinct sets; this matters for the
multiplicities in the adaptive packing construction. -/
namespace Erdos338.Existence.Analytic
open scoped BigOperators
open Erdos335 Erdos338.MixedDyson

theorem hits_eq_count (P : ℕ → Prop) (N : ℕ) : hits P N = count {x : ℕ | P x} N := by
  classical
  induction N with
  | zero => exact (count_zero {x : ℕ | P x}).symm
  | succ N ih =>
    rw [count_succ,← ih]
    rfl

private theorem weight_eq_donor_sum (ss : List (ℕ → Prop)) (N : ℕ) :
    weight ss N = ∑ i : Fin ss.length, count {x : ℕ | ss.get i x} N := by
  induction ss with
  | nil => simp [weight]
  | cons P ss ih =>
    erw [Fin.sum_univ_succ (n := ss.length) (f := fun i => count {x : ℕ | (P::ss).get i x} N)]
    change hits P N + weight ss N = count {x | P x} N + ∑ i : Fin ss.length, count {x | ss.get i x} N
    rw [hits_eq_count,ih]

private theorem fills_of_fin (ss : List (ℕ → Prop)) (b : Fin ss.length → ℕ)
    (hb : ∀ i, ss.get i (b i)) : Fills ss (∑ i, b i) := by
  induction ss with
  | nil => simp [Fills]
  | cons P ss ih =>
    erw [Fin.sum_univ_succ (n := ss.length) b]
    exact ⟨b 0,∑ j : Fin ss.length, b j.succ,hb 0,
      ih (fun j => b j.succ) (fun j => hb j.succ),rfl⟩

private theorem zero_receiver_empty (N : ℕ) : count ({0} : Set ℕ) N = 0 := by
  classical
  simp [count]; omega

/-- The threshold for the catalogue ray may be taken to be the first covered
term. This direct argument also covers offsets greater than the period. -/
theorem ray_of_progression {P : ℕ → Prop} (a g T : ℕ) (hg : 0 < g)
    (hp : ∀ t ≥ T, P (a+g*t)) :
    ∀ n ≥ a+g*T, n%g=a%g → P n := by
  intro n hn he
  let t := n/g-a/g
  have hd : a/g ≤ n/g := Nat.div_le_div_right (by omega)
  have hc : t+a/g=n/g := Nat.sub_add_cancel hd
  have hn' := Nat.mod_add_div n g
  have ha' := Nat.mod_add_div a g
  rw [he, ← hc, Nat.mul_add] at hn'
  have ht : a+g*t=n := by omega
  have hb : g*T≤g*t := by omega
  rw [← ht]
  exact hp t (Nat.le_of_mul_le_mul_left hb hg)

/-- A finite-index theorem is sufficient even when zero is the only left
summand and the list is empty. Prefix weights use exactly [1,N], on both sides. -/
theorem mixedKneserRay_of_fin
    (hfin : ∀ (m : ℕ) (A : Set ℕ) (B : Fin m → Set ℕ),
      0 ∈ A → (∀ i, 0 ∈ B i) →
      (∃ K : ℕ, ∀ n ≥ K, 2*n ≤ Erdos338.MixedDyson.mass A B n) →
      ∃ a g T : ℕ, 0 < g ∧ ∀ t ≥ T, a+g*t ∈ mixed A B) : MixedKneserRay := by
  intro ss hzero hweight
  let A : Set ℕ := {0}
  let B (i : Fin ss.length) : Set ℕ := {x : ℕ | ss.get i x}
  have hA : 0 ∈ A := Set.mem_singleton _
  have hB (i : Fin ss.length) : 0 ∈ B i := hzero _ (List.get_mem ss i)
  have hm (N : ℕ) : Erdos338.MixedDyson.mass A B N = weight ss N := by
    simp only [Erdos338.MixedDyson.mass,A,B,zero_receiver_empty,zero_add]
    exact (weight_eq_donor_sum ss N).symm
  obtain ⟨K,hK⟩ := hweight
  obtain ⟨a,g,T,hg,hp⟩ := hfin ss.length A B hA hB ⟨K,fun N hN => (hm N).symm ▸ hK N hN⟩
  refine ⟨a,g,a+g*T,hg,ray_of_progression a g T hg ?_⟩
  intro t ht
  obtain ⟨x,hx,b,hb,hs⟩ := hp t ht
  have hx0 : x=0 := hx
  rw [hx0,zero_add] at hs
  rw [← hs]
  exact fills_of_fin ss b hb

#print axioms mixedKneserRay_of_fin
end Erdos338.Existence.Analytic
