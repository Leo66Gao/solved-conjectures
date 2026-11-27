import CollisionBridge

/-!
Quantitative popularity schedule for the Erdős #338 uniform upper bound.
A layer is entered only once here; its multiplicity is recorded separately.
-/

namespace Erdos338.Existence.Bounded

open Erdos338.Existence.Analytic

structure Entry where
  r : Nat
  Q : Nat
  L : Nat
  deriving DecidableEq

def Entry.layer (e : Entry) : Layer := ⟨e.r,e.Q⟩

def copies (d : Nat) : Nat := 8*d*d

def qBudget (r d b : Nat) : Nat := 1+copies d+4*r*copies d+b

def nextDensity (r d b : Nat) : Nat := 80*r*qBudget r d b*d*d

def nextBudget (r d b : Nat) : Nat := b+4*r*copies d

def entry (r d b : Nat) : Entry := ⟨r,qBudget r d b,copies d⟩

def schedule : Nat → Nat → Nat → List Entry
  | 0, _, _ => []
  | h+1,d,b => entry (h+1) d b :: schedule h (nextDensity (h+1) d b) (nextBudget (h+1) d b)

def cutoff : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | h+1,d,b => max 1 (max (nextDensity (h+1) d b)
      (cutoff h (nextDensity (h+1) d b) (nextBudget (h+1) d b)))

theorem cutoff_pos (h d b : Nat) : 0 < cutoff h d b := by
  cases h <;> simp only [cutoff] <;> omega

theorem copies_pos {d : Nat} (hd : 0<d) : 0<copies d := by
  unfold copies
  exact Nat.mul_pos (Nat.mul_pos (by decide) hd) hd

theorem qBudget_pos (r d b : Nat) : 0<qBudget r d b := by
  unfold qBudget
  omega

theorem nextDensity_pos {r d : Nat} (b : Nat) (hr : 0<r) (hd : 0<d) :
    0<nextDensity r d b := by
  unfold nextDensity
  have q := qBudget_pos r d b
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hr) q) hd) hd

private theorem restricted_rank_zero_hits (A : Nat → Prop) (N : Nat) :
    hits (R A 0) N = 0 := by
  classical
  induction N with
  | zero => rfl
  | succ N ih =>
    have no : ¬ R A 0 (N+1) := by
      rintro ⟨xs,_,_,eq,len⟩
      have en : xs=[] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      simp at eq
    change hits (R A 0) N + (if R A 0 (N+1) then 1 else 0) = 0
    simp [ih,no]

/-- Main scalar implication, with the lost incidence budget explicitly
separated from the popularity term. -/
theorem active_scalar (r Q d N M e D : Nat)
    (pos : 0<N) (hi : N≤d*M) (lo : 80*r*Q*d*d*e ≤ N+N)
    (inc : M*M ≤ N*(D+9*r*Q*e)) :
    6*N ≤ copies d*D := by
  have hh := Nat.mul_le_mul hi hi
  have h1 : N*N ≤ (d*d)*(M*M) := by
    calc N*N ≤ (d*M)*(d*M) := hh
         _ = _ := by ac_rfl
  have h2 : N*N ≤ N*((d*d)*(D+9*r*Q*e)) := by
    calc N*N ≤ (d*d)*(M*M) := h1
         _ ≤ (d*d)*(N*(D+9*r*Q*e)) := Nat.mul_le_mul_left _ inc
         _ = _ := by ac_rfl
  have h3 := Nat.le_of_mul_le_mul_left h2 pos
  let t := r*Q*d*d*e
  have hs : 72*t ≤ 80*t := Nat.mul_le_mul_right _ (by decide)
  have l80 : 80*t ≤ N+N := by simpa [t,Nat.mul_assoc] using lo
  have h4 : (d*d)*(9*r*Q*e)=9*t := by dsimp [t]; ac_rfl
  rw [Nat.mul_add,h4] at h3
  have h5 : copies d*D=8*((d*d)*D) := by unfold copies; ac_rfl
  rw [h5]; omega

theorem active_at (A : Nat→Prop) (inc : CollisionBound A)
    (h d b N : Nat) (hd : 0<d) (cut : cutoff h d b ≤ N)
    (den : N ≤ d * hits (R A h) N) :
    ∃ e ∈ schedule h d b, 6*N ≤ e.L*hits (Pack A e.layer) (2*N) := by
  induction h generalizing d b with
  | zero =>
    rw [restricted_rank_zero_hits,Nat.mul_zero] at den
    have pos := cutoff_pos 0 d b
    omega
  | succ h ih =>
    let r := h+1
    let Q := qBudget r d b
    let dd := nextDensity r d b
    let nb := nextBudget r d b
    have hn := Nat.lt_of_lt_of_le (cutoff_pos _ _ _) cut
    have hc : dd≤N ∧ cutoff h dd nb ≤ N := by
      simpa only [cutoff,Nat.max_le,dd,nb,r] using (Nat.max_le.mp cut).2
    have hr : 0<r := Nat.succ_pos _
    have hdd : 0<dd := nextDensity_pos b hr hd
    change ∃ e ∈ entry r d b :: schedule h dd nb, _
    by_cases next : N≤dd*hits (R A h) N
    · obtain ⟨e,em,ep⟩ := ih dd nb hdd hc.2 next
      exact ⟨e,List.mem_cons_of_mem _ em,ep⟩
    · refine ⟨entry r d b,List.mem_cons_self,?_⟩
      change 6*N ≤ copies d*hits (Pack A ⟨r,Q⟩) (2*N)
      apply active_scalar r Q d N (hits (R A r) N) (1+hits (R A h) N) _ hn den
      · change dd*(1+hits (R A h) N) ≤ N+N
        rw [Nat.mul_add,Nat.mul_one]
        omega
      · simpa [r] using inc r Q N hr (qBudget_pos r d b)

theorem active_eventually_with_budget (A : Set ℕ) (h d b n0 : Nat)
    (hd : 0<d) (den : ∀ n≥n0,n≤d*hits (R A h) n) :
    ∃ N0, ∀ n≥N0, ∃ e ∈ schedule h d b, 6*n ≤ e.L*hits (Pack A e.layer) (2*n) := by
  refine ⟨max n0 (cutoff h d b), fun n hn => ?_⟩
  have v := Nat.max_le.mp hn
  exact active_at A (CollisionBridge.collisionBound A) h d b n hd v.2 (den n v.1)

theorem active_eventually (A : Set ℕ) (h d n0 : Nat)
    (hd : 0<d) (den : ∀ n≥n0,n≤d*hits (R A h) n) :
    ∃ N0, ∀ n≥N0, ∃ e ∈ schedule h d 0, 6*n ≤ e.L*hits (Pack A e.layer) (2*n) :=
  active_eventually_with_budget A h d 0 n0 hd den

/-- The rank cost of using an entry twice (one baseline and one reserve). -/
def entryCost (e : Entry) : Nat := 4*e.r*e.L

def scheduleCost (es : List Entry) : Nat := (es.map entryCost).sum

theorem schedule_cost_cons (e : Entry) (es : List Entry) :
    scheduleCost (e::es) = entryCost e+scheduleCost es := rfl

theorem schedule_entry_budget {h d b : Nat} {pre post : List Entry} {e : Entry}
    (eq : schedule h d b = pre ++ e::post) :
    e.Q = b+scheduleCost pre+e.L+entryCost e+1 := by
  induction h generalizing d b pre with
  | zero => cases pre <;> simp [schedule] at eq
  | succ h ih =>
    cases pre with
    | nil =>
      have ee : entry (h+1) d b=e := (List.cons.inj eq).1
      subst e
      change 1+copies d+4*(h+1)*copies d+b = b+0+copies d+4*(h+1)*copies d+1
      omega
    | cons x pre =>
      obtain ⟨ee,tail⟩ := List.cons.inj eq
      subst x
      have q := ih tail
      rw [schedule_cost_cons]
      change e.Q = b+(4*(h+1)*copies d+scheduleCost pre)+e.L+entryCost e+1
      simpa only [nextBudget,Nat.add_assoc] using q

theorem copies_mono {x y : Nat} (hxy : x≤y) : copies x≤copies y := by
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 8 hxy) hxy

theorem density_mono {r d : Nat} (b : Nat) (hr : 0<r) (hd : 0<d) :
    d≤nextDensity r d b := by
  unfold nextDensity
  exact Nat.le_mul_of_pos_left d <|
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hr) (qBudget_pos r d b)) hd

theorem schedule_entry_attrs {h d b : Nat} (hd : 0<d) {e : Entry}
    (m : e∈schedule h d b) : 0<e.r ∧ 0<e.Q ∧ copies d≤e.L := by
  induction h generalizing d b with
  | zero => simp [schedule] at m
  | succ h ih =>
    rw [schedule,List.mem_cons] at m
    rcases m with e'|tail
    · subst e
      exact ⟨Nat.succ_pos _, qBudget_pos _ _ _,Nat.le_refl _⟩
    · have hi := ih (nextDensity_pos b (Nat.succ_pos h) hd) tail
      exact ⟨hi.1,hi.2.1,(copies_mono (density_mono b (Nat.succ_pos h) hd)).trans hi.2.2⟩

theorem schedule_lengths_nondecreasing (h d b : Nat) (hd : 0<d) :
    (schedule h d b).Pairwise (fun e f => e.L≤f.L) := by
  induction h generalizing d b with
  | zero => exact .nil
  | succ h ih =>
    rw [schedule,List.pairwise_cons]
    have hr : 0<h+1 := Nat.succ_pos _
    have hn := nextDensity_pos b hr hd
    constructor
    · intro e he
      exact (copies_mono (density_mono b hr hd)).trans (schedule_entry_attrs hn he).2.2
    · exact ih _ _ hn

theorem schedule_entry_rank_le {h d b : Nat} {e : Entry} (m : e∈schedule h d b) :
    e.r≤h := by
  induction h generalizing d b with
  | zero => simp [schedule] at m
  | succ h ih =>
    rw [schedule,List.mem_cons] at m
    rcases m with e'|tail
    · subst e; exact Nat.le_refl _
    · exact (ih tail).trans (Nat.le_succ _)

theorem schedule_length (h d b : Nat) : (schedule h d b).length=h := by
  induction h generalizing d b with
  | zero => rfl
  | succ h ih => simp [schedule, ih]

#print axioms active_eventually
#print axioms schedule_entry_budget
#print axioms schedule_lengths_nondecreasing
end Erdos338.Existence.Bounded
