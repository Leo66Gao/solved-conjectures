import UniformPopularity
import Mathlib.Tactic

namespace Erdos338.Existence.Bounded
open Erdos338.Existence.Analytic Erdos338.Growth

def Active (A : Nat → Prop) (e : Entry) (n : Nat) :=
  6*n ≤ e.L * hits (Pack A e.layer) (2*n)

def Recurrent (A : Nat → Prop) (e : Entry) :=
  ∀ K : Nat, ∃ n ≥ K, Active A e n

def EventualActive (A : Nat → Prop) (es : List Entry) :=
  ∃ K : Nat, ∀ n ≥ K, ∃ e ∈ es, Active A e n

theorem recurrent_suffix_of_eventual (A : Nat → Prop) (es : List Entry)
    (ev : EventualActive A es) :
    ∃ pref e tail, es = pref ++ e :: tail ∧ Recurrent A e ∧ EventualActive A (e::tail) := by
  classical
  induction es with
  | nil =>
    obtain ⟨K,hK⟩ := ev
    obtain ⟨e,he,_⟩ := hK K le_rfl
    exact (List.not_mem_nil he).elim
  | cons hd tl ih =>
    by_cases hrec : Recurrent A hd
    · exact ⟨[],hd,tl,rfl,hrec,ev⟩
    · have hex : ∃ K : Nat, ∀ n ≥ K, ¬Active A hd n := by
        simpa only [Recurrent, not_forall, not_exists, not_and] using hrec
      obtain ⟨K,hK⟩ := hex
      have he : EventualActive A tl := by
        obtain ⟨T,hT⟩ := ev
        refine ⟨max K T, fun n hn => ?_⟩
        obtain ⟨e,hel,hea⟩ := hT n (by omega)
        rcases List.mem_cons.mp hel with rfl | ht
        · exact (hK n (by omega) hea).elim
        · exact ⟨e,ht,hea⟩
      obtain ⟨p,e,t,eq,hr,ha⟩ := ih he
      exact ⟨hd::p,e,t,by rw [eq]; rfl,hr,ha⟩

/-- Rescale an active prefix from 2n to the full cutoff used by the
cyclic-group shrinking theorem. Recurrent does not mean positive lower density. -/
theorem recurrent_dense {A : Nat → Prop} {e : Entry} (he : Recurrent A e) :
    ∀ K : Nat, ∃ N ≥ K, 3*N ≤ e.L * hits (Pack A e.layer) N := by
  intro K
  obtain ⟨n,hn,ha⟩ := he K
  refine ⟨2*n,by omega,?_⟩
  change 6*n ≤ e.L * hits (Pack A e.layer) (2*n) at ha
  rw [← Nat.mul_assoc]
  exact ha

def expand (es : List Entry) : List Layer :=
  es.flatMap (fun e => List.replicate e.L e.layer)

private theorem weight_expand_cons (A : Nat → Prop) (e : Entry) (es : List Entry) (x : Nat) :
    weight ((expand (e::es)).map (Pack A)) x =
      e.L*hits (Pack A e.layer) x + weight ((expand es).map (Pack A)) x := by
  simp [expand,weight,List.map_replicate,List.sum_append]

private theorem active_le_weight (A : Nat → Prop) (es : List Entry) (e : Entry)
    (he : e ∈ es) (x : Nat) :
    e.L*hits (Pack A e.layer) x ≤ weight ((expand es).map (Pack A)) x := by
  induction es with
  | nil => exact (List.not_mem_nil he).elim
  | cons hd es ih =>
    rw [weight_expand_cons]
    rcases List.mem_cons.mp he with rfl | heb
    · omega
    · have := ih heb; omega

private theorem hits_mono_cutoff (P : Nat → Prop) {n m : Nat} (h : n ≤ m) :
    hits P n ≤ hits P m := by
  classical
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    have hu : ∀ x, hits P (x+1) = hits P x + (if P (x+1) then 1 else 0) := fun _ => rfl
    rw [hu]; omega

theorem eventual_weight_of_active (A : Nat → Prop) (es : List Entry)
    (ev : EventualActive A es) :
    ∃ K : Nat, ∀ n ≥ K, 2*n ≤ weight ((expand es).map (Pack A)) n := by
  obtain ⟨K,hK⟩ := ev
  refine ⟨2*(K+1), fun x hx => ?_⟩
  let n := x/2
  have hn : K≤n ∧ 1≤n ∧ 2*n≤x := by dsimp [n]; omega
  obtain ⟨e,he,hact⟩ := hK n hn.1
  have hW := active_le_weight A es e he x
  have hM := Nat.mul_le_mul_left e.L (hits_mono_cutoff (Pack A e.layer) hn.2.2)
  have hh : 6*n ≤ weight ((expand es).map (Pack A)) x :=
    hact.trans (hM.trans hW)
  dsimp [n] at *; omega

theorem pack_map_zero (A : Nat → Prop) (es : List Layer) :
    ∀ P ∈ es.map (Pack A), P 0 := by
  intro Q hQ
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hQ
  exact pack_zero A e

private theorem fills_append_add {ps qs : List (Nat → Prop)} {x y : Nat}
    (hx : Fills ps x) (hy : Fills qs y) : Fills (ps++qs) (x+y) := by
  induction ps generalizing x with
  | nil => have eq : x=0 := hx; subst x; simpa
  | cons P ps ih =>
    obtain ⟨a,b,ha,hb,eq⟩ := hx
    exact ⟨a,b+y,ha,ih hb,by omega⟩

private theorem safe_mono {es : List Layer} {b b' : Nat} (h : b ≤ b')
    (hs : Safe b' es) : Safe b es := by
  induction es generalizing b b' with
  | nil => trivial
  | cons e es ih =>
    exact ⟨Nat.lt_of_le_of_lt h hs.1,ih (Nat.add_le_add_right h _) hs.2⟩

private theorem safe_repeat (b l : Nat) (s : Layer) (ss : List Layer)
    (bud : b+l*(2*s.r) < s.Q) (later : Safe (b+l*(2*s.r)) ss) :
    Safe b (List.replicate l s ++ ss) := by
  induction l generalizing b with
  | zero => simpa using later
  | succ i ih =>
    simp only [List.replicate_succ,List.cons_append,Safe]
    rw [Nat.succ_mul] at bud later
    constructor
    · omega
    · apply ih
      · omega
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later

private theorem next_ge (r d b : Nat) (hr : 0<r) (hd : 0<d) : d ≤ nextDensity r d b := by
  have hQ : 1 ≤ qBudget r d b := by unfold qBudget; omega
  have h : 1 ≤ 80*r*qBudget r d b := Nat.mul_pos (Nat.mul_pos (by decide) hr) hQ
  have k := Nat.mul_le_mul_right d (Nat.mul_pos h hd)
  simpa [nextDensity] using k

private theorem half_cost_le (l r : Nat) : l*(2*r) ≤ 4*r*l := by
  rw [Nat.mul_comm l]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem safe_expand_from (r d b ell : Nat) (hd : 0<d) (hle : ell ≤ copies d) :
    Safe (b+ell) (expand (schedule r d b)) := by
  induction r generalizing d b with
  | zero => trivial
  | succ r ih =>
    change Safe (b+ell) (List.replicate (copies d) (entry (r+1) d b).layer
      ++ expand (schedule r (nextDensity (r+1) d b) (nextBudget (r+1) d b)))
    apply safe_repeat
    · change b+ell+copies d*(2*(r+1)) < 1+copies d+4*(r+1)*copies d+b
      have h₁ := half_cost_le (copies d) (r+1)
      omega
    · have hnd := next_ge (r+1) d b (by omega) hd
      apply safe_mono _ (ih _ _ (hd.trans_le hnd) (hle.trans (copies_mono hnd)))
      change b+ell+copies d*(2*(r+1)) ≤ b+4*(r+1)*copies d+ell
      have h₁ := half_cost_le (copies d) (r+1)
      omega

private theorem head_cons_safe (r d b : Nat) (hd : 0<d) :
    let E := entry (r+1) d b
    let rest := schedule r (nextDensity (r+1) d b) (nextBudget (r+1) d b)
    Safe E.L (List.replicate E.L E.layer ++ expand (E::rest)) := by
  simp only [expand,List.flatMap_cons, ← List.append_assoc, ← List.replicate_add]
  change Safe (copies d) (List.replicate (copies d+copies d) (entry (r+1) d b).layer ++ expand (schedule r (nextDensity (r+1) d b) (nextBudget (r+1) d b)))
  apply safe_repeat
  · change copies d+(copies d+copies d)*(2*(r+1)) <
      1+copies d+4*(r+1)*copies d+b
    have eq : (copies d+copies d)*(2*(r+1)) = 4*(r+1)*copies d := by ring
    rw [eq]; omega
  · change Safe (copies d+(copies d+copies d)*(2*(r+1)))
      (expand (schedule r (nextDensity (r+1) d b) (nextBudget (r+1) d b)))
    have hnd := next_ge (r+1) d b (by omega) hd
    apply safe_mono _ (safe_expand_from r _ _ (copies d) (hd.trans_le hnd) (copies_mono hnd))
    change copies d+(copies d+copies d)*(2*(r+1)) ≤ b+4*(r+1)*copies d+copies d
    have eq : (copies d+copies d)*(2*(r+1)) = 4*(r+1)*copies d := by ring
    rw [eq]; omega

theorem reserve_safe_suffix (r d b : Nat) (hd : 0<d)
    (pref : List Entry) (e : Entry) (tail : List Entry)
    (hsplit : schedule r d b = pref ++ e::tail) :
    Safe e.L (List.replicate e.L e.layer ++ expand (e::tail)) ∧ 0 < e.L := by
  induction pref generalizing r d b with
  | nil =>
    cases r with
    | zero => simp [schedule] at hsplit
    | succ r =>
      change entry (r+1) d b ::
        schedule r (nextDensity (r+1) d b) (nextBudget (r+1) d b) = e::tail at hsplit
      obtain ⟨he,ht⟩ := List.cons.inj hsplit
      subst e; subst tail
      exact ⟨head_cons_safe r d b hd,Nat.mul_pos (Nat.mul_pos (by decide) hd) hd⟩
  | cons f pref ih =>
    cases r with
    | zero => simp [schedule] at hsplit
    | succ r =>
      change entry (r+1) d b ::
        schedule r (nextDensity (r+1) d b) (nextBudget (r+1) d b) = f::(pref++e::tail) at hsplit
      exact ih r _ _ (hd.trans_le (next_ge _ _ _ (by omega) hd)) (List.cons.inj hsplit).2

def cost (ss : List Layer) := (ss.map (fun s=>2*s.r)).sum

private theorem cost_append (ss ts : List Layer) : cost (ss++ts) = cost ss + cost ts := by
  simp [cost,List.sum_append]

private theorem cost_replicate (e : Entry) : cost (List.replicate e.L e.layer) = e.L*(2*e.r) := by
  simp [cost,List.map_replicate,Entry.layer]

private theorem cost_expand_le (ss : List Entry) : cost (expand ss) ≤ scheduleCost ss := by
  induction ss with
  | nil => simp [cost,scheduleCost,expand]
  | cons e ss ih =>
    change cost (List.replicate e.L e.layer ++ expand ss) ≤ 4*e.r*e.L+scheduleCost ss
    rw [cost_append,cost_replicate]
    have hl := half_cost_le e.L e.r
    omega

private theorem reserve_cost (pref : List Entry) (e : Entry) (tail : List Entry) :
    cost (List.replicate e.L e.layer ++ expand (e::tail)) ≤ scheduleCost (pref++e::tail) := by
  have ht := cost_expand_le tail
  have he : e.L*(2*e.r)+e.L*(2*e.r) = 4*e.r*e.L := by ring
  change cost (List.replicate e.L e.layer ++ (List.replicate e.L e.layer ++ expand tail)) ≤
    scheduleCost (pref++e::tail)
  rw [cost_append,cost_append,cost_replicate,← Nat.add_assoc,he]
  have eq : scheduleCost (pref++e::tail) = scheduleCost pref + 4*e.r*e.L + scheduleCost tail := by
    simp [scheduleCost,entryCost,List.sum_append,Nat.add_assoc]
  rw [eq]; omega

theorem safe_reserve_lift {A : Nat → Prop} (h d : Nat) (hd : 0<d)
    (pref : List Entry) (e : Entry) (tail : List Entry)
    (hsplit : schedule h d 0 = pref ++ e::tail) {x y : Nat}
    (hx : Fills ((List.replicate e.L e.layer).map (Pack A)) x)
    (hy : Fills ((expand (e::tail)).map (Pack A)) y)
    (E : List Nat) (hE : E.length ≤ e.L) :
    ∃ zs : List Nat, zs.Nodup ∧ (∀ z∈zs,A z) ∧ Avoid zs E ∧
      zs.sum=x+y ∧ zs.length ≤ scheduleCost (schedule h d 0) := by
  have hs := (reserve_safe_suffix h d 0 hd pref e tail hsplit).1
  have hF : Fills ((List.replicate e.L e.layer ++ expand (e::tail)).map (Pack A)) (x+y) := by
    rw [List.map_append]
    exact fills_append_add hx hy
  obtain ⟨z,nd,mem,avo,su,le⟩ := lift_form (safe_mono hE hs) hF E le_rfl
  refine ⟨z,nd,mem,avo,su,?_⟩
  have hc := reserve_cost pref e tail
  have le' : z.length ≤ cost (List.replicate e.L e.layer ++ expand (e::tail)) := le
  rw [hsplit]; exact le'.trans hc

#print axioms recurrent_suffix_of_eventual
#print axioms eventual_weight_of_active
#print axioms safe_reserve_lift
end Erdos338.Existence.Bounded
