import Std

/-!
# Deletion-robust lifting in the quantitative order bound

Core arithmetic and finite combinatorial steps from the dyadic progression proof.
The analytic density and period inputs are **not** taken as axioms of this file.
-/
namespace Erdos338.Growth

/-- `Avoid xs es`: no label of `xs` occurs among the forbidden labels `es`. -/
def Avoid (xs es : List Nat) : Prop := ∀ x, x ∈ xs → x ∉ es

theorem avoid_symm {xs es : List Nat} (h : Avoid xs es) : Avoid es xs :=
  fun x hx h' => h x h' hx

/-- More pairwise disjoint candidate supports than forbidden labels ensure survival.
No nodup or nonemptiness assumption on the forbidden labels is needed. -/
theorem survivor {choices : List (List Nat)} (sep : choices.Pairwise Avoid)
    (E : List Nat) (hbudget : E.length < choices.length) :
    ∃ F ∈ choices, Avoid F E := by
  induction choices generalizing E with
  | nil => simp at hbudget
  | cons F rest ih =>
    by_cases h : Avoid F E
    · exact ⟨F, by simp, h⟩
    · simp only [Avoid, Classical.not_forall, Classical.not_imp, Classical.not_not] at h
      obtain ⟨z, hz, he⟩ := h
      obtain ⟨hr, ht⟩ := List.pairwise_cons.mp sep
      have hzlen := List.length_pos_of_mem he
      have hb : (E.erase z).length < rest.length := by
        rw [List.length_erase_of_mem he]
        simp only [List.length_cons] at hbudget
        omega
      obtain ⟨G, hG, hAvoid⟩ := ih ht (E.erase z) hb
      refine ⟨G, List.mem_cons_of_mem _ hG, ?_⟩
      intro a ha hae
      by_cases H : a = z
      · subst a; exact hr _ hG _ hz ha
      · exact hAvoid a ha ((List.mem_erase_of_ne H).mpr hae)

theorem natSumAppend (a b : List Nat) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp [List.sum]
  | cons x xs ih => simp [List.sum_cons, ih, Nat.add_assoc]

/-- All witnesses use distinct labels of the basis, have the prescribed sum, and
cost at most the slot's rank. -/
structure Slot (A : Nat → Prop) where
  target : Nat
  rank : Nat
  choices : List (List Nat)
  separated : choices.Pairwise Avoid
  valid : ∀ xs ∈ choices, xs.Nodup ∧ (∀ x ∈ xs, A x) ∧
      xs.sum = target ∧ xs.length ≤ rank

/-- Chronological upper bound on forbidden labels, including earlier lifted slots. -/
def BudgetsOK {A} (prior : Nat) : List (Slot A) → Prop
  | [] => True
  | s :: ss => prior < s.choices.length ∧ BudgetsOK (prior + s.rank) ss

/-- Greedy lifting of a whole list of ordinary summands to disjoint representations
while avoiding the initially deleted set. This is the disjoint-lifting step of §4. -/
theorem liftSlots {A} (ss : List (Slot A)) (E : List Nat) (prior : Nat)
    (he : E.length ≤ prior) (hb : BudgetsOK prior ss) :
    ∃ xs : List Nat, xs.Nodup ∧ (∀ x ∈ xs, A x) ∧ Avoid xs E ∧
      xs.sum = (ss.map Slot.target).sum ∧ xs.length ≤ (ss.map Slot.rank).sum := by
  induction ss generalizing E prior with
  | nil => exact ⟨[], List.Pairwise.nil, by simp, by simp [Avoid], rfl, Nat.le_refl _⟩
  | cons s ss ih =>
    obtain ⟨hslots, hrem⟩ := hb
    obtain ⟨F, hF, hoff⟩ := survivor s.separated E (Nat.lt_of_le_of_lt he hslots)
    obtain ⟨hFn, hFA, hsum, hlen⟩ := s.valid F hF
    have hbudget' : (F ++ E).length ≤ prior + s.rank := by
      rw [List.length_append]; omega
    obtain ⟨G, hGn, hGA, hg, hgs, hgl⟩ := ih (F ++ E) (prior + s.rank) hbudget' hrem
    refine ⟨F ++ G, List.pairwise_append.mpr ⟨hFn, hGn, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxy; subst y; exact hg x hy (List.mem_append_left _ hx)
    · intro x hx
      exact (List.mem_append.mp hx).elim (hFA x) (hGA x)
    · intro x hx
      rcases List.mem_append.mp hx with hl|hr
      · exact hoff x hl
      · exact fun hxE => hg x hr (List.mem_append_right _ hxE)
    · simp [natSumAppend, List.sum_cons, hsum, hgs]
    · simp only [List.length_append, List.map_cons, List.sum_cons]; omega

/-- Exact dyadic partial sum identity, giving the uniform bound on the number
of forbidden labels before a slot at scale 2^j. -/
theorem dyadicSum (j : Nat) : ((List.range (j+1)).map (fun i => 2^i)).sum + 1 = 2 * 2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.map_append, natSumAppend]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_succ]
    omega

/-- Once the logarithmic descent error is majorized by a linear function of the
step count, the envelope is C·2^k, not (2+ε)^k. Natural-number majorants suffice. -/
theorem dyadicEnvelope (f : Nat → Nat) (c : Nat)
    (step : ∀ k, f (k+1) ≤ 2*f k + c*(k+1)) (k : Nat) :
    f k + c*(k+2) ≤ 2^k * (f 0 + 2*c) := by
  induction k with
  | zero => simp; omega
  | succ k ih =>
    have hx := step k
    have hd : 2*(f k + c*(k+2)) ≤ 2*(2^k*(f 0+2*c)) := Nat.mul_le_mul_left 2 ih
    have hr : 2^(k+1)*(f 0+2*c) = 2*(2^k*(f 0+2*c)) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [hr]
    simp only [Nat.mul_add] at hd
    simp only [Nat.mul_add] at hx ⊢
    omega

/-- Vertex list of the walk through residue classes, using successive labels in `xs`. -/
private def states (g s : Nat) : List Nat → List Nat
  | [] => [s]
  | x :: xs => s :: states g ((s+x)%g) xs

private def terminal (g s : Nat) : List Nat → Nat
  | [] => s
  | x :: xs => terminal g ((s+x)%g) xs

private theorem terminal_eq {g s : Nat} (hs : s<g) (xs : List Nat) :
    terminal g s xs = (s+xs.sum)%g := by
  induction xs generalizing s with
  | nil => simp [terminal, Nat.mod_eq_of_lt hs]
  | cons x xs ih =>
    rw [terminal, ih (Nat.mod_lt _ (by omega)), Nat.mod_add_mod, Nat.add_assoc, List.sum_cons]

private theorem suffix_from_vertex {g s z} {xs : List Nat}
    (hz : z ∈ states g s xs) (hn : (states g s xs).Nodup) :
    ∃ ys, ys.Sublist xs ∧ terminal g z ys = terminal g s xs ∧ (states g z ys).Nodup := by
  induction xs generalizing s with
  | nil => simp [states] at hz; subst z; exact ⟨[], .refl _, rfl, hn⟩
  | cons x xs ih =>
    rcases List.mem_cons.mp hz with h|h
    · subst z; exact ⟨_, .refl _, rfl, hn⟩
    · obtain ⟨l, hl, hl', hl''⟩ := ih h (List.nodup_cons.mp hn).2
      exact ⟨l, .cons _ hl, hl', hl''⟩

private theorem erase_loops (g s : Nat) (xs : List Nat) :
    ∃ ys, ys.Sublist xs ∧ terminal g s ys = terminal g s xs ∧ (states g s ys).Nodup := by
  induction xs generalizing s with
  | nil => exact ⟨[], .refl _, rfl, by simp [states]⟩
  | cons x xs ih =>
    obtain ⟨l, hl, hlast, hno⟩ := ih ((s+x)%g)
    by_cases hh : s ∈ states g ((s+x)%g) l
    · obtain ⟨z, hz, hze, hzn⟩ := suffix_from_vertex hh hno
      exact ⟨z, .cons _ (hz.trans hl), hze.trans hlast, hzn⟩
    · exact ⟨x::l, .cons₂ _ hl, hlast, List.nodup_cons.mpr ⟨hh,hno⟩⟩

private theorem bound_by_universe (xs u : List Nat) (hn : xs.Nodup)
    (hsub : ∀ x ∈ xs, x∈u) : xs.length ≤ u.length := by
  induction xs generalizing u with
  | nil => simp
  | cons a xs ih =>
    have hau := hsub a (by simp)
    obtain ⟨hna,hnt⟩ := List.nodup_cons.mp hn
    have recStep := ih (u.erase a) hnt (by
      intro x hx
      exact (List.mem_erase_of_ne (show x ≠ a by intro h; subst x; exact hna hx)).mpr
        (hsub _ (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem hau] at recStep
    have := List.length_pos_of_mem hau
    simp only [List.length_cons]; omega

private theorem states_length (g s) (xs : List Nat) : (states g s xs).length = xs.length+1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [states, ih]

private theorem states_bounded {g s} (hs : s<g) (xs : List Nat) :
    ∀ z ∈ states g s xs, z < g := by
  induction xs generalizing s with
  | nil => simpa [states] using hs
  | cons x xs ih =>
    intro z hz; rcases List.mem_cons.mp hz with rfl | ht
    · exact hs
    · exact ih (Nat.mod_lt _ (by omega)) z ht

/-- Every attainable residue has a witness using at most g−1 members of the
original support. In particular the distinctness constraint is preserved. -/
theorem shortResidue {g : Nat} (hg : 0<g) (xs : List Nat) :
    ∃ ys : List Nat, ys.Sublist xs ∧ ys.sum % g = xs.sum % g ∧ ys.length < g := by
  obtain ⟨ys, hys, ht, hn⟩ := erase_loops g 0 xs
  rw [terminal_eq hg, terminal_eq hg] at ht
  have H := bound_by_universe (states g 0 ys) (List.range g) hn
    (fun z hz => List.mem_range.mpr (states_bounded hg ys z hz))
  rw [states_length, List.length_range] at H
  exact ⟨ys, hys, by simpa using ht, by omega⟩

/-- Finite many residue classes allow a *common* maximum on their correcting sums. -/
private theorem bounded_choices (P : Nat → Nat → Prop) (n : Nat)
    (h : ∀ r<n, ∃ e, P r e) : ∃ C, ∀ r<n, ∃ e, e≤C ∧ P r e := by
  induction n with
  | zero => exact ⟨0, by omega⟩
  | succ k ih =>
    obtain ⟨C,hC⟩ := ih (fun r hr => h r (by omega))
    obtain ⟨e,he⟩ := h k (by omega)
    refine ⟨max C e, ?_⟩
    intro r hr
    by_cases h' : r=k
    · subst r; exact ⟨e,Nat.le_max_right _ _,he⟩
    · obtain ⟨b,hb,hb'⟩ := hC r (by omega)
      exact ⟨b,Nat.le_trans hb (Nat.le_max_left _ _), hb'⟩

/-- Subset sums of `A` meet every residue class. -/
def CompleteMod (A : Nat → Prop) (g : Nat) : Prop := ∀ r<g, ∃ xs : List Nat,
  xs.Nodup ∧ (∀ x ∈ xs, A x) ∧ xs.sum % g = r

/-- Every sufficiently large target is a sum of at most k distinct members. -/
def RestrictedAtMost (A : Nat → Prop) (k : Nat) : Prop := ∃ N, ∀ n≥N, ∃ xs : List Nat,
  xs.Nodup ∧ (∀ x ∈ xs, A x) ∧ xs.sum = n ∧ xs.length ≤ k

/-- The same onset works for every deletion of up to g−1 members of A. -/
def RobustProgression (A : Nat → Prop) (a g K N : Nat) : Prop :=
  ∀ E : List Nat, E.Nodup → (∀ x ∈ E, A x) → E.length < g →
    ∀ t≥N, t%g=a%g → ∃ xs : List Nat,
      xs.Nodup ∧ (∀ x ∈ xs, A x) ∧ Avoid xs E ∧ xs.sum=t ∧ xs.length≤K

private theorem sub_congruence {n e a g : Nat} (ha : a≤n) (he : e≤n)
    (hr : e%g=(n-a)%g) : (n-e)%g=a%g := by
  have h1 := Nat.mod_add_div e g
  have h2 := Nat.mod_add_div (n-a) g
  have h : n-e+g*(e/g) = a+g*((n-a)/g) := by omega
  simpa only [Nat.add_mul_mod_self_left] using congrArg (· % g) h

/-- The uniform-order application, independent of the analytic progression
construction. A common deletion-robust class plus modular subset completeness
gives the explicit finite restricted-order budget K+g−1. -/
theorem robustProgression_lifts {A : Nat → Prop} {a g K N : Nat}
    (hg : 0<g) (hr : RobustProgression A a g K N) (hc : CompleteMod A g) :
    RestrictedAtMost A (K+g-1) := by
  let P (r e : Nat) := ∃ E : List Nat, E.Nodup ∧ (∀ x ∈ E, A x) ∧
       E.sum=e ∧ E.length<g ∧ e%g=r
  have h : ∀ r<g, ∃ e, P r e := by
    intro r hrg
    obtain ⟨xs,hn,hA,hs⟩ := hc r hrg
    obtain ⟨ys,hsub,hmod,hlen⟩ := shortResidue hg xs
    exact ⟨ys.sum, ys, hn.sublist hsub, fun x hx => hA x (hsub.subset hx),
      rfl, hlen, hmod.trans hs⟩
  obtain ⟨C,hC⟩ := bounded_choices P g h
  refine ⟨N+C+a, ?_⟩
  intro n hn
  obtain ⟨e,he,E,hEn,hEA,hEs,hEl,hEm⟩ := hC ((n-a)%g) (Nat.mod_lt _ hg)
  have hmn : (n-e)%g=a%g := sub_congruence (by omega) (by omega) hEm
  obtain ⟨xs,hxn,hxA,havoid,hxs,hxl⟩ := hr E hEn hEA hEl (n-e) (by omega) hmn
  refine ⟨xs++E,List.pairwise_append.mpr ⟨hxn,hEn,?_⟩,?_,?_,?_⟩
  · intro x hx y hy heq; subst y; exact havoid x hx hy
  · intro x hx; exact (List.mem_append.mp hx).elim (hxA x) (hEA x)
  · rw [natSumAppend, hEs, hxs]; omega
  · rw [List.length_append]; omega

/-- Conversely a bounded restricted order implies modular completeness. -/
theorem completeMod_of_restricted {A : Nat → Prop} {k g : Nat} (hg : 0<g)
    (H : RestrictedAtMost A k) : CompleteMod A g := by
  obtain ⟨N,hN⟩ := H
  intro r hr
  let n := r + g*N
  have hn : N ≤ n := by
    have H' := Nat.mul_le_mul_right N (show 1≤g by omega)
    simp [n] at *; omega
  obtain ⟨xs, hn, hA, hs, _⟩ := hN n hn
  exact ⟨xs,hn,hA, by rw [hs]; simp [n,Nat.mod_eq_of_lt hr]⟩

/-- Equivalence claimed at the progression modulus (not a proof that a bounded
robust progression exists). -/
theorem modCriterion_at_robust_class {A : Nat → Prop} {a g K N : Nat} (hg : 0<g)
    (hr : RobustProgression A a g K N) :
    CompleteMod A g ↔ RestrictedAtMost A (K+g-1) :=
  ⟨robustProgression_lifts hg hr, completeMod_of_restricted hg⟩

/-! ## Periodic mixed-radix lower examples

Stage k corresponds to h=k+5. The auxiliary half-radix squares at each step.
A stage with top place P and next radix u=2V is replaced by top place uP,
coins uC ∪ [0,u), and the next half-radix V². Zero is allowed as an unused
denomination throughout this at-most-order construction. -/
namespace Mixed

def V : Nat → Nat
  | 0 => 2
  | n+1 => V n * V n

def P : Nat → Nat
  | 0 => 4
  | n+1 => (2*V n) * P n

def coins : Nat → List Nat
  | 0 => List.range 5
  | n+1 => ((coins n).map (fun x => (2*V n)*x)) ++ List.range (2*V n)

theorem V_pos (k) : 0<V k := by
  induction k with
  | zero => decide
  | succ k ih => exact Nat.mul_pos ih ih

theorem P_pos (k) : 0<P k := by
  induction k with
  | zero => decide
  | succ k ih => exact Nat.mul_pos (Nat.mul_pos (by decide) (V_pos k)) ih

theorem V_formula (k) : V k = 2^(2^k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [V, ih, ←Nat.pow_add, Nat.pow_succ]
    congr 1; omega

theorem P_formula (k) : P k = 2^(2^k+k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [P, ih, V_formula, ←Nat.pow_succ', ←Nat.pow_add, Nat.pow_succ 2 k]
    congr 1; omega

private theorem sum_scale (u : Nat) (xs : List Nat) :
    (xs.map (fun x => u*x)).sum = u*xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, Nat.mul_add, ih]

private theorem twice_range (u : Nat) :
    2*(List.range u).sum + u = u*u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [List.range_succ, natSumAppend]
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.mul_succ, Nat.succ_mul] at *
    omega

/-- The unused mass of the modulus is at least P. Stronger induction reserves
twice the *next* radix, and so avoids any use of real-valued estimates. -/
theorem mass_invariant (k) : 2*(coins k).sum + 4*V k ≤ 7*P k := by
  induction k with
  | zero => decide
  | succ k ih =>
    let u := 2*V k
    have h0 : u*(2*(coins k).sum + 4*V k) ≤ u*(7*P k) :=
      Nat.mul_le_mul_left _ ih
    have h1 : u*(2*(coins k).sum)+u*(4*V k) ≤ 7*(u*P k) := by
      simpa only [Nat.mul_add, Nat.mul_left_comm u 7 (P k)] using h0
    have h2 := twice_range u
    have h3 : u*(4*V k) = u*u+4*(V k*V k) := by
      dsimp [u]
      calc
        2*V k*(4*V k) = 8*(V k*V k) := by ac_rfl
        _ = (2*V k)*(2*V k)+4*(V k*V k) := by
          have h' : 2*V k*(2*V k) = 4*(V k*V k) := by ac_rfl
          rw [h']; omega
    have h4 : u*(2*(coins k).sum) = 2*(u*(coins k).sum) := by ac_rfl
    change 2*((((coins k).map (fun x => u*x)) ++ List.range u).sum) +
        4*(V k*V k) ≤ 7*(u*P k)
    rw [natSumAppend, sum_scale, Nat.mul_add, ←h4]
    omega

theorem top_coin (k) : P k ∈ coins k := by
  induction k with
  | zero => decide
  | succ k ih =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨P k,ih,rfl⟩

/-- Every integer below P has an ordinary representation with at most one
denomination from each digit place. -/
theorem digits (k t : Nat) (ht : t<P k) :
    ∃ xs : List Nat, (∀ x ∈ xs, x ∈ coins k) ∧ xs.sum=t ∧ xs.length ≤ k+1 := by
  induction k generalizing t with
  | zero =>
    exact ⟨[t], by simpa [coins] using (show t<5 by change t<4 at ht; omega), by simp, by simp⟩
  | succ k ih =>
    let u := 2*V k
    have hu : 0<u := Nat.mul_pos (by decide) (V_pos _)
    have hd : t/u < P k := (Nat.div_lt_iff_lt_mul hu).mpr (by
      change t < u*P k at ht; simpa [Nat.mul_comm] using ht)
    obtain ⟨xs, hxs, hsum, hlen⟩ := ih _ hd
    refine ⟨(t%u)::(xs.map (fun x=>u*x)),?_,?_,?_⟩
    · intro x hx; rcases List.mem_cons.mp hx with hh|hh
      · subst x; exact List.mem_append_right _ (List.mem_range.mpr (Nat.mod_lt _ hu))
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hh
        exact List.mem_append_left _ (List.mem_map.mpr ⟨y,hxs _ hy,rfl⟩)
    · rw [List.sum_cons, sum_scale, hsum, Nat.mod_add_div]
    · simp only [List.length_cons,List.length_map]; omega

/-- Basis with finitely many exceptional doubled coins, and two infinite
residue classes modulo 8P. -/
def A (k x : Nat) : Prop :=
  x ∈ (coins k).map (fun c => 2*c) ∨ x%(8*P k) ≤ 1

def OrdinaryAtMost (B : Nat → Prop) (h : Nat) : Prop := ∃ N, ∀ n≥N, ∃ xs : List Nat,
  (∀ x ∈ xs, B x) ∧ xs.sum=n ∧ xs.length ≤h

private theorem sum_replicate_nat (r p : Nat) : (List.replicate r p).sum = r*p := by
  induction r with
  | zero => simp
  | succ r ih => simp [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem ordinary_upper (k : Nat) : OrdinaryAtMost (A k) (k+5) := by
  refine ⟨0,?_⟩; intro n _
  let p := P k
  let m := 8*p
  let r := n%m
  let t := r/2
  have hp : 0<p := P_pos k
  have hm : 0<m := by dsimp [m]; omega
  have hr : r<m := Nat.mod_lt _ hm
  have ht : t<4*p := by dsimp [t,m] at *; omega
  have hd : t/p<4 := (Nat.div_lt_iff_lt_mul hp).mpr ht
  obtain ⟨xs,hxs,hxs',hxl⟩ := digits k (t%p) (Nat.mod_lt _ hp)
  let ys := (List.replicate (t/p) p) ++ xs
  have hy : ∀ y ∈ ys, y ∈ coins k := by
    intro y hy
    rcases List.mem_append.mp hy with hy|hy
    · exact (List.eq_of_mem_replicate hy) ▸ top_coin k
    · exact hxs y hy
  have hs : ys.sum=t := by
    dsimp [ys]; rw [natSumAppend,sum_replicate_nat,hxs',Nat.mul_comm (t/p) p,Nat.add_comm,Nat.mod_add_div]
  have hl : ys.length ≤k+4 := by
    simp only [ys,List.length_append,List.length_replicate]; omega
  let tail := r%2 + m*(n/m)
  have htail : tail%m ≤ 1 := by
    rw [show tail%m=(r%2)%m by exact Nat.add_mul_mod_self_left ..]
    exact Nat.le_trans (Nat.mod_le _ _) (by omega)
  have hrec : tail + 2*t = n := by
    have h₁ := Nat.mod_add_div r 2
    have h₂ := Nat.mod_add_div n m
    change r+m*(n/m)=n at h₂
    dsimp [tail,t]; omega
  refine ⟨tail::ys.map (fun c=>2*c),?_,?_,?_⟩
  · intro x hx; rcases List.mem_cons.mp hx with hx|hx
    · subst x; exact Or.inr htail
    · obtain ⟨y,hy',rfl⟩ := List.mem_map.mp hx
      exact Or.inl (List.mem_map.mpr ⟨y, hy _ hy',rfl⟩)
  · rw [List.sum_cons,sum_scale,hs]; exact hrec
  · simp only [List.length_map,List.length_cons]; omega

private theorem sum_erase (x : Nat) (u : List Nat) (hx : x∈u) : (u.erase x).sum+x=u.sum := by
  induction u with
  | nil => simp at hx
  | cons a u ih =>
    by_cases h : a=x
    · subst a; simp [List.sum_cons, Nat.add_comm]
    · have h' : x∈u := (List.mem_cons.mp hx).resolve_left (Ne.symm h)
      simp only [List.erase_cons, beq_iff_eq, h, if_false, List.sum_cons]
      have := ih h'; omega

private theorem residue_mass (m : Nat) (xs E : List Nat) (hn : xs.Nodup)
    (hc : ∀ x∈xs, x∈E ∨ x%m≤1) :
    (xs.map (·%m)).sum ≤ E.sum+xs.length := by
  induction xs generalizing E with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hn
    rcases hc a (by simp) with hae|hasmall
    · have hsmall : ∀ x∈xs, x∈E.erase a ∨ x%m≤1 := by
        intro x hx; rcases hc x (List.mem_cons_of_mem a hx) with h|h
        · exact Or.inl ((List.mem_erase_of_ne (by intro eq; subst x; exact hnot hx)).mpr h)
        · exact Or.inr h
      have hh := ih (E.erase a) hnd hsmall
      have := sum_erase a E hae
      have := Nat.mod_le a m
      simp only [List.map_cons,List.sum_cons,List.length_cons]; omega
    · have hh := ih E hnd (fun x hx=>hc x (List.mem_cons_of_mem a hx))
      simp only [List.map_cons,List.sum_cons,List.length_cons]; omega

private theorem sum_mod (m : Nat) (xs : List Nat) :
    (xs.map (·%m)).sum%m = xs.sum%m := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Nat.mod_add_mod, ←Nat.add_mod_mod, ih, Nat.add_mod_mod]

/-- Every distinct witness of residue 8P−1 has length at least P. This holds
pointwise, not only for an isolated finite set of test targets. -/
theorem long_residue (k : Nat) (xs : List Nat) (hn : xs.Nodup)
    (hA : ∀ x∈xs, A k x) (hr : xs.sum%(8*P k)=8*P k-1) : P k ≤ xs.length := by
  have hm := residue_mass (8*P k) xs ((coins k).map (fun c => 2*c)) hn hA
  have hc := Nat.mod_le ((xs.map (·%(8*P k))).sum) (8*P k)
  rw [sum_mod, hr] at hc
  rw [sum_scale] at hm
  have := mass_invariant k
  have := V_pos k
  omega

/-- Lower bound for *every* budget of the mixed-radix basis, with no assumed
bound or density theorem about arbitrary bases. -/
theorem restricted_lower (k H : Nat) (hr : RestrictedAtMost (A k) H) : 2^(2^k+k+1) ≤ H := by
  rw [← P_formula]
  obtain ⟨N,hN⟩ := hr
  let m := 8*P k
  have hm : 0<m := by dsimp [m]; have := P_pos k; omega
  let n := m-1 + m*N
  have hn : n≥N := by
    have h := Nat.mul_le_mul_right N (show 1≤m by omega)
    dsimp [n]; simp only [Nat.one_mul] at h; omega
  obtain ⟨xs,hnd,hA,hs,hl⟩ := hN n hn
  have hmod : n%m=m-1 := by
    rw [show n%m=(m-1)%m by exact Nat.add_mul_mod_self_left ..]
    exact Nat.mod_eq_of_lt (by omega)
  exact Nat.le_trans (long_residue k xs hnd hA (hs ▸ hmod)) hl

private theorem sum_ge_member (x : Nat) (xs : List Nat) (hx : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with hh|hh
    · subst x; simp [List.sum_cons]
    · have := ih hh; simp only [List.sum_cons]; omega

/- A residue r is covered by the first r terms of the class 1 progression. -/
private def anchors (m : Nat) : Nat → List Nat
  | 0 => []
  | r+1 => (1+m*r) :: anchors m r

private theorem anchor_bounds {m : Nat} (hm : 1<m) (r : Nat) :
    ∀ x∈anchors m r, x<1+m*r ∧ x%m=1 := by
  induction r with
  | zero => simp [anchors]
  | succ r ih =>
    intro x hx; rcases List.mem_cons.mp hx with hx|hx
    · subst x; constructor
      · rw [Nat.mul_succ]; omega
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]
    · obtain ⟨h,h'⟩ := ih x hx; rw [Nat.mul_succ]; exact ⟨by omega,h'⟩

private theorem anchors_nodup {m : Nat} (hm : 1<m) (r : Nat) : (anchors m r).Nodup := by
  induction r with
  | zero => exact List.Pairwise.nil
  | succ r ih =>
    exact List.nodup_cons.mpr ⟨fun hx => (Nat.lt_irrefl _) (anchor_bounds hm _ _ hx).1, ih⟩

private theorem anchors_sum (m r : Nat) : (anchors m r).sum % m = r%m := by
  induction r with
  | zero => simp [anchors]
  | succ r ih =>
    rw [anchors,List.sum_cons, Nat.add_comm (1+m*r), ←Nat.add_assoc,
        Nat.add_mul_mod_self_left, Nat.add_comm, ←Nat.add_mod_mod, ih, Nat.add_mod_mod, Nat.add_comm]

private theorem anchors_len (m r : Nat) : (anchors m r).length=r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [anchors, ih]

/-- Each mixed-radix basis really has finite restricted order. In fact every
sufficiently large integer uses at most 8P distinct members. -/
theorem restricted_upper (k : Nat) : RestrictedAtMost (A k) (8*P k) := by
  let m := 8*P k
  have hm : 1<m := by have := P_pos k; dsimp [m]; omega
  let B := (List.range m).map (fun r => (anchors m r).sum)
  refine ⟨2*B.sum+1,?_⟩
  intro n hn
  let r := n%m
  have hrg : r<m := Nat.mod_lt _ (by omega)
  let es := anchors m r
  have he : es.sum ≤ B.sum := sum_ge_member _ _ (List.mem_map.mpr ⟨r,List.mem_range.mpr hrg,rfl⟩)
  let z := n-es.sum
  have hz : es.sum<z := by dsimp [z]; omega
  have hzA : A k z := Or.inr (by
    have hmod : es.sum%m=(n-0)%m := by
      change (anchors m r).sum%m=(n-0)%m
      rw [anchors_sum,Nat.mod_eq_of_lt hrg,Nat.sub_zero]
    have h : z%m=0%m := sub_congruence (by omega) (by omega) hmod
    change z%m≤1; rw [h]; simp)
  refine ⟨z::es,List.nodup_cons.mpr ⟨fun h => (Nat.not_le_of_gt hz) (sum_ge_member _ _ h),
      anchors_nodup hm _⟩,?_,?_,?_⟩
  · intro x hx; rcases List.mem_cons.mp hx with hh|hh
    · subst x; exact hzA
    · exact Or.inr (Nat.le_of_eq (anchor_bounds hm r x hh).2)
  · rw [List.sum_cons]; dsimp [z]; omega
  · rw [List.length_cons,anchors_len]; omega

/-- The unconditional mixed-radix witness family gives the claimed double
exponential lower bound for ordinary order **at most** k+5. -/
theorem mixedRadixGap (k : Nat) : ∃ B : Nat → Prop, OrdinaryAtMost B (k+5) ∧
    RestrictedAtMost B (8*P k) ∧ ∀ H, RestrictedAtMost B H → 2^(2^k+k+1)≤H :=
  ⟨A k,ordinary_upper k,restricted_upper k,restricted_lower k⟩

private theorem unit_coin (k) : 1 ∈ coins k := by
  cases k with
  | zero => decide
  | succ k =>
    apply List.mem_append_right
    apply List.mem_range.mpr
    have := V_pos k; omega

/-- Split into scaled old digits and the new radix's digits. The sum of s
small digits is at most s·(u−1), written without subtraction. -/
private theorem peel (k : Nat) (xs : List Nat) (hv : ∀ x∈xs, x∈coins (k+1)) :
    ∃ (ys : List Nat) (a s : Nat), (∀ y∈ys, y∈coins k) ∧
     xs.sum = (2*V k)*ys.sum + a ∧ ys.length+s = xs.length ∧ a+s ≤ (2*V k)*s := by
  induction xs with
  | nil => exact ⟨[],0,0,by simp,by simp,by simp,by simp⟩
  | cons x xs ih =>
    obtain ⟨ys,a,s,hv',hs,hl,hA⟩ := ih (fun y hy=>hv _ (List.mem_cons_of_mem _ hy))
    rcases List.mem_append.mp (hv x (by simp)) with hr|hr
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
      refine ⟨z::ys,a,s,?_,?_,?_,hA⟩
      · intro y hy; rcases List.mem_cons.mp hy with e|e
        · exact e ▸ hz
        · exact hv' y e
      · rw [List.sum_cons,hs,List.sum_cons,Nat.mul_add,Nat.add_assoc]
      · simp only [List.length_cons]; omega
    · have hx := List.mem_range.mp hr
      refine ⟨ys,x+a,s+1,hv',?_,?_,?_⟩
      · rw [List.sum_cons,hs]; omega
      · simp only [List.length_cons]; omega
      · rw [Nat.mul_succ]; omega

private theorem sum_target_cost (k : Nat) (xs : List Nat) (Z : Nat)
    (hxs : ∀ x∈xs, x∈coins k) (hmod : xs.sum+1 = 4*P k*Z) : k+4≤xs.length := by
  induction k generalizing xs Z with
  | zero =>
    have hu : ∀ ws : List Nat, (∀ x∈ws, x≤4) → ws.sum≤4*ws.length := by
      intro ws; induction ws with
      | nil => simp
      | cons x l ih =>
        intro h
        have h' := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
        have hx := h x (by simp)
        simp only [List.sum_cons,List.length_cons]; omega
    have hcount := hu xs (fun x hx => Nat.le_of_lt_succ (List.mem_range.mp (hxs _ hx)))
    change xs.sum+1=16*Z at hmod
    omega
  | succ k ih =>
    obtain ⟨ys,a,s,hys,hsum,hlen,hsmall⟩ := peel k xs hxs
    let u := 2*V k
    let base := 4*P k*Z
    have hu : 1<u := by dsimp [u]; have := V_pos k; omega
    have hraw : u*ys.sum+a+1=u*base := by
      change xs.sum+1=4*(u*P k)*Z at hmod
      rw [hsum] at hmod
      calc
        _ = 4*(u*P k)*Z := hmod
        _ = u*base := by dsimp [base]; ac_rfl
    have hy : ys.sum < base := Nat.lt_of_mul_lt_mul_left (show u*ys.sum<u*base by omega)
    let Q := base-ys.sum
    have hQ : u*Q = a+1 := by
      have hh : u*ys.sum+u*Q=u*base := by
        rw [←Nat.mul_add]; congr 1; dsimp [Q]; omega
      omega
    have hposQ : 0<Q := by dsimp [Q]; omega
    have hposS : 0<s := by
      apply Classical.byContradiction; intro h
      have hzero : s=0 := by omega
      rw [hzero,Nat.mul_zero] at hsmall
      have h' := Nat.le_mul_of_pos_right u hposQ
      omega
    have hQs : Q≤s := Nat.le_of_mul_le_mul_left (show u*Q≤u*s by
      change a+s≤u*s at hsmall; omega) (by omega)
    let ws := ys++List.replicate (Q-1) 1
    have hw : ∀ y∈ws,y∈coins k := by
      intro y hy; rcases List.mem_append.mp hy with h|h
      · exact hys _ h
      · exact (List.eq_of_mem_replicate h) ▸ unit_coin k
    have heq : ws.sum+1=4*P k*Z := by
      dsimp [ws]; rw [natSumAppend,sum_replicate_nat,Nat.mul_one]
      change ys.sum+(base-ys.sum-1)+1=base; omega
    have hcost := ih ws Z hw heq
    simp only [ws,List.length_append,List.length_replicate] at hcost
    omega

/-- Replace tail labels by their residues 0 and 1, keeping exceptional coins with
multiplicity (ordinary rather than restricted representations). -/
private theorem collapse (k : Nat) (xs : List Nat) (hv : ∀ x∈xs,A k x) :
    ∃ (ys : List Nat) (j : Nat), (∀ y∈ys,y∈coins k) ∧ ys.length+j≤xs.length ∧
      (2*ys.sum+j)%(8*P k)=xs.sum%(8*P k) := by
  induction xs with
  | nil => exact ⟨[],0,by simp,by simp,by simp⟩
  | cons x xs ih =>
    let m:=8*P k
    obtain ⟨ys,j,hy,hl,hs⟩ := ih (fun y h=>hv y (List.mem_cons_of_mem x h))
    rcases hv _ (List.mem_cons_self) with he|ht
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
      refine ⟨c::ys,j,?_,?_,?_⟩
      · intro y h; rcases List.mem_cons.mp h with e|e
        · exact e ▸ hc
        · exact hy y e
      · simp only [List.length_cons]; omega
      · simp only [List.sum_cons,Nat.mul_add,Nat.add_assoc]
        rw [←Nat.add_mod_mod,hs,Nat.add_mod_mod]
    · refine ⟨ys,x%m+j,hy,?_,?_⟩
      · change x%m≤1 at ht
        simp only [List.length_cons]; omega
      · rw [List.sum_cons]
        change (2*ys.sum+(x%m+j))%m=(x+xs.sum)%m
        rw [show 2*ys.sum+(x%m+j)=x%m+(2*ys.sum+j) by omega,
          Nat.mod_add_mod,←Nat.add_mod_mod, hs, Nat.add_mod_mod]

/-- The same troublesome residue forces at least k+5 ordinary summands: after
retaining one odd tail, each pair of further odd tails becomes a unit coin. -/
theorem ordinary_long_residue (k : Nat) (xs : List Nat) (hv : ∀ x∈xs,A k x)
    (hn : xs.sum%(8*P k)=8*P k-1) : k+5≤xs.length := by
  let p:=P k
  let m:=8*p
  have hp : 0<p := P_pos k
  obtain ⟨ys,j,hy,hl,hs⟩ := collapse k xs hv
  rw [hn] at hs
  let q:=(2*ys.sum+j)/m
  have hraw : m-1+m*q=2*ys.sum+j := hs ▸ (Nat.mod_add_div (2*ys.sum+j) m)
  have hstep : 2*ys.sum+j+1=2*(4*p*(q+1)) := by
    change 8*p-1+(8*p)*q=2*ys.sum+j at hraw
    rw [Nat.mul_assoc 8 p q] at hraw
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_assoc 4 p q,Nat.mul_add]
    omega
  have hd := Nat.mod_add_div j 2
  have hh := Nat.mod_lt j (show 0<2 by decide)
  have hodd : j%2=1 := by omega
  let zs:=ys++List.replicate (j/2) 1
  have hz : ∀ z∈zs,z∈coins k := by
    intro z hz; rcases List.mem_append.mp hz with h|h
    · exact hy _ h
    · exact (List.eq_of_mem_replicate h) ▸ unit_coin k
  have heq : zs.sum+1=4*p*(q+1) := by
    dsimp [zs]; rw [natSumAppend,sum_replicate_nat,Nat.mul_one]
    omega
  have H := sum_target_cost k zs (q+1) hz heq
  simp only [zs,List.length_append,List.length_replicate] at H
  omega

/-- Sharp ordinary order, not just an upper bound. -/
theorem ordinary_lower (k h : Nat) (ho : OrdinaryAtMost (A k) h) : k+5≤h := by
  obtain ⟨N,hN⟩ := ho
  let m:=8*P k
  have hm : 0<m := by dsimp [m]; have := P_pos k; omega
  let n:=m-1+m*N
  have hn : n≥N := by
    dsimp [n]; have := Nat.le_mul_of_pos_right N hm; rw [Nat.mul_comm N m] at this; omega
  obtain ⟨xs,hA,hEq,hL⟩ := hN n hn
  have H : n%m=m-1 := by dsimp [n]; rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  exact Nat.le_trans (ordinary_long_residue k xs hA (hEq ▸ H)) hL

/-- Unconditional quantitative lower gap with the ordinary order *exactly* k+5. -/
theorem exactMixedRadixGap (k : Nat) : ∃ B : Nat → Prop, OrdinaryAtMost B (k+5) ∧
    (∀ h, OrdinaryAtMost B h → k+5≤h) ∧ RestrictedAtMost B (8*P k) ∧
    ∀ H, RestrictedAtMost B H → 2^(2^k+k+1)≤H :=
  ⟨A k, ordinary_upper k, ordinary_lower k, restricted_upper k, restricted_lower k⟩

private theorem sum_dropZeros (xs : List Nat) :
    (xs.filter (fun x => decide (0<x))).sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | zero => simp [List.sum_cons,ih]
    | succ x => simp [List.sum_cons,ih]

private theorem ordinary_positive_iff (B : Nat→Prop) (h) :
    OrdinaryAtMost (fun x => 0<x ∧ B x) h ↔ OrdinaryAtMost B h := by
  constructor
  · rintro ⟨N,H⟩
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨xs,hA,hs,hl⟩ := H n hn
    exact ⟨xs,fun x hx=>(hA x hx).2,hs,hl⟩
  · rintro ⟨N,H⟩
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨xs,hA,hs,hl⟩ := H n hn
    let ys:=xs.filter (fun x=>decide (0<x))
    refine ⟨ys,?_,(sum_dropZeros xs).trans hs,Nat.le_trans (List.length_filter_le ..) hl⟩
    intro x hx; obtain ⟨hm,hp⟩ := List.mem_filter.mp hx
    exact ⟨of_decide_eq_true hp,hA x hm⟩

private theorem restricted_positive_iff (B : Nat→Prop) (h) :
    RestrictedAtMost (fun x => 0<x ∧ B x) h ↔ RestrictedAtMost B h := by
  constructor
  · rintro ⟨N,H⟩
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨xs,hn,hA,hs,hl⟩ := H n hn
    exact ⟨xs,hn,fun x hx=>(hA x hx).2,hs,hl⟩
  · rintro ⟨N,H⟩
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨xs,hnd,hA,hs,hl⟩ := H n hn
    let ys:=xs.filter (fun x=>decide (0<x))
    refine ⟨ys,hnd.sublist (List.filter_sublist),?_,(sum_dropZeros xs).trans hs,
      Nat.le_trans (List.length_filter_le ..) hl⟩
    intro x hx; obtain ⟨hm,hp⟩ := List.mem_filter.mp hx
    exact ⟨of_decide_eq_true hp,hA x hm⟩

/-- Identical theorem with *positive* labels only, so there is no auxiliary
convention about whether zero is allowed in an additive basis. -/
theorem exactPositiveMixedRadixGap (k : Nat) : ∃ B : Nat → Prop, ¬ B 0 ∧
    OrdinaryAtMost B (k+5) ∧ (∀ h, OrdinaryAtMost B h → k+5≤h) ∧
    RestrictedAtMost B (8*P k) ∧ ∀ H, RestrictedAtMost B H → 2^(2^k+k+1)≤H := by
  obtain ⟨C,ho,hom,hr,hrm⟩:=exactMixedRadixGap k
  exact ⟨fun x => 0<x ∧ C x, by simp, (ordinary_positive_iff _ _).mpr ho,
    fun h ha=>hom h ((ordinary_positive_iff _ _).mp ha), (restricted_positive_iff _ _).mpr hr,
    fun H ha=>hrm H ((restricted_positive_iff _ _).mp ha)⟩

end Mixed
/-! ## Universal moduli and finite removal (the analytic bridge is explicit) -/

/-- Completeness descends to every positive divisor of the test modulus. -/
theorem completeMod_dvd {A M g} (hM : 0<M) (hd : g∣M) (hc : CompleteMod A M) :
    CompleteMod A g := by
  intro r hr
  have hg := Nat.le_of_dvd hM hd
  obtain ⟨xs,hn,ha,hs⟩:=hc r (by omega)
  refine ⟨xs,hn,ha,?_⟩
  rw [←Nat.mod_mod_of_dvd _ hd,hs,Nat.mod_eq_of_lt hr]

/-- An intentionally coarse common multiple, so no lcm library is required. -/
def commonMultiple : Nat→Nat
  | 0 => 1
  | b+1 => (b+1)*commonMultiple b

theorem commonMultiple_pos (b) : 0<commonMultiple b := by
  induction b with
  | zero => decide
  | succ b ih => exact Nat.mul_pos (Nat.succ_pos _) ih

theorem dvd_commonMultiple {g b : Nat} (hg : 0<g) (hb : g≤b) : g∣commonMultiple b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases he : g=b+1
    · subst g; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih (by omega)) _

private theorem restricted_mono_budget {A k k'} (hr : RestrictedAtMost A k) (hm : k≤k') :
    RestrictedAtMost A k' := by
  obtain ⟨N,hN⟩:=hr
  refine ⟨N,?_⟩
  intro n hn
  obtain ⟨xs,hnd,hA,hs,hk⟩:=hN n hn
  exact ⟨xs,hnd,hA,hs,Nat.le_trans hk hm⟩

/-- Source corollary, with the missing analytic input isolated as a precise
hypothesis: from an eventual robust coset of bounded modulus obtain a *single*
universal modulus and a *uniform* finite restricted-order budget. -/
theorem uniformModulus_of_bounded_progression {A : Nat→Prop} {B K : Nat}
    (h : ∃ g, 0<g ∧ g≤B ∧ ∃ a N, RobustProgression A a g K N) :
    CompleteMod A (commonMultiple B) ↔ RestrictedAtMost A (K+B-1) := by
  obtain ⟨g,hg,hb,a,N,H⟩:=h
  constructor
  · intro hC
    exact restricted_mono_budget (robustProgression_lifts hg H
      (completeMod_dvd (commonMultiple_pos _) (dvd_commonMultiple hg hb) hC)) (by omega)
  · exact completeMod_of_restricted (commonMultiple_pos _)

/-- Removing the union of the finitely many "small" residue classes leaves only
residues that can be obtained while avoiding any list shorter than g. -/
private theorem avoid_small_classes (A : Nat→Prop) {g : Nat} (hg : 0<g) :
    ∃ D : List Nat, ∀ x, A x → x∉D → ∀ E : List Nat, E.length<g →
      ∃ y, A y ∧ y%g=x%g ∧ y∉E := by
  classical
  let Blocks (r : Nat) (E : List Nat) := ∀ y, A y → y%g=r → y∈E
  let Bad (r : Nat) := ∃ E : List Nat, E.length<g ∧ Blocks r E
  let witness (r : Nat) := if h : Bad r then Classical.choose h else []
  refine ⟨(List.range g).flatMap witness,?_⟩
  intro x hx hxD E hE
  apply Classical.byContradiction; intro habs
  have bad : Bad (x%g) := by
    refine ⟨E,hE,?_⟩; intro y hy hres
    exact Classical.byContradiction (fun hyE=>habs ⟨y,hy,hres,hyE⟩)
  have hw : x ∈ witness (x%g) := by
    dsimp [witness]; rw [dif_pos bad]
    exact (Classical.choose_spec bad).2 x hx rfl
  exact hxD (List.mem_flatMap.mpr ⟨x%g,List.mem_range.mpr (Nat.mod_lt _ hg),hw⟩)

private theorem liftResidues {A : Nat→Prop} {g : Nat} (xs : List Nat)
    (h : ∀ x∈xs, ∀ E : List Nat, E.length<g → ∃ y, A y ∧ y%g=x%g ∧ y∉E)
    (hlen : xs.length<g) : ∃ ys : List Nat, ys.Nodup ∧
      (∀ y∈ys, A y) ∧ ys.sum%g=xs.sum%g ∧ ys.length=xs.length := by
  induction xs with
  | nil => exact ⟨[],List.Pairwise.nil,by simp,rfl,rfl⟩
  | cons x xs ih =>
    have hle : xs.length<g := by simp only [List.length_cons] at hlen; omega
    obtain ⟨ys,hn,ha,hs,hl⟩:=ih (fun a hm=>h a (List.mem_cons_of_mem _ hm)) hle
    obtain ⟨z,hz,hzmod,hznot⟩:=h x (List.mem_cons_self) ys (hl ▸ hle)
    refine ⟨z::ys,List.nodup_cons.mpr ⟨hznot,hn⟩,?_,?_,by simpa using hl⟩
    · intro y hy; rcases List.mem_cons.mp hy with hh|hh
      · exact hh ▸ hz
      · exact ha y hh
    · simp only [List.sum_cons]; rw [Nat.add_mod, hzmod,hs, ←Nat.add_mod]

/-- **Unconditional** local part of the finite-deletion variant in #338. If
every finite deletion remains an ordinary basis (the order may vary), then the
finite subset sums cover every modulus. Only the local-to-global analytic
implication is missing for a proof of the full original variant. -/
theorem completeMod_of_finite_removal {A : Nat→Prop}
    (hrem : ∀ D : List Nat, ∃ h, Mixed.OrdinaryAtMost (fun x=>A x ∧ x∉D) h)
    {g : Nat} (hg : 0<g) : CompleteMod A g := by
  obtain ⟨D,hD⟩:=avoid_small_classes A hg
  obtain ⟨_,N,hN⟩:=hrem D
  intro r hrg
  let n := r+g*N
  have hn : N≤n := by
    have h := Nat.le_mul_of_pos_right N hg
    rw [Nat.mul_comm N g] at h; dsimp [n]; omega
  obtain ⟨xs,ha,hs,_⟩:=hN n hn
  obtain ⟨l,hl,hmod,hlen⟩:=shortResidue hg xs
  obtain ⟨ys,hnd,hA,heq,_⟩:=liftResidues l (fun x hx=>by
    obtain ⟨h₁,h₂⟩:=ha x (hl.subset hx)
    exact hD x h₁ h₂) hlen
  refine ⟨ys,hnd,hA,?_⟩
  rw [heq,hmod,hs]
  change (r+g*N)%g=r
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hrg]

theorem restricted_of_finite_removal_and_robust_class {A : Nat→Prop} {a g K N : Nat}
    (hrem : ∀ D : List Nat, ∃ h, Mixed.OrdinaryAtMost (fun x=>A x ∧ x∉D) h)
    (hg : 0<g) (hr : RobustProgression A a g K N) : RestrictedAtMost A (K+g-1) :=
  robustProgression_lifts hg hr (completeMod_of_finite_removal hrem hg)

end Erdos338.Growth
