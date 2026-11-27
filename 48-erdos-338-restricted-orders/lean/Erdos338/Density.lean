import Std

/-!
# Finite quotient part of the density criteria for Erdős #338
Theorems here isolate the analytic input: the common modulus must eventually
fill every class that the restricted sumset meets, *including* classes hit by
small witnesses. Ordinary eventual periodicity alone is insufficient.
Neither a density inequality nor Kneser's or Roth's theorem is an axiom here.
-/
namespace Erdos338.Density

/-- At least `k` distinct actual members of `A` occur in residue `u`. -/
def Has (A : Nat → Prop) (q u k : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧ xs.length = k ∧ ∀ x ∈ xs, A x ∧ x % q = u

theorem has_zero (A : Nat → Prop) (q u : Nat) : Has A q u 0 :=
  ⟨[], by simp, rfl, by simp⟩

theorem Has.down {A q u k j} (H : Has A q u k) (hle : j ≤ k) : Has A q u j := by
  obtain ⟨xs, hn, hl, hm⟩ := H
  exact ⟨xs.take j, hn.take, by simp [List.length_take, hl, Nat.min_eq_left hle],
    fun x hx => hm x (List.mem_of_mem_take hx)⟩

/-- `cap ... h` is min(h, class size) even for an infinite or undecidable A.
This is a mathematical invariant, not an algorithm for an arbitrary oracle. -/
noncomputable def cap (A : Nat → Prop) (q u : Nat) : Nat → Nat
  | 0 => 0
  | h+1 => @ite Nat (Has A q u (h+1)) (Classical.propDecidable _) (h+1) (cap A q u h)

theorem le_cap_iff {A q u k h} :
    k ≤ cap A q u h ↔ k ≤ h ∧ Has A q u k := by
  classical
  induction h with
  | zero =>
    simp only [cap, Nat.le_zero_eq]
    exact ⟨fun hk => ⟨hk, hk ▸ has_zero A q u⟩, And.left⟩
  | succ h ih =>
    by_cases HH : Has A q u (h+1)
    · simp only [cap, if_pos HH]
      exact ⟨fun hk => ⟨hk, HH.down hk⟩, And.left⟩
    · simp only [cap, if_neg HH, ih]
      constructor
      · exact fun ⟨hle, hf⟩ => ⟨by omega, hf⟩
      · intro ⟨hle, hf⟩
        have hk : k ≠ h+1 := fun e => HH (e ▸ hf)
        exact ⟨by omega, hf⟩

/-- We store the bounded multiplicity vector sparsely by a recurrence over the
residues. Its indices are its total number of summands and its *integer*
weighted sum before reduction modulo q. -/
def Vector (capacity : Nat → Nat) : Nat → Nat → Nat → Prop
  | 0, len, w => len = 0 ∧ w = 0
  | r+1, len, w => ∃ k l s, k ≤ capacity r ∧ Vector capacity r l s ∧
      len = l + k ∧ w = s + k * r

def weight (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => f x + weight f xs

private theorem weight_append (f : Nat → Nat) (xs ys : List Nat) :
    weight f (xs ++ ys) = weight f xs + weight f ys := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih => simp [weight, ih, Nat.add_assoc]

private theorem weight_const {f : Nat → Nat} {v : Nat} (xs : List Nat)
    (hv : ∀ x ∈ xs, f x = v) : weight f xs = xs.length * v := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih =>
    have htl := ih (fun y hy => hv y (by simp [hy]))
    simp [weight, hv x (by simp), htl, Nat.succ_mul, Nat.add_comm]

private theorem split_weight (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) :
    weight f xs = weight f (xs.filter p) + weight f (xs.filter (fun x => !(p x))) := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih =>
    cases hp : p x <;> simp [weight, List.filter_cons, hp, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem split_length (p : Nat → Bool) (xs : List Nat) :
    xs.length = (xs.filter p).length + (xs.filter (fun x => !(p x))).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [List.filter_cons, hp, ih, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]

/-- Exact support criterion before reduction: bounded residue populations are
the *only* information required to lift residue multiplicities to distinct labels. -/
theorem vector_iff {A : Nat → Prop} {q h r l w : Nat} (hl : l ≤ h) :
    Vector (fun u => cap A q u h) r l w ↔
    ∃ xs : List Nat, xs.Nodup ∧ xs.length = l ∧ weight (· % q) xs = w ∧
        ∀ x ∈ xs, A x ∧ x % q < r := by
  induction r generalizing l w with
  | zero =>
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨[], by simp, rfl, rfl, by simp⟩
    · rintro ⟨xs,_,hx,hw,H⟩
      cases xs with
      | nil => exact ⟨hx.symm, hw.symm⟩
      | cons x xs => exact (Nat.not_lt_zero _ (H x (by simp)).2).elim
  | succ r ih =>
    constructor
    · rintro ⟨k,l',s,hk,vec,el,ew⟩
      obtain ⟨ys, hy, eyl, eyw, hys⟩ := (ih (by omega)).mp vec
      obtain ⟨zs, hz, ezl, hzs⟩ := (le_cap_iff.mp hk).2
      refine ⟨ys ++ zs, List.pairwise_append.mpr ⟨hy, hz, ?_⟩, ?_, ?_, ?_⟩
      · rintro a ha b hb rfl
        have h1 := (hys a ha).2
        have h2 := (hzs a hb).2
        omega
      · simp [eyl, ezl, el]
      · rw [weight_append, eyw, weight_const zs (fun x hx => (hzs x hx).2), ezl, ew]
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact ⟨(hys x h1).1, by have := (hys x h1).2; omega⟩
        · exact ⟨(hzs x h2).1, by have := (hzs x h2).2; omega⟩
    · rintro ⟨xs, hn, ell, eww, H⟩
      let p := fun x : Nat => decide (x % q < r)
      let ys := xs.filter p
      let zs := xs.filter (fun x => !(p x))
      have hsplit : l = ys.length + zs.length := ell ▸ split_length p xs
      have hy : ∀ x ∈ ys, A x ∧ x % q < r := by
        intro x hx
        obtain ⟨mx, hp⟩ := List.mem_filter.mp hx
        exact ⟨(H x mx).1, of_decide_eq_true hp⟩
      have hz : ∀ x ∈ zs, A x ∧ x % q = r := by
        intro x hx
        obtain ⟨mx, hp⟩ := List.mem_filter.mp hx
        have hlt := (H x mx).2
        have hge : ¬ x % q < r := by simpa [p] using hp
        exact ⟨(H x mx).1, by omega⟩
      refine ⟨zs.length, ys.length, weight (· % q) ys,
        le_cap_iff.mpr ⟨by omega, ⟨zs, hn.filter _, rfl, hz⟩⟩,
        (ih (by omega)).mpr ⟨ys, hn.filter _, rfl, rfl, hy⟩, hsplit, ?_⟩
      calc w = weight (· % q) xs := eww.symm
           _ = weight (· % q) ys + weight (· % q) zs := split_weight _ p xs
           _ = _ := by rw [weight_const zs fun x hx => (hz x hx).2]

def Represents (A : Nat → Prop) (h n : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧ xs.length ≤ h ∧ (∀ x ∈ xs, A x) ∧ weight id xs = n

def CappedTest (A : Nat → Prop) (h q u : Nat) : Prop :=
  ∃ l w, l ≤ h ∧ Vector (fun r => cap A q r h) q l w ∧ w % q = u

private theorem weight_mod (q : Nat) (xs : List Nat) :
    weight (· % q) xs % q = weight id xs % q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [weight, id_eq]
    rw [Nat.mod_add_mod, Nat.add_mod x, ih, ← Nat.add_mod]

theorem cappedTest_iff_hit {A h q u} (hq : 0 < q) :
    CappedTest A h q u ↔ ∃ n, Represents A h n ∧ n % q = u := by
  constructor
  · rintro ⟨l,w,hl,H,hw⟩
    obtain ⟨xs, hn, ell, ew, hxs⟩ := (vector_iff hl).mp H
    exact ⟨weight id xs, ⟨xs, hn, by omega, fun x hx => (hxs x hx).1, rfl⟩,
      by rw [← weight_mod, ew, hw]⟩
  · rintro ⟨n, ⟨xs, hn, hl, H, ew⟩, en⟩
    exact ⟨xs.length, weight (· % q) xs, hl,
      (vector_iff hl).mpr ⟨xs,hn,rfl,rfl,fun x hx => ⟨H x hx, Nat.mod_lt _ hq⟩⟩,
      by rw [weight_mod, ew, en]⟩

/-- A residue witnessed once is filled eventually (one common cutoff). This
strong, rather than ordinary, eventual periodicity is the analytic input. -/
def FillsOccupied (S : Nat → Prop) (q : Nat) : Prop :=
  ∃ N, ∀ n ≥ N, (∃ a, S a ∧ a % q = n % q) → S n

def CofinalCoverage (S : Nat → Prop) : Prop := ∃ N, ∀ n ≥ N, S n

theorem cofinal_iff_capped {A h q} (hq : 0 < q) (H : FillsOccupied (Represents A h) q) :
    CofinalCoverage (Represents A h) ↔ ∀ u < q, CappedTest A h q u := by
  constructor
  · rintro ⟨N,hN⟩ u hu
    have hle : N ≤ u + N*q := by have := Nat.mul_le_mul_left N hq; omega
    exact (cappedTest_iff_hit hq).mpr ⟨u+N*q, hN _ hle, by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]⟩
  · intro hc
    obtain ⟨N,hN⟩ := H
    exact ⟨N,fun n hn => hN n hn ((cappedTest_iff_hit hq).mp (hc _ (Nat.mod_lt _ hq)))⟩


/-- The Kneser argument produces a modulus that can depend on the witness.
If each such modulus divides a common positive q, the finitely many occupied
classes have one common cutoff.  No isolated witnesses may be discarded. -/
theorem fills_of_local_divisors {S : Nat → Prop} {q : Nat} (hq : 0 < q)
    (H : ∀ a, S a → ∃ d, d ∣ q ∧ ∃ N, ∀ n ≥ N, n % d = a % d → S n) :
    FillsOccupied S q := by
  classical
  have single : ∀ u, ∃ N, ∀ n ≥ N, n % q = u →
      (∃ a, S a ∧ a % q = u) → S n := by
    intro u
    by_cases h : ∃ a, S a ∧ a % q = u
    · obtain ⟨a,ha,au⟩ := h
      obtain ⟨d,hd,N,T⟩ := H a ha
      refine ⟨N, fun n hn en _ => T n hn ?_⟩
      calc n % d = n % q % d := (Nat.mod_mod_of_dvd n hd).symm
           _ = a % q % d := by rw [en, au]
           _ = a % d := Nat.mod_mod_of_dvd a hd
    · exact ⟨0, fun _ _ _ he => (h he).elim⟩
  have finitely : ∀ r, ∃ N, ∀ u < r, ∀ n ≥ N, n % q = u →
      (∃ a, S a ∧ a % q = u) → S n := by
    intro r
    induction r with
    | zero => exact ⟨0, fun _ hu => (Nat.not_lt_zero _ hu).elim⟩
    | succ r ih =>
      obtain ⟨N,hN⟩ := ih
      obtain ⟨K,hK⟩ := single r
      refine ⟨max N K, fun u hu n hn => ?_⟩
      by_cases eq : u = r
      · exact eq ▸ hK n (Nat.le_trans (Nat.le_max_right _ _) hn)
      · exact hN u (by omega) n (Nat.le_trans (Nat.le_max_left _ _) hn)
  obtain ⟨N, hN⟩ := finitely q
  exact ⟨N, fun n hn => hN (n % q) (Nat.mod_lt n hq) n hn rfl⟩

def Ordinary (A : Nat → Prop) (h n : Nat) : Prop :=
  ∃ xs : List Nat, xs.length ≤ h ∧ (∀ x ∈ xs, A x) ∧ weight id xs = n

theorem restricted_to_ordinary {A h n} : Represents A h n → Ordinary A h n :=
  fun ⟨xs,_,rest⟩ => ⟨xs,rest⟩

def IsOrder (R : Nat → Nat → Prop) (h : Nat) : Prop :=
  CofinalCoverage (R h) ∧ ∀ k < h, ¬ CofinalCoverage (R k)

theorem equalOrder_iff_capped {A h q} (ho : IsOrder (Ordinary A) h)
    (hq : 0 < q) (H : FillsOccupied (Represents A h) q) :
    IsOrder (Represents A) h ↔ ∀ u < q, CappedTest A h q u := by
  constructor
  · intro ⟨hr,_⟩; exact (cofinal_iff_capped hq H).mp hr
  · refine fun test => ⟨(cofinal_iff_capped hq H).mpr test,?_⟩
    rintro k hkh ⟨N,hN⟩
    exact ho.2 k hkh ⟨N,fun n hn => restricted_to_ordinary (hN n hn)⟩

/-! ## A completely proved sharp endpoint: natural density 1/3, orders (3,4).
The concrete set is the positive integers in residue classes 0 and 1 modulo
6, together with the element 2. The ordinary representations of 6t+5 may
use 2 twice; distinct representations at rank 3 cannot. -/

def Endpoint (n : Nat) : Prop := 0 < n ∧ (n % 6 ≤ 1 ∨ n = 2)

private theorem ord_endpoint_upper : CofinalCoverage (Ordinary Endpoint 3) := by
  refine ⟨30, fun n hn => ?_⟩
  by_cases h01 : n % 6 ≤ 1
  · exact ⟨[n], by simp, by simpa [Endpoint] using And.intro hn (Or.inl h01 : n%6≤1 ∨ n=2) |>.imp (fun h => by omega) id, by simp [weight]⟩
  · by_cases h23 : n % 6 ≤ 3
    · refine ⟨[2,n-2], by simp, ?_, by simp [weight]; omega⟩
      simp [Endpoint]; omega
    · refine ⟨[2,2,n-4], by simp, ?_, by simp [weight]; omega⟩
      simp [Endpoint]; omega

private theorem res_endpoint_upper : CofinalCoverage (Represents Endpoint 4) := by
  refine ⟨30, fun n hn => ?_⟩
  by_cases h01 : n % 6 ≤ 1
  · exact ⟨[n], by simp, by simp, by simpa [Endpoint] using And.intro (by omega : 0<n) (Or.inl h01 : n%6≤1 ∨ n=2), by simp [weight]⟩
  · by_cases h23 : n % 6 ≤ 3
    · refine ⟨[2,n-2], ?_, by simp, ?_, by simp [weight]; omega⟩
      · simp; omega
      · simp [Endpoint]; omega
    · refine ⟨[2,1,7,n-10], ?_, by simp, ?_, by simp [weight]; omega⟩
      · simp; omega
      · simp [Endpoint]; omega

private theorem endpoint_modwt (xs : List Nat) (A : ∀ x ∈ xs, Endpoint x) :
    weight (· % 6) xs ≤ 2*xs.length := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih =>
    have ha := (A x (by simp)).2
    have hb := ih (fun y hy => A y (by simp [hy]))
    simp only [weight, List.length_cons]
    omega

private theorem endpoint_distinct_modwt (xs : List Nat) (hn : xs.Nodup)
    (A : ∀ x ∈ xs, Endpoint x) :
    weight (· % 6) xs ≤ xs.length + (if 2 ∈ xs then 1 else 0) := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.nodup_cons.mp hn
    have ha := (A x (by simp)).2
    have hb := ih ht (fun y hy => A y (by simp [hy]))
    by_cases h : x=2
    · subst x
      simp [weight, hx] at hb ⊢
      omega
    · simp [weight, Ne.symm h, h]
      omega

private theorem mode5_no_low_ordinary (n : Nat) (e : n % 6 = 5) {k : Nat} (hk : k < 3) :
    ¬ Ordinary Endpoint k n := by
  rintro ⟨xs,l,A,wt⟩
  have h := endpoint_modwt xs A
  have eh : weight (· %6) xs % 6 = 5 := (weight_mod 6 xs).trans (wt ▸ e)
  omega

private theorem mode5_no_low_distinct (n : Nat) (e : n % 6 = 5) {k : Nat} (hk : k < 4) :
    ¬ Represents Endpoint k n := by
  rintro ⟨xs,nd,l,A,wt⟩
  have h := endpoint_distinct_modwt xs nd A
  have eh : weight (· %6) xs % 6 = 5 := (weight_mod 6 xs).trans (wt ▸ e)
  split at h <;> omega

/-- An unconditional endpoint counterexample to extending the one-third result
to density equal to one third. -/
theorem endpoint_orders : IsOrder (Ordinary Endpoint) 3 ∧ IsOrder (Represents Endpoint) 4 := by
  constructor
  · refine ⟨ord_endpoint_upper,?_⟩
    rintro k hk ⟨N,hN⟩
    exact mode5_no_low_ordinary (5+N*6) (by omega) hk (hN _ (by omega))
  · refine ⟨res_endpoint_upper,?_⟩
    rintro k hk ⟨N,hN⟩
    exact mode5_no_low_distinct (5+N*6) (by omega) hk (hN _ (by omega))

/-- Counting function for the half-open interval [0,N). -/
def endpointCount : Nat → Nat
  | 0 => 0
  | n+1 => endpointCount n + (if 0<n ∧ (n%6≤1 ∨ n=2) then 1 else 0)

theorem endpoint_count_exact {N : Nat} (h : 3 ≤ N) :
    endpointCount N = 2*(N/6) + min (N%6) 2 := by
  obtain ⟨n,rfl⟩ : ∃ n, N = n+3 := ⟨N-3, by omega⟩
  induction n with
  | zero => decide
  | succ n ih =>
    have IH := ih (by omega)
    change endpointCount (n+3+1) = _
    rw [endpointCount, IH]
    split <;> omega

/-- Uniform bounded discrepancy, in particular natural density exactly 1/3. -/
theorem endpoint_density_discrepancy {N : Nat} (h : 3 ≤ N) :
    N ≤ 3 * endpointCount N + 4 ∧ 3 * endpointCount N ≤ N + 4 := by
  rw [endpoint_count_exact h]; omega


/-! ## Unconditional positive class: ultimately periodic input sets
Here the finite criterion applies *without* any Kneser, Roth, or sumset
periodicity input. It handles arbitrary finite insertions/deletions; an
arbitrary low-rank modular hit consisting only of exceptional elements is
not enough. At least one slot must come from a full tail residue.
-/

def PeriodicTail (A : Nat → Prop) (q : Nat) (T : Nat → Prop) : Prop :=
  ∃ K, ∀ x ≥ K, A x ↔ T (x % q)

/-- Reserve one slot from an infinite tail class, and use ordinary capped
populations for the remaining distinct slots. All tests are finite once the
residue mask and the q capped multiplicities are supplied. -/
def TailTest (A : Nat → Prop) (h q : Nat) (T : Nat → Prop) (u : Nat) : Prop :=
  ∃ t l w, t < q ∧ T t ∧ l+1 ≤ h ∧
    Vector (fun r => cap A q r h) q l w ∧ (t+w)%q = u

private theorem addModCancel {a b z q : Nat} (hq : 0 < q)
    (H : (a+z)%q=(b+z)%q) : a%q = b%q := by
  let c := q-z%q
  have hlt := Nat.mod_lt z hq
  have hzero : (z+c)%q=0 := by
    rw [← Nat.mod_add_mod z q c]
    have hc : z%q + c = q := by dsimp [c]; omega
    rw [hc, Nat.mod_self]
  have rev (x : Nat) : ((x+z)%q+c)%q = x%q := by
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_mod x, hzero]
    simp
  exact (rev a).symm.trans ((congrArg (fun y => (y+c)%q) H).trans (rev b))

private theorem term_le_weight {ys : List Nat} {a : Nat} (ha : a ∈ ys) :
    a ≤ weight id ys := by
  induction ys with
  | nil => simp at ha
  | cons b ys ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · simp [weight]
    · have := ih ht; simp only [weight,id_eq]; omega

private theorem weight_le_multiple {ys : List Nat} {K : Nat}
    (H : ∀ x ∈ ys, x ≤ K) : weight id ys ≤ ys.length*K := by
  induction ys with
  | nil => simp [weight]
  | cons x xs ih =>
    have xt := H x (by simp)
    have tl := ih (fun y hy => H y (by simp [hy]))
    simp only [weight, id_eq, List.length_cons, Nat.succ_mul]; omega

private theorem weight_perm {xs ys : List Nat} (p : xs.Perm ys) (f : Nat → Nat) :
    weight f xs = weight f ys := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [weight, ih]
  | swap => simp [weight, Nat.add_left_comm]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- This class has eventual coverage iff its anchored finite test succeeds.
The reverse direction only needs *one* sufficiently large represented
member of this class, by the proof. -/
theorem tailClass_iff_test {A h q T u} (hq : 0 < q) (hu : u < q) (H : PeriodicTail A q T) :
    (∃ N, ∀ n ≥ N, n % q = u → Represents A h n) ↔ TailTest A h q T u := by
  classical
  obtain ⟨K,hK⟩ := H
  constructor
  · rintro ⟨N,hN⟩
    let Z := 1 + h*K + N
    let n := u + Z*q
    have hle : Z ≤ Z*q := by simpa using Nat.mul_le_mul_left Z hq
    have nN : N ≤ n := by dsimp [n,Z] at *; omega
    have nBig : h*K < n := by dsimp [n,Z] at *; omega
    have nu : n%q=u := by simp [n,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hu]
    obtain ⟨xs, hn, hl, ham, hw⟩ := hN n nN nu
    have big : ∃ x ∈ xs, K ≤ x := by
      apply Classical.byContradiction; intro hf
      have hz : ∀ y ∈ xs, y ≤ K := by
        intro y hy
        have : ¬ K ≤ y := fun hky => hf ⟨y,hy,hky⟩
        omega
      have := weight_le_multiple hz
      have := Nat.mul_le_mul_right K hl
      omega
    obtain ⟨x,hx,hkx⟩ := big
    let ys := xs.erase x
    have hp : xs.Perm (x :: ys) := List.perm_cons_erase hx
    have hlen := hp.length_eq
    simp only [List.length_cons] at hlen
    have yw := weight_perm hp (·%q)
    simp only [weight] at yw
    refine ⟨x%q,ys.length,weight (·%q) ys, Nat.mod_lt _ hq, (hK x hkx).mp (ham x hx),
      by omega, (vector_iff (by omega)).mpr ⟨ys,List.erase_sublist.nodup hn,rfl,rfl,?_⟩,?_⟩
    · exact fun y hy => ⟨ham y (List.mem_of_mem_erase hy), Nat.mod_lt _ hq⟩
    · rw [← yw, weight_mod, hw, nu]
  · rintro ⟨t,l,w,ht,tT,hl,hv,huv⟩
    obtain ⟨ys,hy,ell,ew,hys⟩ := (vector_iff (by omega)).mp hv
    let s := weight id ys
    have ews : w%q = s%q := ew ▸ weight_mod q ys
    refine ⟨K+2*s+1,?_⟩
    intro n hn en
    let x := n-s
    have xeq : x+s=n := by dsimp [x]; omega
    have ex : x%q=t := by
      rw [← Nat.mod_eq_of_lt ht]
      apply addModCancel (z:=s) hq
      rw [xeq,en,← huv]
      simp only [Nat.add_mod t s,Nat.add_mod t w, ews]
    have fresh : x ∉ ys := by
      intro hm
      have Hx : x ≤ s := term_le_weight hm
      omega
    refine ⟨x :: ys, List.nodup_cons.mpr ⟨fresh,hy⟩, by simp [ell]; omega,?_,xeq⟩
    intro y hym
    rcases List.mem_cons.mp hym with rfl | ht'
    · exact (hK _ (by omega)).mpr (ex ▸ tT)
    · exact (hys y ht').1

/-- Complete all-ranks finite test for *every* eventually periodic ordinary
basis, including arbitrary finite edits. This is a subclass, not all #338. -/
theorem periodicTail_equalOrder_iff {A h q T} (hq : 0 < q) (H : PeriodicTail A q T)
    (ho : IsOrder (Ordinary A) h) :
    IsOrder (Represents A) h ↔ ∀ u < q, TailTest A h q T u := by
  constructor
  · rintro ⟨⟨N,hN⟩,_⟩ u hu
    exact (tailClass_iff_test hq hu H).mp ⟨N,fun n hn _ => hN n hn⟩
  · intro ht
    have fin : ∀ r, r ≤ q → ∃ N, ∀ n ≥ N, n%q < r → Represents A h n := by
      intro r
      induction r with
      | zero => exact fun _ => ⟨0,fun _ _ hu => (Nat.not_lt_zero _ hu).elim⟩
      | succ r ih =>
        intro hr
        obtain ⟨N,hN⟩ := ih (by omega)
        obtain ⟨K,hK⟩ := (tailClass_iff_test hq (by omega : r<q) H).mpr (ht r (by omega))
        refine ⟨max N K,fun n hn hrn => ?_⟩
        by_cases he : n%q=r
        · exact hK _ (Nat.le_trans (Nat.le_max_right _ _) hn) he
        · exact hN _ (Nat.le_trans (Nat.le_max_left _ _) hn) (by omega)
    obtain ⟨N,hN⟩ := fin q (Nat.le_refl _)
    refine ⟨⟨N, fun n hn => hN _ hn (Nat.mod_lt _ hq)⟩,?_⟩
    rintro k hk ⟨K,hK⟩
    exact ho.2 k hk ⟨K,fun n hn => restricted_to_ordinary (hK n hn)⟩


/-! ## Executable residue test on a supplied finite population table -/

/-- Enumerate all (length, weighted sum) pairs attainable through `r`
residues. Multiplicities in the input must be capped at the rank. -/
def states (C : Nat → Nat) : Nat → List (Nat × Nat)
  | 0 => [(0,0)]
  | r+1 => (states C r).flatMap (fun p => (List.range (C r + 1)).map
      (fun k => (p.1+k,p.2+k*r)))

theorem mem_states {C : Nat → Nat} {r l w : Nat} :
    (l,w) ∈ states C r ↔ Vector C r l w := by
  induction r generalizing l w with
  | zero => simp [states,Vector,Prod.ext_iff]
  | succ r ih =>
    simp only [states,List.mem_flatMap,List.mem_map,List.mem_range,Vector]
    constructor
    · rintro ⟨⟨m,s⟩,he,k,hk,eh⟩
      exact ⟨k,m,s,by omega,ih.mp he, (congrArg Prod.fst eh).symm, (congrArg Prod.snd eh).symm⟩
    · rintro ⟨k,m,s,hk,prev,rfl,rfl⟩
      exact ⟨(m,s),ih.mpr prev,k,by omega,rfl⟩

/-- `true` iff an anchored tuple achieves this residue. Uses only the
input finite-period tail mask and supplied finite capped class populations. -/
def tailDecision (h q : Nat) (T : Nat → Bool) (C : Nat → Nat) (u : Nat) : Bool :=
  (List.range q).any (fun t => T t && (states C q).any
    (fun p => decide (p.1+1≤h ∧ (t+p.2)%q=u)))

theorem tailDecision_correct {A h q T} (mask : Nat → Bool) (C : Nat → Nat)
    (hmask : ∀ t < q, mask t = true ↔ T t) (hcap : ∀ t < q, C t = cap A q t h) (u) :
    tailDecision h q mask C u = true ↔ TailTest A h q T u := by
  have vectors : ∀ r, r ≤ q → ∀ l w, Vector C r l w ↔ Vector (fun t => cap A q t h) r l w := by
    intro r; induction r with
    | zero => exact fun _ _ _ => Iff.rfl
    | succ r ih =>
      intro hr l w
      simp only [Vector,hcap r (by omega),ih (by omega)]
  simp only [tailDecision, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨t,ht,hm,⟨l,w⟩,hw,hl,ew⟩
    exact ⟨t,l,w,ht,(hmask t ht).mp hm,hl,(vectors q (Nat.le_refl _) l w).mp (mem_states.mp hw),ew⟩
  · rintro ⟨t,l,w,ht,hm,hl,hv,ew⟩
    exact ⟨t,ht,(hmask t ht).mpr hm,(l,w),mem_states.mpr ((vectors q (Nat.le_refl _) l w).mpr hv),hl,ew⟩

/-- The endpoint's finite decision problem: modulo 6 the tail mask is 0,1;
there is only one extra element in residue 2. -/
example : (List.range 6).map (tailDecision 3 6 (fun t => decide (t≤1))
    (fun t => if t≤1 then 3 else if t=2 then 1 else 0)) =
    [true,true,true,true,true,false] := by decide

example : (List.range 6).all (tailDecision 4 6 (fun t => decide (t≤1))
    (fun t => if t≤1 then 4 else if t=2 then 1 else 0)) = true := by decide


/-! ## Another threshold example, with *infinite* restricted order
For all q≥3, adjoining a single 1 to the positive multiples of q creates
an ordinary asymptotic basis of exact order q but no restricted basis at all.
For q=3 this is a natural-density-one-third example independent of the
preceding example with finite restricted order four. -/

def OneException (q n : Nat) : Prop := (n % q = 0 ∧ 0 < n) ∨ n=1

private theorem oe_weight {q} (hq : 3 ≤ q) {xs : List Nat}
    (ha : ∀ x ∈ xs, OneException q x) : weight (· % q) xs = xs.count 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have H := ih (fun y hy => ha y (by simp [hy]))
    simp only [weight,H,List.count_cons]
    rcases ha x (by simp) with ⟨hmod,_⟩ | rfl
    · have h1 : x≠1 := by
        rintro rfl
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      simp [hmod,h1]
    · simp [Nat.mod_eq_of_lt (by omega : 1<q), Nat.add_comm]

private theorem count_one_le {xs : List Nat} (hn : xs.Nodup) : xs.count 1 ≤ 1 := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    obtain ⟨h,hn⟩ := List.nodup_cons.mp hn
    specialize ih hn
    by_cases e : a=1
    · subst a; simp [List.count_cons,List.count_eq_zero.mpr h]
    · simp [List.count_cons, e, ih]

theorem oneException_orders {q : Nat} (hq : 3 ≤ q) :
    IsOrder (Ordinary (OneException q)) q ∧
    ∀ h, ¬ CofinalCoverage (Represents (OneException q) h) := by
  have qp : 0<q := by omega
  have q1 : 1%q=1 := Nat.mod_eq_of_lt (by omega)
  constructor
  · constructor
    · refine ⟨q,fun n hn => ?_⟩
      let r := n%q
      let b := q * (n/q)
      have showEq : b+r=n := Nat.div_add_mod n q
      have rlt : r < q := Nat.mod_lt n qp
      have bq : b%q=0 := Nat.mod_eq_zero_of_dvd ⟨n/q,rfl⟩
      let ys := List.replicate r 1
      have yw : weight id ys = r := by
        rw [weight_const (f:=id) ys (v:=1) (fun _ h => (List.mem_replicate.mp h).2)]
        simp [ys]
      refine ⟨b :: ys, by simp [ys]; omega, ?_, by simp [weight,yw,showEq]⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hm
      · exact Or.inl ⟨bq, by omega⟩
      · exact Or.inr (List.mem_replicate.mp hm).2
    · rintro k hk ⟨N,hN⟩
      let Z := N+q+1
      let n := q-1 + Z*q
      have hL : Z ≤ Z*q := by simpa using Nat.mul_le_mul_left Z qp
      have nN : N ≤ n := by dsimp [n,Z] at *; omega
      have nBig : q<n := by dsimp [n,Z] at *; omega
      have en : n%q=q-1 := by simp [n,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (by omega : q-1<q)]
      obtain ⟨xs,hl,ha,hw⟩ := hN n nN
      have hc : xs.count 1 ≤ xs.length := List.count_le_length
      have em := weight_mod q xs
      rw [oe_weight hq ha, Nat.mod_eq_of_lt (by omega), hw, en] at em
      have el : xs.count 1=xs.length := by omega
      have wt := weight_const xs (f:=id) (v:=1) (fun x hx => (List.count_eq_length.mp el x hx).symm)
      simp only [Nat.mul_one] at wt
      omega
  · rintro h ⟨N,hN⟩
    have hL : N ≤ N*q := by simpa using Nat.mul_le_mul_left N qp
    obtain ⟨xs,hd,_,ha,hw⟩ := hN (2+N*q) (by omega)
    have em := weight_mod q xs
    have ec := count_one_le hd
    rw [oe_weight hq ha, Nat.mod_eq_of_lt (by omega), hw, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega : 2<q)] at em
    omega

end Erdos338.Density
