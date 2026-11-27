import Std

/-! # Lacunary obstructions for restricted bases
All sums have *at most* the indicated number of summands. Sets are predicates on
the natural numbers, and distinctness is imposed on actual positive summands. -/
namespace Erdos338.QAdic

def Skeleton (q n : Nat) : Prop := ∃ j t : Nat, n = q^j * (1 + q*t)
def Square (n : Nat) : Prop := ∃ a : Nat, 0 < a ∧ n = a*a

/-- Local version of being represented at restricted rank at most h. -/
def Hit (A : Nat → Prop) (h n : Nat) : Prop :=
  ∃ l : List Nat, l.length ≤ h ∧ l.Nodup ∧ (∀ x ∈ l, A x) ∧ l.sum = n

private theorem sum_mod (q : Nat) (l : List Nat) :
    l.sum % q = (l.map (fun x => x % q)).sum % q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    rw [Nat.add_mod a, ih]
    rw [Nat.add_mod (a % q)]
    simp

private theorem sum_res_le {q : Nat} {l : List Nat}
    (H : ∀ x ∈ l, x % q ≤ 1) :
    (l.map (fun x => x % q)).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := H a (by simp)
    have h' := ih (fun x h => H x (by simp [h]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem all_res_zero {q : Nat} {l : List Nat}
    (H : (l.map (fun x => x % q)).sum = 0) : ∀ x ∈ l, x % q = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons] at H
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · exact ih (by omega) x h

private theorem noTwo {A : Nat → Prop} {l : List Nat} (P : ∀ x, A x → 0 < x ∧ x ≠ 2)
    (H : ∀ x ∈ l, A x) (N : l.Nodup) : l.sum ≠ 2 := by
  cases l with
  | nil => decide
  | cons a l =>
    have ha := P a (H a (by simp))
    cases l with
    | nil => simpa using ha.2
    | cons b l =>
      have hb := P b (H b (by simp))
      have hab : a ≠ b := fun e => (List.nodup_cons.mp N).1 (by simp [e])
      simp only [List.sum_cons]
      omega

private theorem unscale {q : Nat} {A : Nat → Prop} {l : List Nat}
    (H : ∀ x ∈ l, ∃ y, A y ∧ x = q*y) :
    ∃ m : List Nat, (∀ y ∈ m, A y) ∧ l = m.map (fun y => q*y) := by
  induction l with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons a l ih =>
    obtain ⟨b,hb,e⟩ := H a (by simp)
    obtain ⟨m,hm,f⟩ := ih (fun y h => H y (by simp [h]))
    refine ⟨b::m, ?_, by simp [e,f]⟩
    intro y h
    rcases List.mem_cons.mp h with rfl | h
    · exact hb
    · exact hm _ h

private theorem nodup_of_nodup_map {l : List Nat} {f : Nat → Nat}
    (hn : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    exact List.nodup_cons.mpr ⟨fun h => hn.1 (List.mem_map.mpr ⟨_,h,rfl⟩), ih hn.2⟩

private theorem scale_sum (q : Nat) (m : List Nat) :
    (m.map (fun y => q*y)).sum = q*m.sum := by
  induction m with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]

private theorem descent {A : Nat → Prop} {q h : Nat} (hq : 0 < q)
    (P : ∀ x, A x → 0 < x ∧ x ≠ 2)
    (step : ∀ (k : Nat) (l : List Nat), l.length ≤ h → (∀ x ∈ l, A x) →
      l.sum = q * (2*q^k) → ∀ x ∈ l, ∃ y, A y ∧ x = q*y) :
    ∀ k, ¬Hit A h (2*q^k) := by
  intro k
  induction k with
  | zero =>
    rintro ⟨l,_,hn,H,hs⟩
    exact noTwo P H hn (by simpa using hs)
  | succ k ih =>
    rintro ⟨l,hl,hn,H,hs⟩
    have hs' : l.sum = q*(2*q^k) := by simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
    obtain ⟨m,hm,rfl⟩ := unscale (step k l hl H hs')
    exact ih ⟨m, by simpa using hl, nodup_of_nodup_map hn, hm,
      Nat.mul_left_cancel hq ((scale_sum q m).symm.trans hs')⟩

theorem skeleton_mod {q x : Nat} (hq : 1 < q) (hx : Skeleton q x) : x % q ≤ 1 := by
  obtain ⟨j,t,rfl⟩ := hx
  cases j with
  | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  | succ j => simp [Nat.pow_succ', Nat.mul_assoc]

private theorem skeleton_pos {q x : Nat} (hq : 0 < q) (hx : Skeleton q x) : 0 < x := by
  obtain ⟨j,t,rfl⟩ := hx
  exact Nat.mul_pos (Nat.pow_pos hq) (by omega)

private theorem skeleton_unscale {q x : Nat} (hq : 1 < q) (hx : Skeleton q x)
    (hr : x % q = 0) : ∃ y, Skeleton q y ∧ x = q*y := by
  obtain ⟨j,t,rfl⟩ := hx
  cases j with
  | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq] at hr
  | succ j => exact ⟨_,⟨j,t,rfl⟩,by rw [Nat.pow_succ', Nat.mul_assoc]⟩

/-- The obstruction works for every integer modulus q ≥ 3, prime or composite. -/
theorem skeleton_misses {q : Nat} (hq : 3 ≤ q) (k : Nat) :
    ¬Hit (Skeleton q) (q-1) (2*q^k) := by
  apply descent (by omega : 0 < q) _ _ k
  · intro x hx
    refine ⟨skeleton_pos (by omega) hx, ?_⟩
    intro e
    subst x
    have he := skeleton_mod (by omega : 1 < q) hx
    rw [Nat.mod_eq_of_lt (by omega)] at he
    omega
  · intro j l hl H hs x hx
    have H₁ := sum_res_le (fun y hy => skeleton_mod (by omega : 1 < q) (H y hy))
    have H₂ := sum_mod q l
    rw [hs, Nat.mul_mod_right, Nat.mod_eq_of_lt (by omega : (l.map (fun a => a % q)).sum < q)] at H₂
    exact skeleton_unscale (by omega) (H x hx) (all_res_zero H₂.symm x hx)


private theorem square_residues {x : Nat} (hx : Square x) :
    x%8 = 0 ∨ x%8 = 1 ∨ x%8 = 4 := by
  obtain ⟨a,_,rfl⟩ := hx
  rw [Nat.mul_mod]
  have h := Nat.mod_lt a (by decide : 0 < 8)
  have c : a%8=0 ∨ a%8=1 ∨ a%8=2 ∨ a%8=3 ∨ a%8=4 ∨ a%8=5 ∨ a%8=6 ∨ a%8=7 := by omega
  rcases c with c|c|c|c|c|c|c|c <;> simp [c]

private theorem square_unscale {x : Nat} (hx : Square x) (h : x%4=0) :
    ∃ y, Square y ∧ x = 4*y := by
  obtain ⟨a,ap,rfl⟩ := hx
  have he : a%2=0 := by
    have hh := Nat.mul_mod a a 2
    apply Classical.byContradiction
    intro h'
    have h'' : a%2=1 := by omega
    simp [h''] at hh
    omega
  have e : 2*(a/2) = a := by omega
  refine ⟨_,⟨a/2,by omega,rfl⟩,?_⟩
  calc
    a*a = (2*(a/2))*(2*(a/2)) := by rw [e]
    _ = (2*2)*((a/2)*(a/2)) := by ac_rfl
    _ = _ := rfl

private theorem all_res_one {q : Nat} {l : List Nat} (H : ∀ x ∈ l, x%q ≤ 1)
    (S : (l.map (fun x => x%q)).sum = l.length) : ∀ x ∈ l, x%q=1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := H a (by simp)
    have h' : ∀ x ∈ l, x%q ≤ 1 := fun x hx => H x (by simp [hx])
    have hs := sum_res_le h'
    simp only [List.map_cons, List.sum_cons, List.length_cons] at S
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact ih h' (by omega) x hx

private theorem sum_res_one {q : Nat} {l : List Nat} (H : ∀ x ∈ l, x%q=1) :
    (l.map (fun x => x%q)).sum = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [H a (by simp), ih (fun x hx => H x (by simp [hx])), Nat.add_comm]

/-- The original squares example: infinitely many exact targets have no
representation using at most four distinct positive squares. -/
theorem squares_miss_four (k : Nat) : ¬Hit Square 4 (2*4^k) := by
  apply descent (by decide : 0<4) _ _ k
  · intro x hx
    have r := square_residues hx
    obtain ⟨a,hp,rfl⟩ := hx
    exact ⟨Nat.mul_pos hp hp, by omega⟩
  · intro j l hl H hs x hx
    have R : ∀ a ∈ l, a%4 ≤ 1 := by
      intro a ha
      have ha' := square_residues (H a ha)
      omega
    have h1 := sum_res_le R
    have h2 := sum_mod 4 l
    have h8 : l.sum % 8 = 0 := by rw [hs]; omega
    have h3 : (l.map (fun a => a%4)).sum = 0 ∨
              (l.map (fun a => a%4)).sum = 4 := by omega
    apply square_unscale (H x hx)
    rcases h3 with h|h
    · exact all_res_zero h x hx
    · have hall := all_res_one R (by omega : (l.map (fun a => a%4)).sum = l.length)
      have h8' : ∀ a ∈ l, a%8=1 := by
        intro a ha
        have H1 := hall a ha
        have H8 := square_residues (H a ha)
        omega
      have h8'' := sum_res_one h8'
      have hh := sum_mod 8 l
      omega


def OrdinaryHit (A : Nat → Prop) (h n : Nat) : Prop :=
  ∃ l : List Nat, l.length ≤ h ∧ (∀ x ∈ l, A x) ∧ l.sum = n

def OrdinaryBasisAt (A : Nat → Prop) (h : Nat) : Prop :=
  ∃ N, ∀ n ≥ N, OrdinaryHit A h n

def RestrictedBasisAt (A : Nat → Prop) (h : Nat) : Prop :=
  ∃ N, ∀ n ≥ N, Hit A h n

private theorem skeleton_one (q : Nat) : Skeleton q 1 := ⟨0,0,by simp⟩
private theorem skeleton_scale {q x : Nat} (hx : Skeleton q x) : Skeleton q (q*x) := by
  obtain ⟨j,t,rfl⟩ := hx
  exact ⟨j+1,t,by rw [Nat.pow_succ',Nat.mul_assoc]⟩

private theorem sum_ones (n : Nat) : (List.replicate n 1 : List Nat).sum = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih,Nat.add_comm]

theorem skeleton_ordinary_all {q : Nat} (hq : 3 ≤ q) (n : Nat) :
    OrdinaryHit (Skeleton q) (q-1) n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n=0
    · subst n
      exact ⟨[],by simp,by simp,rfl⟩
    have h1 := Nat.mod_lt n (by omega : q>0)
    have h2 := Nat.div_add_mod n q
    by_cases H : n%q=0
    · obtain ⟨l,hl,H',hs⟩ := ih (n/q) (Nat.div_lt_self (by omega) (by omega))
      refine ⟨l.map (fun x=>q*x),by simpa using hl,?_,?_⟩
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
        exact skeleton_scale (H' a ha)
      · rw [scale_sum,hs]; omega
    · refine ⟨(1+q*(n/q)) :: List.replicate (n%q-1) 1,?_,?_,?_⟩
      · simp; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | h
        · exact ⟨0,n/q,by simp⟩
        · obtain ⟨_,rfl⟩ := List.mem_replicate.mp h
          exact skeleton_one q
      · rw [List.sum_cons,sum_ones]; omega

private theorem ordinary_lower {q h : Nat} (hq : 3 ≤ q) (hl : h < q-1) :
    ¬OrdinaryBasisAt (Skeleton q) h := by
  rintro ⟨N,H⟩
  have hN : N ≤ q*N := by simpa using Nat.mul_le_mul_right N (by omega : 1≤q)
  obtain ⟨l,hL,hm,hs⟩ := H (q*N+(q-1)) (by omega)
  have hr := sum_res_le (fun x hx => skeleton_mod (by omega : 1<q) (hm x hx))
  have H₁ := sum_mod q l
  rw [hs,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega : q-1<q),
      Nat.mod_eq_of_lt (by omega : (l.map (fun a => a%q)).sum<q)] at H₁
  omega

/-- If n=r+q*m and m is large, use exactly r distinct terms equal to 1 modulo q,
all larger than any prescribed cutoff t. No primality assumption is needed. -/
private theorem full_class {q : Nat} (hq : q>0) (r : Nat) (hr : 0<r) (t : Nat) :
    ∃ T, ∀ m ≥ T, ∃ l : List Nat, l.length = r ∧ l.Nodup ∧
      (∀ x ∈ l, t < x ∧ ∃ u, x=1+q*u) ∧ l.sum = r+q*m := by
  induction r generalizing t with
  | zero => omega
  | succ r ih =>
    by_cases hz : r=0
    · subst r
      refine ⟨t+1, fun m hm => ⟨[1+q*m],by simp,by simp,?_,by simp⟩⟩
      intro x hx
      obtain rfl : x=1+q*m := by simpa using hx
      have := Nat.mul_le_mul_right m (by omega : 1 ≤ q)
      simp at this
      exact ⟨by omega,m,rfl⟩
    · let a := 1+q*(t+1)
      obtain ⟨T,H⟩ := ih (by omega) a
      refine ⟨T+(t+1),?_⟩
      intro m hm
      obtain ⟨l,hl,hn,hm',hs⟩ := H (m-(t+1)) (by omega)
      refine ⟨a::l,by simp [hl],List.nodup_cons.mpr ⟨?_,hn⟩,?_,?_⟩
      · intro ha
        have := (hm' a ha).1
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | h
        · have := Nat.mul_le_mul_right (t+1) (by omega : 1≤q)
          simp at this
          exact ⟨by dsimp [a]; omega,t+1,rfl⟩
        · obtain ⟨ha,hu⟩ := hm' x h
          have := Nat.mul_le_mul_right (t+1) (by omega : 1≤q)
          simp at this
          exact ⟨by dsimp [a] at ha; omega,hu⟩
      · have eq : t+1+(m-(t+1))=m := by omega
        have eq' := congrArg (fun i => q*i) eq
        change q*(t+1+(m-(t+1))) = q*m at eq'
        rw [Nat.mul_add] at eq'
        simp [hs,a]; omega

private theorem finite_upper (P : Nat → Nat → Prop) (b : Nat)
    (H : ∀ i, 1≤i → i≤b → ∃ T, ∀ m≥T, P i m) :
    ∃ T, ∀ i, 1≤i → i≤b → ∀ m≥T, P i m := by
  induction b with
  | zero => exact ⟨0,by intros; omega⟩
  | succ b ih =>
    obtain ⟨T₁,h₁⟩ := ih (fun i hI hi => H i hI (by omega))
    obtain ⟨T₂,h₂⟩ := H (b+1) (by omega) (by omega)
    refine ⟨T₁+T₂,?_⟩
    intro i hp hb m hm
    by_cases h : i≤b
    · exact h₁ i hp h m (by omega)
    · obtain rfl : i=b+1 := by omega
      exact h₂ m (by omega)

/-- Even a tail of the class 1 modulo q suffices for the restricted upper bound q. -/
theorem progression_restricted {q : Nat} (hq : 0 < q) (t : Nat) :
    RestrictedBasisAt (fun x => x>t ∧ ∃ u, x=1+q*u) q := by
  let P := fun r m => Hit (fun x=>x>t ∧ ∃ u, x=1+q*u) q (r+q*m)
  have H : ∀ i, 1≤i → i≤q → ∃ T, ∀ m≥T, P i m := by
    intro i h1 h2
    obtain ⟨T,h⟩ := full_class hq i h1 t
    refine ⟨T,?_⟩
    intro m hm
    obtain ⟨l,hl,hn,ha,hs⟩ := h m hm
    exact ⟨l,by omega,hn,ha,hs⟩
  obtain ⟨T,H'⟩ := finite_upper P q H
  refine ⟨q*T+1,?_⟩
  intro n hn
  let m := (n-1)/q
  let r := (n-1)%q+1
  have hr := Nat.mod_lt (n-1) hq
  have hm : T≤m := (Nat.le_div_iff_mul_le hq).mpr (by rw [Nat.mul_comm]; omega)
  have he := Nat.div_add_mod (n-1) q
  have e : n = r+q*m := by dsimp [r,m]; omega
  rw [e]
  exact H' r (by dsimp [r]; omega) (by dsimp [r]; omega) m hm

private theorem pow_large {q : Nat} (hq : 2≤q) (k : Nat) : k+1 ≤ q^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul_left (q^k) hq
    omega

theorem skeleton_orders {q : Nat} (hq : 3 ≤ q) :
    OrdinaryBasisAt (Skeleton q) (q-1) ∧ (∀ h, h<q-1 → ¬OrdinaryBasisAt (Skeleton q) h) ∧
    RestrictedBasisAt (Skeleton q) q ∧ (∀ h, h<q → ¬RestrictedBasisAt (Skeleton q) h) := by
  refine ⟨⟨0, fun n _ => skeleton_ordinary_all hq n⟩,fun _ h => ordinary_lower hq h,?_,?_⟩
  · obtain ⟨T,H⟩ := progression_restricted (by omega : q>0) 0
    refine ⟨T,?_⟩
    intro n hn
    obtain ⟨l,hl,hd,ha,hs⟩ := H n hn
    refine ⟨l,hl,hd,?_,hs⟩
    intro x hx
    obtain ⟨u,hu⟩ := (ha x hx).2
    exact ⟨0,u,by simpa using hu⟩
  · intro h hh
    rintro ⟨N,H⟩
    have hp := pow_large (by omega : 2≤q) N
    obtain ⟨l,hl,hn,ha,hs⟩ := H (2*q^N) (by omega)
    exact skeleton_misses hq N ⟨l,by omega,hn,ha,hs⟩


private theorem map_nodup_mul {l : List Nat} {q : Nat} (hq : q>0) (hn : l.Nodup) :
    (l.map (fun y=>q*y)).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hl⟩
    rintro H
    obtain ⟨y,hy,e⟩ := List.mem_map.mp H
    exact ha ((Nat.mul_left_cancel hq e) ▸ hy)

private theorem hit_mono {A B : Nat → Prop} {h n : Nat}
    (H : ∀ x, A x → B x) (hN : Hit A h n) : Hit B h n := by
  obtain ⟨l,hl,hn,ha,hs⟩ := hN
  exact ⟨l,hl,hn,fun x hx=>H x (ha x hx),hs⟩

private theorem mult_ge (q t : Nat) (hq : 0<q) : t ≤ q*t := by
  simpa using Nat.mul_le_mul_right t hq

private theorem lift_hit {t n h q : Nat} (hq : q>0)
    (H : Hit (fun x=> t<x ∧ Skeleton q x) h n) :
    Hit (fun x=> t<x ∧ Skeleton q x) h (q*n) := by
  obtain ⟨l,hl,hn,ha,hs⟩ := H
  refine ⟨l.map (fun x=>q*x),by simpa using hl,map_nodup_mul hq hn,?_,by rw [scale_sum,hs]⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  exact ⟨Nat.lt_of_lt_of_le (ha x hx).1 (mult_ge q x hq),skeleton_scale (ha x hx).2⟩

private theorem tail_low_digit {q : Nat} (hq : 3≤q) (t : Nat) :
    ∃ N, ∀ n≥N, n%q≠0 → Hit (fun x=>t<x ∧ Skeleton q x) (q-1) n := by
  let P := fun r m => Hit (fun x=>t<x ∧ Skeleton q x) (q-1) (r+q*m)
  have H : ∀ i, 1≤i → i≤q-1 → ∃ T, ∀ m≥T, P i m := by
    intro i h1 h2
    obtain ⟨T,h⟩ := full_class (by omega : q>0) i h1 t
    refine ⟨T,?_⟩
    intro m hm
    obtain ⟨l,hl,hn,ha,hs⟩ := h m hm
    refine ⟨l,by omega,hn,?_,hs⟩
    intro x hx
    obtain ⟨ht,u,hu⟩ := ha x hx
    exact ⟨ht,0,u,by simpa using hu⟩
  obtain ⟨T,H'⟩ := finite_upper P (q-1) H
  refine ⟨q*T,?_⟩
  intro n hn hne
  have hr := Nat.mod_lt n (by omega : 0<q)
  have hm : T≤n/q := (Nat.le_div_iff_mul_le (by omega : 0<q)).mpr (by rwa [Nat.mul_comm])
  have he := Nat.mod_add_div n q
  exact he ▸ H' (n%q) (by omega) (by omega) (n/q) hm

private theorem tail_below {q : Nat} (hq : 3≤q) (K t : Nat) :
    ∃ N, ∀ n≥N, ¬q^K∣n → Hit (fun x=>t<x ∧ Skeleton q x) (q-1) n := by
  induction K with
  | zero => exact ⟨0,by simp⟩
  | succ K ih =>
    obtain ⟨N,IH⟩ := ih
    obtain ⟨T,H⟩ := tail_low_digit hq t
    refine ⟨q*N + T,?_⟩
    intro n hn hD
    by_cases h : n%q=0
    · let m := n/q
      have e : n = q*m := by
        have := Nat.div_add_mod n q
        dsimp [m]; omega
      have h' : ¬q^K∣m := by
        rintro ⟨z,hz⟩
        exact hD ⟨z,by rw [e,hz,Nat.pow_succ',Nat.mul_assoc]⟩
      have hm : m≥N := (Nat.le_div_iff_mul_le (by omega : 0<q)).mpr (by rw [Nat.mul_comm]; omega)
      rw [e]
      exact lift_hit (by omega) (IH m hm h')
    · exact H n (by omega) h

private theorem digit_form {q : Nat} (hq : 3≤q) (b : Nat) (hb : b>0) :
    ∃ v r u, 0<r ∧ r<q ∧ b=q^v*(r+q*u) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases h : b%q=0
    · obtain ⟨v,r,u,hr,hq',e⟩ := ih (b/q)
          (Nat.div_lt_self hb (by omega)) (by
            have H := Nat.div_add_mod b q
            apply Nat.pos_of_ne_zero
            intro hz
            rw [hz,h] at H
            simp at H
            omega)
      refine ⟨v+1,r,u,hr,hq',?_⟩
      have he := Nat.div_add_mod b q
      rw [Nat.pow_succ',Nat.mul_assoc,←e]
      omega
    · exact ⟨0,b%q,b/q,by omega,Nat.mod_lt b (by omega),by simp [Nat.mod_add_div]⟩

/-- Extend any sufficiently long skeleton tail by a single positive outsider.
No restriction is placed on any *other* inserted elements. -/
theorem outsider_suffices {q : Nat} (hq : 3≤q) {A : Nat → Prop} {t b : Nat}
    (contains : ∀ x, t<x → Skeleton q x → A x) (ab : A b)
    (pos : 0<b) (outside : ¬Skeleton q b) : RestrictedBasisAt A (q-1) := by
  obtain ⟨v,r,u,hr,hr',eb⟩ := digit_form hq b pos
  have hr2 : 2≤r := by
    by_cases h : r=1
    · exact False.elim (outside ⟨v,u,by simpa [h] using eb⟩)
    · omega
  obtain ⟨T,H⟩ := full_class (by omega : q>0) (q-r) (by omega) (t+b)
  obtain ⟨N,L⟩ := tail_below hq (v+1) t
  refine ⟨N + q^(v+1)*(T+u+1),?_⟩
  intro n hn
  by_cases D : q^(v+1)∣n
  · obtain ⟨w,ew⟩ := D
    have hp := Nat.pow_pos (n:=v) (by omega : 0<q)
    have hp' := Nat.pow_pos (n:=v+1) (by omega : 0<q)
    have hw : T+u+1≤w := Nat.le_of_mul_le_mul_left
      (by rw [←ew]; omega : q^(v+1)*(T+u+1) ≤ q^(v+1)*w) hp'
    obtain ⟨l,hl,hd,ha,hs⟩ := H (w-u-1) (by omega)
    let m := l.map (fun x=>q^v*x)
    have memb : ∀ y ∈ m, y>b ∧ A y := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      obtain ⟨hxb,d,ed⟩ := ha x hx
      have hh := mult_ge (q^v) x hp
      exact ⟨by omega, contains _ (by omega) ⟨v,d,by rw [ed]⟩⟩
    refine ⟨b::m, ?_, List.nodup_cons.mpr ⟨?_,map_nodup_mul hp hd⟩, ?_, ?_⟩
    · simp [m,hl]; omega
    · intro h; have := (memb b h).1; omega
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact ab
      · exact (memb _ h).2
    · have id : u+(w-u-1)+1=w := by omega
      have id' : q*u+q*(w-u-1)+q=q*w := by
        rw [←Nat.mul_add,←Nat.mul_succ]
        exact congrArg (fun z=>q*z) id
      have id'' : (r+q*u)+((q-r)+q*(w-u-1))=q*w := by omega
      simp only [List.sum_cons,m,scale_sum,hs]
      rw [eb,←Nat.mul_add,id'',ew,Nat.pow_succ,Nat.mul_assoc]
  · exact hit_mono (fun x (hx : t<x ∧ Skeleton q x)=>contains x hx.1 hx.2)
      (L n (by omega) D)

/-- An inclusion-maximal failure of restricted rank q−1 in every rank q−1 ≥ 2:
for a positive set containing a tail of B_q, an element outside B_q is both
necessary and sufficient for restricted rank at most q−1. -/
theorem maximal_obstruction {q : Nat} (hq : 3≤q) {A : Nat → Prop} {t : Nat}
    (positive : ∀ x, A x → 0<x) (contains : ∀ x, t<x → Skeleton q x → A x) :
    RestrictedBasisAt A (q-1) ↔ ∃ b, A b ∧ ¬Skeleton q b := by
  constructor
  · intro H
    apply Classical.byContradiction
    intro Hnone
    have sub : ∀ x, A x → Skeleton q x := by
      intro x hx
      apply Classical.byContradiction
      intro hs
      exact Hnone ⟨x,hx,hs⟩
    obtain ⟨N,hN⟩ := H
    have pow := pow_large (by omega : 2≤q) N
    exact skeleton_misses hq N (hit_mono sub (hN (2*q^N) (by omega)))
  · rintro ⟨b,hb,hs⟩
    exact outsider_suffices hq contains hb (positive b hb) hs


theorem squares_not_restricted_four : ¬RestrictedBasisAt Square 4 := by
  rintro ⟨N,H⟩
  have hp := pow_large (by decide : 2≤4) N
  exact squares_miss_four N (H _ (by omega))

private theorem skeleton_pow_scale {q x : Nat} (hx : Skeleton q x) (k : Nat) :
    Skeleton q (q^k*x) := by
  obtain ⟨v,t,rfl⟩ := hx
  exact ⟨k+v,t,by rw [Nat.pow_add,Nat.mul_assoc]⟩

private theorem tail_ordinary {q : Nat} (hq : 3≤q) (t : Nat) :
    OrdinaryBasisAt (fun x=> t<x ∧ Skeleton q x) (q-1) := by
  obtain ⟨N,H⟩ := tail_below hq (t+1) t
  refine ⟨N,?_⟩
  intro n hn
  by_cases D : q^(t+1) ∣ n
  · obtain ⟨w,ew⟩ := D
    obtain ⟨l,hl,ha,hs⟩ := skeleton_ordinary_all hq w
    have hp := pow_large (by omega : 2≤q) (t+1)
    refine ⟨l.map (fun x =>q^(t+1)*x),by simpa using hl,?_,?_⟩
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      have h := ha x hx
      have hp' := skeleton_pos (by omega) h
      have hh := mult_ge x (q^(t+1)) hp'
      rw [Nat.mul_comm x] at hh
      exact ⟨by omega,skeleton_pow_scale h (t+1)⟩
    · rw [scale_sum,hs,←ew]
  · obtain ⟨l,hl,_,ha,hs⟩ := H n hn D
    exact ⟨l,hl,ha,hs⟩

/-- Arbitrary finite deletion from the skeleton preserves BOTH exact orders. -/
theorem tail_orders {q : Nat} (hq : 3 ≤ q) {A : Nat → Prop} {t : Nat}
    (contains : ∀ x, t<x → Skeleton q x → A x) (sub : ∀ x, A x → Skeleton q x) :
    OrdinaryBasisAt A (q-1) ∧ (∀ h, h<q-1 → ¬OrdinaryBasisAt A h) ∧
    RestrictedBasisAt A q ∧ (∀ h, h<q → ¬RestrictedBasisAt A h) := by
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨N,H⟩ := tail_ordinary hq t
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨l,hl,ha,hs⟩ := H n hn
    exact ⟨l,hl,fun x hx=>contains x (ha x hx).1 (ha x hx).2,hs⟩
  · rintro h hh ⟨N,H⟩
    apply ordinary_lower hq hh
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨l,hl,ha,hs⟩ := H n hn
    exact ⟨l,hl,fun x hx=>sub x (ha x hx),hs⟩
  · obtain ⟨N,H⟩ := progression_restricted (by omega : q>0) t
    refine ⟨N,?_⟩
    intro n hn
    refine hit_mono (A:=fun x => x>t ∧ ∃ u, x=1+q*u) (B:=A) ?_ (H n hn)
    rintro x ⟨hx,u,e⟩
    exact contains _ hx ⟨0,u,by simpa using e⟩
  · rintro h hh ⟨N,H⟩
    exact (skeleton_orders hq).2.2.2 _ hh ⟨N,fun n hn => hit_mono sub (H n hn)⟩

end Erdos338.QAdic
