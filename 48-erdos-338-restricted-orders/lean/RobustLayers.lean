import UniformLocal

/-!
Adaptive rank descent and deletion-robust lifting (Chen–Yang–Zhao, Lemma 4).
Counts are integer prefix counts, avoiding appeal to numerical limit estimates.
-/
namespace Erdos338.Existence.Analytic
open Erdos338.Growth
open Erdos338.Existence

/-- Count hits on [1,N]; zero is not counted. -/
noncomputable def hits (P : Nat→Prop) : Nat→Nat := by
  classical
  exact Nat.rec 0 (fun k c => c+(if P (k+1) then 1 else 0))
private theorem hits_zero (P : Nat→Prop) : hits P 0=0 := rfl
private theorem hits_succ (P : Nat→Prop) (n : Nat) :
    hits P (n+1) = hits P n + (by classical exact if P (n+1) then 1 else 0) := rfl
private theorem hits_mono (P : Nat→Prop) {m n : Nat} (h : m≤n) :
    hits P m ≤ hits P n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [hits_succ]; omega
private theorem hits_of_false {P : Nat→Prop} (h : ∀ n, 0<n → ¬P n) (n : Nat) :
    hits P n=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hits_succ,ih,h (n+1) (Nat.zero_lt_succ n)]

def R (A : Nat→Prop) (r n : Nat) : Prop := ∃ xs : List Nat, xs.Nodup ∧
  (∀ x∈xs,A x) ∧ xs.sum=n ∧ xs.length≤r

structure Layer where
  r : Nat
  Q : Nat

/-- Zero has arbitrarily many empty, mutually disjoint witnesses. -/
def Pack (A : Nat→Prop) (s : Layer) (n : Nat) : Prop :=
  ∃ w : List (List Nat), w.Pairwise Avoid ∧ s.Q≤w.length ∧
    ∀ xs∈w,xs.Nodup ∧ (∀ x∈xs, A x) ∧ xs.sum=n ∧ xs.length≤2*s.r

private theorem nil_replicate (Q : Nat) : (List.replicate Q ([]:List Nat)).Pairwise Avoid := by
  induction Q with
  | zero => exact List.Pairwise.nil
  | succ q ih =>
    rw [List.replicate_succ]
    exact List.pairwise_cons.mpr ⟨fun _ _ _ h=>False.elim (List.not_mem_nil h),ih⟩

theorem pack_zero (A : Nat→Prop) (s : Layer) : Pack A s 0 := by
  refine ⟨List.replicate s.Q [],nil_replicate _,by simp,?_⟩
  intro xs hx
  have h := (List.mem_replicate.mp hx).2
  subst xs; exact ⟨List.Pairwise.nil,by simp,rfl,by simp⟩

/-- Add one represented value from each set in the list, with no restriction
on re-use at this intermediate, ordinary-sumset stage. -/
def Fills (ss : List (Nat→Prop)) (n : Nat) : Prop := match ss with
  | [] => n=0
  | P::ps => ∃ x y, P x ∧ Fills ps y ∧ x+y=n

noncomputable def weight (ss : List (Nat→Prop)) (n : Nat) : Nat := (ss.map (fun P=>hits P n)).sum

/-- A weak consequence of mixed asymptotic Kneser: if the sum of prefix
counts eventually exceeds twice the window size, the mixed sumset of
sets containing zero contains a whole eventual residue class. Finite
summands are allowed here; dropping them changes the counts by O(1). -/
def MixedKneserRay : Prop := ∀ ss : List (Nat→Prop), (∀ P∈ss,P 0) →
  (∃ n0, ∀ n≥n0, 2*n≤weight ss n) →
  ∃ a g N, 0<g ∧ ∀ n≥N, n%g=a%g → Fills ss n

/-- The standard restricted-density theorem, in the only strength needed. -/
def HHPDensity : Prop := ∀ (A : Nat→Prop) h, Mixed.OrdinaryAtMost A h →
  ∃ d N, 0<d ∧ ∀ n≥N,n ≤ d*hits (R A h) n

/-- Finite incidence estimate, integrated over the target interval.
This is the aggregate consequence of the finite pair lemma, not a
positive-density or progression hypothesis. -/
def CollisionBound (A : Nat→Prop) : Prop := ∀ r Q N, 0<r → 0<Q →
 (hits (R A r) N) * (hits (R A r) N) ≤
   N*(hits (Pack A ⟨r,Q⟩) (2*N) + 9*r*Q*(1+hits (R A (r-1)) N))

private def L (d : Nat) := 8*d*d
private def Q (r d b : Nat) := b+L d*(2*r)+1
private def down (r d b : Nat) := 80*r*Q r d b*d*d

def plan : Nat → Nat → Nat → List Layer
  | 0, _, _ => []
  | k+1,d,b => List.replicate (L d) ⟨k+1,Q (k+1) d b⟩ ++
       plan k (down (k+1) d b) (b+L d*(2*(k+1)))

private def cutoff : Nat→Nat→Nat→Nat
  | 0,_,_ => 1
  | k+1,d,b => max 1 (max (down (k+1) d b)
        (cutoff k (down (k+1) d b) (b+L d*(2*(k+1)))))

private theorem cutoff_pos (k d b : Nat) : 0 < cutoff k d b := by
  cases k <;> simp only [cutoff] <;> omega

private theorem scalar (r Q d N M e D : Nat)
    (pos : 0<N) (hi : N≤d*M) (lo : 80*r*Q*d*d*e ≤ N+N)
    (inc : M*M ≤ N*(D+9*r*Q*e)) :
    6*N ≤ 8*d*d*D := by
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
  have h5 : 8*d*d*D=8*((d*d)*D) := by ac_rfl
  rw [h5]; omega

private theorem sum_rep (n a : Nat) : (List.replicate n a).sum=n*a := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ,List.sum_cons,ih,Nat.succ_mul]; omega

private theorem mass (A : Nat→Prop) (inc : CollisionBound A)
    (r d b n : Nat) (dpos : 0<d)
    (cut : cutoff r d b ≤ n) (hi : n≤ d*hits (R A r) n) :
    6*n ≤ weight ((plan r d b).map (Pack A)) (2*n) := by
  induction r generalizing d b with
  | zero =>
    have eh : hits (R A 0) n=0 := hits_of_false (fun m hm recStep => by
      obtain ⟨xs,_,_,sm,len⟩:= recStep
      have eq : xs=[] := List.length_eq_zero_iff.mp (by omega)
      subst xs; simp at sm; omega) n
    simp [eh] at hi
    simp [hi]
  | succ k ih =>
    let r:=k+1
    let qq:=Q r d b
    let dd:=down r d b
    let nb:=b+L d*(2*r)
    have hn : 0<n := Nat.lt_of_lt_of_le (cutoff_pos _ _ _) cut
    have hcut : dd≤n ∧ cutoff k dd nb ≤ n := by
      simpa only [cutoff,Nat.max_le,dd,nb,r] using (Nat.max_le.mp cut).2
    have hdd : 0<dd := by
      dsimp [dd,down,Q,r,L]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)) dpos) dpos
    have add : weight ((plan (k+1) d b).map (Pack A)) (2*n) =
        L d*hits (Pack A ⟨r,qq⟩) (2*n)+weight ((plan k dd nb).map (Pack A)) (2*n) := by
      simp [weight,plan,r,qq,dd,nb,List.map_replicate,natSumAppend,sum_rep]
    rw [add]
    by_cases next : n≤ dd*hits (R A k) n
    · exact Nat.le_trans (ih dd nb hdd hcut.2 next) (Nat.le_add_left _ _)
    · apply Nat.le_trans _ (Nat.le_add_right _ _)
      apply scalar r qq d n (hits (R A r) n) (1+hits (R A k) n) _ hn hi
      · have de : dd*(1+hits (R A k) n) ≤ n+n := by rw [Nat.mul_add,Nat.mul_one]; omega
        exact de
      · simpa [r] using inc r qq n (by dsimp [r]; omega) (by dsimp [qq,Q]; omega)

private theorem weight_mono (ss : List (Nat→Prop)) {m n : Nat} (hmn : m≤n) :
    weight ss m ≤ weight ss n := by
  induction ss with
  | nil => exact Nat.le_refl _
  | cons s ss ih => exact Nat.add_le_add (hits_mono s hmn) ih

theorem total_counts_eventual (A : Nat→Prop) (inc : CollisionBound A) (h d b n0 : Nat)
    (hd : 0<d) (den : ∀ n≥n0, n≤d*hits (R A h) n) :
    ∃ N, ∀ x≥N, 2*x≤weight ((plan h d b).map (Pack A)) x := by
  refine ⟨2*(max n0 (cutoff h d b)+1),?_⟩
  intro x hx
  let n:=x/2
  have hN : cutoff h d b≤n ∧ n0≤n ∧ 1≤n := by dsimp [n]; omega
  have hmass := mass A inc h d b n hd hN.1 (den n hN.2.1)
  have hh := weight_mono ((plan h d b).map (Pack A)) (m:=2*n) (n:=x) (by dsimp [n]; omega)
  dsimp [n] at *; omega

def Safe (b : Nat) : List Layer → Prop
  | [] => True
  | s::ss => b<s.Q ∧ Safe (b+2*s.r) ss

private theorem safe_repeat (b l : Nat) (s : Layer) (ss : List Layer)
    (budget : b+l*(2*s.r) < s.Q) (later : Safe (b+l*(2*s.r)) ss) :
    Safe b (List.replicate l s ++ ss) := by
  induction l generalizing b with
  | zero => simpa using later
  | succ i ih =>
    simp only [List.replicate_succ,List.cons_append,Safe]
    rw [Nat.succ_mul] at budget later
    constructor
    · omega
    · apply ih
      · omega
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later

theorem plan_safe (r d b : Nat) : Safe b (plan r d b) := by
  induction r generalizing d b with
  | zero => trivial
  | succ r ih =>
    change Safe b (List.replicate _ _ ++ _)
    apply safe_repeat
    · change b+L d*(2*(r+1)) < Q (r+1) d b
      simp [Q]
    · apply ih

private def ranks (ss : List Layer) := (ss.map (fun s=>2*s.r)).sum

/-- A member of the mixed sumset can be lifted using fresh summands
in the order of the precomputed layers. -/
theorem lift_form {A : Nat→Prop} {ss : List Layer} {b n : Nat}
    (safe : Safe b ss) (source : Fills (ss.map (Pack A)) n) (E : List Nat)
    (small : E.length≤b) : ∃ zs : List Nat, zs.Nodup ∧ (∀z∈zs,A z) ∧
      Avoid zs E ∧ zs.sum=n ∧ zs.length≤ranks ss := by
  induction ss generalizing b n E with
  | nil => exact ⟨[],List.Pairwise.nil,by simp,by simp [Avoid],source.symm,by simp [ranks]⟩
  | cons s ss ih =>
    obtain ⟨x,y,px,fy,sm⟩:=source
    obtain ⟨w,sp,len,pw⟩:=px
    obtain ⟨xs,hxs,avoid⟩:=survivor sp E (Nat.lt_of_le_of_lt small (Nat.lt_of_lt_of_le safe.1 len))
    obtain ⟨nd,mem,sx,lc⟩ := pw xs hxs
    obtain ⟨ys,dy,ay,avoidy,sy,ly⟩ := ih safe.2 fy (xs++E) (by simp; omega)
    refine ⟨xs++ys,List.pairwise_append.mpr ⟨nd,dy,?_⟩,?_,?_,?_,?_⟩
    · intro z hz z' hz' he; subst z'; exact avoidy z hz' (List.mem_append_left _ hz)
    · intro z hz; exact (List.mem_append.mp hz).elim (mem z) (ay z)
    · intro z hz he; rcases List.mem_append.mp hz with he'|he'
      · exact avoid z he' he
      · exact avoidy z he' (List.mem_append_right _ he)
    · rw [natSumAppend,sx,sy,sm]
    · change (xs++ys).length≤2*s.r+ranks ss
      rw [List.length_append]; omega

/-- CYZ Lemma 4 from a positive lower bound on the restricted prefix counts,
the finite double-counting estimates, and the stated weak Kneser input. -/
theorem robust_of_density {A : Nat→Prop} {h d n0 : Nat} (dpos : 0<d)
    (den : ∀ n≥n0, n≤d*hits (R A h) n)
    (inc : CollisionBound A) (mixRay : MixedKneserRay) (b : Nat) :
    ∃ a g K N, 0<g ∧ RobustAt A b a g K N := by
  let ss:=plan h d b
  have pos := total_counts_eventual A inc h d b n0 dpos den
  obtain ⟨a,g,N,hg,ray⟩ := mixRay (ss.map (Pack A)) (by
    intro P hp; obtain ⟨s,_,rfl⟩:=List.mem_map.mp hp; exact pack_zero _ _) pos
  refine ⟨a,g,ranks ss,N,hg,?_⟩
  intro E _ _ small t ht modEq
  exact lift_form (plan_safe _ _ _) (ray t ht modEq) E small

/-- Restricted-order existence iff local completeness. The literature's
HHP density theorem, a mixed Kneser consequence, and the displayed finite
collision inequality are EXPLICIT HYPOTHESES, not formalized axioms. -/
theorem headline_reduction {A : Nat→Prop} {h : Nat}
    (ord : Mixed.OrdinaryAtMost A h) (hhp : HHPDensity)
    (mixRay : MixedKneserRay) (inc : CollisionBound A) :
    (∃ k, RestrictedAtMost A k) ↔ ∀ q, 0<q → CompleteMod A q := by
  obtain ⟨d,n0,dp,den⟩ := hhp A h ord
  exact local_to_global_of_progressions ord (robust_of_density dp den inc mixRay)

#print axioms total_counts_eventual
#print axioms robust_of_density
#print axioms headline_reduction
end Erdos338.Existence.Analytic
