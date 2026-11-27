import Erdos338.Growth

/-!
An elementary finite-cylinder proof of Chen–Yang–Zhao's uniform local
completeness theorem (Thm 3). No density or asymptotic-period theorem is
involved in this part. The notation uses actual lists of summands.
-/
namespace Erdos338.Existence
open Erdos338.Growth
def Ray (a g n : Nat) : Prop := ∃ t, n = a+g*t
def Thin (S : Nat → Prop) : Prop := ∀ a g, 0<g → ∃ b q, 0<q ∧
  (∀ n, Ray b q n → Ray a g n) ∧ (∀ n, Ray b q n → ¬S n)
def Shift (x : Nat) (S : Nat → Prop) (n : Nat) : Prop := ∃ s, S s ∧ n=x+s
def Ord (A : Nat → Prop) (h n : Nat) : Prop := ∃ xs : List Nat,
  (∀ x∈xs,A x) ∧ xs.sum=n ∧ xs.length≤h
def Approx (A : Nat→Prop) (h a g : Nat) : Prop :=
  ∀ q, 0<q → ∀ (E : List Nat) t, ∃ ys : List Nat,
      ys.Nodup ∧ (∀ y∈ys,A y) ∧ Avoid ys E ∧
      ys.length≤h ∧ ys.sum % q = (a+g*t)%q

private theorem thin_empty : Thin (fun _ => False) :=
 fun a g hg => ⟨a,g,hg,fun _ h=>h,fun _ _ => id⟩

private theorem thin_or {S T : Nat→Prop} (hs : Thin S) (ht : Thin T) :
    Thin (fun n => S n ∨ T n) := by
  intro a g hg
  obtain ⟨b,q,hq,sub,nots⟩ := hs a g hg
  obtain ⟨c,r,hr,sub',nott⟩ := ht b q hq
  exact ⟨c,r,hr,fun n hn=>sub n (sub' n hn),fun n hn h=>h.elim (nots n (sub' n hn)) (nott n hn)⟩

private theorem thin_shift {S : Nat→Prop} (hs : Thin S) (x : Nat) : Thin (Shift x S) := by
  intro a g hg
  -- First move the original ray far enough to subtract x.
  have hx : x≤g*x := by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right x hg
  let z := a+g*x-x
  have hz : x+z=a+g*x := by dsimp [z]; omega
  obtain ⟨b,q,hq,sub,no⟩ := hs z g hg
  refine ⟨x+b,q,hq,?_,?_⟩
  · rintro n ⟨t,rfl⟩
    obtain ⟨s,he⟩ := sub (b+q*t) ⟨t,rfl⟩
    refine ⟨x+s,?_⟩
    calc x+b+q*t = x+(b+q*t) := by omega
         _ = x+(z+g*s) := by rw [he]
         _ = a+g*(x+s) := by rw [Nat.mul_add]; omega
  · rintro n ⟨t,rfl⟩ ⟨s,hs,he⟩
    exact no s ⟨t,by omega⟩ hs

private theorem thin_list_shift {S : Nat→Prop} (hs : Thin S) (D : List Nat) :
    Thin (fun n => ∃ x∈D, Shift x S n) := by
  induction D with
  | nil => simpa using thin_empty
  | cons x D ih =>
    simpa only [List.mem_cons,exists_prop,or_and_right,exists_or,
      exists_eq_left] using thin_or (thin_shift hs x) ih

private theorem thin_zero {A : Nat→Prop} : Thin (Ord A 0) := by
  intro a g hg
  refine ⟨a+g,g,hg,?_,?_⟩
  · rintro n ⟨t,rfl⟩; exact ⟨t+1,by rw [Nat.mul_add,Nat.mul_one]; omega⟩
  · rintro n ⟨t,rfl⟩ ⟨xs,_,eq,len⟩
    have ez : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs; simp at eq; omega

/-- Remove every class modulo q which can be covered by a list of fewer
than B labels. All remaining classes provide a fresh member. -/
private theorem exc (A : Nat→Prop) {q B : Nat} (hq : 0<q) :
    ∃ D : List Nat, ∀ x, A x → x∉D → ∀ E : List Nat, E.length<B →
      ∃ y, A y ∧ y%q=x%q ∧ y∉E := by
  classical
  let Blocks (r : Nat) (E : List Nat) := ∀ y, A y → y%q=r → y∈E
  let bad (r : Nat) := ∃ E : List Nat, E.length<B ∧ Blocks r E
  let w (r : Nat) := if H : bad r then Classical.choose H else []
  refine ⟨(List.range q).flatMap w,?_⟩
  intro x hx hout E he
  apply Classical.byContradiction; intro nope
  have hx' : bad (x%q) := ⟨E,he,fun y hy hr =>
    Classical.byContradiction (fun hn => nope ⟨y,hy,hr,hn⟩)⟩
  have hin : x ∈ w (x%q) := by
    dsimp [w]; rw [dif_pos hx']; exact (Classical.choose_spec hx').2 x hx rfl
  exact hout (List.mem_flatMap.mpr ⟨x%q,List.mem_range.mpr (Nat.mod_lt _ hq),hin⟩)

private theorem replace {A : Nat→Prop} {q B : Nat} (E xs : List Nat)
    (h : ∀ x∈xs, ∀ F : List Nat, F.length<B → ∃ y, A y ∧ y%q=x%q ∧ y∉F)
    (len : E.length+xs.length<B) :
    ∃ ys : List Nat, ys.Nodup ∧ (∀ y∈ys, A y) ∧ Avoid ys E ∧
      ys.length=xs.length ∧ ys.sum%q=xs.sum%q := by
  induction xs with
  | nil => exact ⟨[],List.Pairwise.nil,by simp,by simp [Avoid],rfl,rfl⟩
  | cons x xs ih =>
    simp only [List.length_cons] at len
    obtain ⟨ys,hd,ha,avoid,hl,sm⟩ := ih (fun a hy=>h a (List.mem_cons_of_mem _ hy)) (by omega)
    obtain ⟨z,hza,zm,hz⟩ := h x List.mem_cons_self (ys++E) (by simp [hl]; omega)
    have hzY : z∉ys := fun h=>hz (List.mem_append_left _ h)
    have hzE : z∉E := fun h=>hz (List.mem_append_right _ h)
    refine ⟨z::ys,List.nodup_cons.mpr ⟨hzY,hd⟩,?_,?_,by simp [hl],?_⟩
    · intro y hy; rcases List.mem_cons.mp hy with hh|hh
      · exact hh ▸ hza
      · exact ha y hh
    · intro y hy; rcases List.mem_cons.mp hy with hh|hh
      · exact hh ▸ hzE
      · exact avoid y hh
    · simp only [List.sum_cons]; rw [Nat.add_mod,zm,sm,←Nat.add_mod]

private theorem splitLabel {A : Nat→Prop} {k x n : Nat} {xs : List Nat}
    (hm : x∈xs) (ha : ∀ y∈xs,A y) (sm : xs.sum=n) (le : xs.length≤k+1) :
    Shift x (Ord A k) n := by
  obtain ⟨l,r,eq⟩ := List.append_of_mem hm
  subst xs
  refine ⟨(l++r).sum, ⟨l++r,?_,rfl,?_⟩,?_⟩
  · intro y hy; apply ha y
    rcases List.mem_append.mp hy with hh|hh
    · exact List.mem_append_left _ hh
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hh)
  · simp only [List.length_append,List.length_cons] at le ⊢; omega
  · simp only [natSumAppend,List.sum_cons] at sm ⊢; omega

/-- Descend in the available number of slots when no cylinder is robustly
approximated: in some subray every permitted witness has a bounded label. -/
private theorem drop_slot {A : Nat→Prop} {h k : Nat} (le : k+1≤h)
    (bad : ∀ a g, 0<g → ¬Approx A h a g) (ih : Thin (Ord A k)) :
    Thin (Ord A (k+1)) := by
  classical
  intro a g hg
  have no := bad a g hg
  simp only [Approx,Classical.not_forall,Classical.not_imp] at no
  obtain ⟨q,hq,E,t,no⟩ := no
  obtain ⟨D,hD⟩ := exc A (B:=E.length+h+1) hq
  let v := a+g*t
  let p := g*q
  have hp : 0<p := Nat.mul_pos hg hq
  have sub : ∀n, Ray v p n → Ray a g n := by
    rintro n ⟨s,rfl⟩
    exact ⟨t+q*s,by simp [v,p,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]⟩
  obtain ⟨b,r,hr,sub',no'⟩ := thin_list_shift ih D v p hp
  refine ⟨b,r,hr,fun n h=>sub n (sub' n h),?_⟩
  rintro n hn ⟨xs,ha,sm,hl⟩
  obtain ⟨u,hu⟩ := sub' n hn
  by_cases hit : ∃ x∈xs, x∈D
  · obtain ⟨x,hx,hd⟩:=hit
    exact no' n hn ⟨x,hd,splitLabel hx ha sm hl⟩
  · obtain ⟨ys,hys,hey,hav,yl,sy⟩ := replace E xs
      (fun x hx => hD x (ha x hx) (fun m => hit ⟨x,hx,m⟩)) (by omega)
    apply no
    refine ⟨ys,hys,hey,hav,by omega,?_⟩
    rw [sy,sm,hu]
    change (v+(g*q)*u)%q=v%q
    rw [Nat.mul_right_comm, Nat.add_mul_mod_self_right]

/-- Any ordinary additive basis of order at most h has a profinite cylinder
represented robustly at that SAME rank. The cylinder is uniform in the
test modulus and in every finite set of labels to be avoided. -/
theorem robust_modular_cylinder {A : Nat→Prop} {h : Nat}
    (ord : Mixed.OrdinaryAtMost A h) :
    ∃ a g, 0<g ∧ Approx A h a g := by
  classical
  apply Classical.byContradiction; intro no
  have bad : ∀ a g, 0<g → ¬Approx A h a g := fun a g hg hh=> no ⟨a,g,hg,hh⟩
  have thin : ∀ k≤h, Thin (Ord A k) := by
    intro k
    induction k with
    | zero => intro _; exact thin_zero
    | succ k ih => intro le; exact drop_slot le bad (ih (by omega))
  obtain ⟨N,ho⟩:=ord
  obtain ⟨b,q,hq,_,avoid⟩:=thin h (Nat.le_refl _) 0 1 (by decide)
  have large : N≤b+q*N := by
    have hx : N≤q*N := by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right N hq
    omega
  exact avoid (b+q*N) ⟨N,rfl⟩ (ho _ large)


def UniformComplete (A : Nat→Prop) (H : Nat) : Prop :=
  ∀ q, 0<q → ∀ r<q, ∃ xs : List Nat, xs.Nodup ∧
    (∀ x∈xs,A x) ∧ xs.sum%q=r ∧ xs.length≤H

private theorem choose_translate {q a g s n : Nat} (hq : 0<q) (ha : a≤n)
    (modulo : s%g=(n-a)%g) :
    ∃ t, (s+(a+g*t))%q=n%q := by
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show q≠0 by omega)
  let u := s/g
  let v := (n-a)/g
  have h1 := Nat.mod_add_div s g
  have h2 := Nat.mod_add_div (n-a) g
  have identity : s+a+g*v=n+g*u := by dsimp [u,v]; omega
  refine ⟨v+j*u,?_⟩
  have eq : s + (a + g * (v + j*u)) = n+(g*u)*(j+1) := by
    calc s + (a + g * (v + j*u)) = (s+a+g*v)+(g*u)*j := by
           rw [Nat.mul_add,←Nat.mul_assoc, Nat.mul_right_comm g j u]; omega
         _ = (n+g*u)+(g*u)*j := by rw [identity]
         _ = n+(g*u)*(j+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
  rw [eq,Nat.add_mul_mod_self_right]

/-- Uniform local completeness, CYZ (2026), Thm 3, via the robust modular
cylinder and shortest finite subset-sum corrections. -/
theorem uniform_of_ordinary_and_local {A : Nat→Prop} {h : Nat}
    (ord : Mixed.OrdinaryAtMost A h) (localAll : ∀ q, 0<q → CompleteMod A q) :
    ∃ H, UniformComplete A H := by
  obtain ⟨a,g,hg,rr⟩ := robust_modular_cylinder ord
  refine ⟨h+g-1,?_⟩
  intro q hq x hx
  let n := x+q*a
  have ha : a≤n := by
    have hx' : a ≤ q*a := by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right a hq
    dsimp [n]; omega
  obtain ⟨xs,xnd,xmem,xmod⟩ := localAll g hg ((n-a)%g) (Nat.mod_lt _ hg)
  obtain ⟨E,sub,me,le⟩ := shortResidue hg xs
  have hE := xnd.sublist sub
  obtain ⟨t,ht⟩ := choose_translate (s:=E.sum) hq ha (me.trans xmod)
  obtain ⟨ys,hd,hy,avoid,len,hm⟩ := rr q hq E t
  refine ⟨E++ys,List.pairwise_append.mpr ⟨hE,hd,?_⟩,?_,?_,?_⟩
  · intro aa haa b hb eq; subst b; exact avoid aa hb haa
  · intro aa haa; rcases List.mem_append.mp haa with H|H
    · exact xmem aa (sub.subset H)
    · exact hy aa H
  · rw [natSumAppend,Nat.add_mod,hm,←Nat.add_mod,ht]
    dsimp [n]; rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx]
  · simp only [List.length_append]; omega

/-- CYZ Lemma 4 interface: the deletion budget b is fixed BEFORE the
progression modulus is produced, not required to dominate that modulus. -/
def RobustAt (A : Nat→Prop) (b a g K N : Nat) : Prop :=
  ∀ E : List Nat, E.Nodup → (∀ x∈E,A x) → E.length≤b →
    ∀ t≥N, t%g=a%g → ∃ xs : List Nat,
      xs.Nodup ∧ (∀ x∈xs,A x) ∧ Avoid xs E ∧ xs.sum=t ∧ xs.length≤K

private theorem finiteBound (P : Nat → Nat → Prop) (g : Nat)
    (h : ∀ r<g, ∃ e, P r e) : ∃ M, ∀r<g, ∃e≤M,P r e := by
  induction g with
  | zero => exact ⟨0, by simp⟩
  | succ g ih =>
    obtain ⟨C,hC⟩ := ih (fun r hr => h r (by omega))
    obtain ⟨e,he⟩ := h g (by omega)
    refine ⟨max C e,?_⟩
    intro r hr; by_cases hr' : r=g
    · subst r; exact ⟨e,Nat.le_max_right _ _,he⟩
    · obtain ⟨f,hf,pf⟩ := hC r (by omega)
      exact ⟨f, Nat.le_trans hf (Nat.le_max_left _ _),pf⟩

/-- Elementary gluing with general budget H and unrestricted modulus g. -/
theorem of_uniform_and_robust {A : Nat→Prop} {H a g K N : Nat} (hg : 0<g)
    (U : UniformComplete A H) (robust : RobustAt A H a g K N) :
    RestrictedAtMost A (H+K) := by
  let W (r e : Nat) := ∃ E : List Nat, E.Nodup ∧ (∀ x∈E,A x) ∧
    E.sum=e ∧ E.length≤H ∧ e%g=r
  have choices : ∀ r<g, ∃ e, W r e := by
    intro r hr; obtain ⟨E,nd,mem,modulo,len⟩:= U g hg r hr
    exact ⟨E.sum,E,nd,mem,rfl,len,modulo⟩
  obtain ⟨C,hC⟩ := finiteBound W g choices
  refine ⟨N+C+a,?_⟩
  intro n hn
  obtain ⟨e,he,E,hEn,hEA,hEs,hEl,hEm⟩ := hC ((n-a)%g) (Nat.mod_lt _ hg)
  have h1 := Nat.mod_add_div e g
  have h2 := Nat.mod_add_div (n-a) g
  have id : n-e+g*(e/g)=a+g*((n-a)/g) := by omega
  have hr : (n-e)%g=a%g := by
    simpa only [Nat.add_mul_mod_self_left] using congrArg (· % g) id
  obtain ⟨xs,nd,mem,avoid,sm,len⟩ := robust E hEn hEA hEl (n-e) (by omega) hr
  refine ⟨E++xs,List.pairwise_append.mpr ⟨hEn,nd,?_⟩,?_,?_,?_⟩
  · intro x hx y hy eq; subst y; exact avoid x hy hx
  · intro x hx; exact (List.mem_append.mp hx).elim (hEA x) (mem x)
  · rw [natSumAppend, hEs,sm]; omega
  · simp only [List.length_append]; omega

/-- The only unproved antecedent here is the analytic progression input.
Our uniform local completeness proof supplies the deletion budget; the
analytic result need not control g in terms of that budget. -/
theorem local_to_global_of_progressions {A : Nat→Prop} {h : Nat}
    (ord : Mixed.OrdinaryAtMost A h)
    (analytic : ∀ b, ∃ a g K N, 0<g ∧ RobustAt A b a g K N) :
    (∃ k, RestrictedAtMost A k) ↔ ∀ q, 0<q → CompleteMod A q := by
  constructor
  · rintro ⟨k,H⟩ q hq; exact completeMod_of_restricted hq H
  · intro localAll
    obtain ⟨H,U⟩ := uniform_of_ordinary_and_local ord localAll
    obtain ⟨a,g,K,N,hg,rob⟩ := analytic H
    exact ⟨H+K,of_uniform_and_robust hg U rob⟩

#print axioms robust_modular_cylinder
#print axioms uniform_of_ordinary_and_local
#print axioms of_uniform_and_robust
#print axioms local_to_global_of_progressions
end Erdos338.Existence
