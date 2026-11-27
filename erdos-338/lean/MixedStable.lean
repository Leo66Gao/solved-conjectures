import MixedDyson
import CoinBox
import Erdos335.DysonProgressions
import Mathlib.Tactic

open scoped Pointwise BigOperators
open Filter Topology Erdos335 Erdos338.MixedDyson
namespace Erdos338.MixedStable
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure St (ι : Type*) where
  A : Set ℕ
  B : ι → Set ℕ
  act : Finset ι

def St.Valid (s : St ι) : Prop :=
  0 ∈ s.A ∧ (∀ i, 0 ∈ s.B i) ∧ ∀ i, i ∉ s.act → s.B i = {0}

def St.move (s : St ι) (i : ι) (e : ℕ) : St ι :=
  ⟨dysonLeft s.A (s.B i) e, Function.update s.B i (dysonRight s.A (s.B i) e), s.act⟩

def St.drop (s : St ι) (i : ι) : St ι :=
  ⟨s.A, Function.update s.B i {0}, s.act.erase i⟩

inductive Reach (R : ℕ) (a : St ι) : St ι → Prop
  | refl : Reach R a a
  | step {s : St ι} (hp : Reach R a s) (i : ι) (e : ℕ) (hi : i ∈ s.act) (he : e ∈ s.A) :
    Reach R a (s.move i e)
  | drop {s : St ι} (hp : Reach R a s) (i : ι) (hi : i ∈ s.act) (hg : Separated (s.B i) R) :
    Reach R a (s.drop i)

theorem Reach.trans {R : ℕ} {a b c : St ι} (h₁ : Reach R a b) (h₂ : Reach R b c) :
    Reach R a c := by
  induction h₂ with
  | refl => exact h₁
  | step _ i e hi he ih => exact ih.step i e hi he
  | drop _ i hi hg ih => exact ih.drop i hi hg

theorem Reach.active_subset {R : ℕ} {a b : St ι} (h : Reach R a b) : b.act ⊆ a.act := by
  induction h with
  | refl => exact Finset.Subset.rfl
  | step _ i e hi he ih => exact ih
  | drop _ i hi hg ih => exact (Finset.erase_subset _ _).trans ih

private theorem move_valid {s : St ι} {i : ι} {e : ℕ}
    (hs : s.Valid) (hi : i ∈ s.act) (he : e ∈ s.A) : (s.move i e).Valid := by
  refine ⟨zero_mem_dysonLeft hs.1, ?_, ?_⟩
  · intro j
    by_cases hj : j=i
    · subst j; simpa [St.move] using zero_mem_dysonRight he (hs.2.1 i)
    · simpa [St.move, Function.update_of_ne hj] using hs.2.1 j
  · intro j h
    have hj : j≠i := fun eq => h (eq ▸ hi)
    simpa [St.move, Function.update_of_ne hj] using hs.2.2 j h

private theorem drop_valid {s : St ι} {i : ι} (hs : s.Valid) : (s.drop i).Valid := by
  refine ⟨hs.1, ?_, ?_⟩
  · intro j
    by_cases hj : j=i
    · subst j; simp [St.drop]
    · simpa [St.drop, Function.update_of_ne hj] using hs.2.1 j
  · intro j hj
    by_cases he : j=i
    · subst j; simp [St.drop]
    · have hn : j ∉ s.act := fun h => hj (Finset.mem_erase.mpr ⟨he,h⟩)
      simpa [St.drop, Function.update_of_ne he] using hs.2.2 j hn

theorem Reach.valid {R : ℕ} {a b : St ι} (h : Reach R a b) (ha : a.Valid) : b.Valid := by
  induction h with
  | refl => exact ha
  | step _ i e hi he ih => exact move_valid ih hi he
  | drop _ i hi hg ih => exact drop_valid ih

theorem Reach.left_subset {R : ℕ} {a b : St ι} (h : Reach R a b) : a.A ⊆ b.A := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step _ i e hi he ih => exact ih.trans (subset_dysonLeft _ _ _)
  | drop _ i hi hg ih => exact ih

theorem Reach.right_subset {R : ℕ} {a b : St ι} (h : Reach R a b) (ha : a.Valid) (j : ι) :
    b.B j ⊆ a.B j := by
  induction h with
  | refl => exact Set.Subset.rfl
  | @step s h i e hi he ih =>
    apply Set.Subset.trans _ ih
    by_cases hj : j=i
    · subst j; simpa [St.move] using dysonRight_subset s.A (s.B i) e
    · simp [St.move, Function.update_of_ne hj]
  | @drop s h i hi hg ih =>
    apply Set.Subset.trans _ ih
    by_cases hj : j=i
    · subst j
      intro x hx
      have he : x=0 := by simpa [St.drop] using hx
      simpa [he] using (h.valid ha).2.1 i
    · simp [St.drop, Function.update_of_ne hj]

theorem Reach.sum_subset {R : ℕ} {a b : St ι} (h : Reach R a b) (ha : a.Valid) :
    mixed b.A b.B ⊆ mixed a.A a.B := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step _ i e hi he ih => exact (mixed_update_subset _ _ i e).trans ih
  | @drop s h i hi hg ih =>
    intro n hn
    obtain ⟨a,ha',b,hb,hn⟩ := hn
    apply ih
    refine ⟨a,ha',b,?_,hn⟩
    intro j
    by_cases hj : j=i
    · subst j
      have he : b i=0 := by simpa [St.drop] using hb i
      simpa [he] using (h.valid ha).2.1 i
    · simpa [St.drop, Function.update_of_ne hj] using hb j

private theorem mass_drop {s : St ι} (i : ι) (N : ℕ) :
    mass s.A s.B N = mass (s.drop i).A (s.drop i).B N + count (s.B i) N := by
  classical
  have hz : count ({0} : Set ℕ) N = 0 := by
    unfold count
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hr,hn0⟩ := (@Finset.mem_filter ℕ (fun a => a ∈ ({0}: Set ℕ)) (fun _ => Classical.propDecidable _) _ _).mp hn
    have h1 := (Finset.mem_Icc.mp hr).1
    have h0 : n = 0 := by simpa using hn0
    omega
  have hcomp (j : ι) (hj : j ∈ Finset.univ.erase i) :
      count ((s.drop i).B j) N = count (s.B j) N := by
    simp [St.drop,Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have heq := Finset.sum_congr rfl hcomp
  have hz' : count ((s.drop i).B i) N = 0 := by simpa [St.drop] using hz
  unfold mass
  rw [← Finset.sum_erase_add Finset.univ (fun j => count (s.B j) N) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (fun j => count ((s.drop i).B j) N) (Finset.mem_univ i), heq,hz']
  simp [St.drop]; omega

theorem Reach.mass_loss {R : ℕ} {a b : St ι} (h : Reach R a b) (hR : 0 < R) (ha : a.Valid) :
    ∃ T : ℕ, ∀ N, mass a.A a.B N ≤ mass b.A b.B N + (a.act.card-b.act.card)*(N/R) + T := by
  induction h with
  | refl => exact ⟨0,by simp⟩
  | @step s h i e hi he ih =>
    obtain ⟨T,hT⟩ := ih
    have hs := h.valid ha
    obtain ⟨V,hV⟩ := (extend_step hs.2.1 he hs.1 i).2.2.2.2
    refine ⟨T+V,fun N => ?_⟩
    have h₁ := hT N; have h₂ := hV N
    change mass a.A a.B N ≤ mass (s.move i e).A (s.move i e).B N +
      (a.act.card-s.act.card)*(N/R) + (T+V)
    change mass s.A s.B N ≤ mass (s.move i e).A (s.move i e).B N + V at h₂
    omega
  | @drop s h i hi hg ih =>
    obtain ⟨T,hT⟩ := ih
    refine ⟨T+1,fun N => ?_⟩
    have h₁ := hT N
    have h₂ := count_le_div_add_one_of_separated hR hg N
    have h₃ := mass_drop (s := s) i N
    have hc : (s.drop i).act.card + 1 = s.act.card := Finset.card_erase_add_one hi
    have hs := Finset.card_le_card h.active_subset
    have hdiff : a.act.card-(s.drop i).act.card = (a.act.card-s.act.card)+1 := by omega
    rw [hdiff,Nat.add_mul,one_mul]
    omega

/-- A system with a minimum number of surviving donors keeps them all and
has a bounded nonzero gap in every such donor under every later move. -/
theorem minimize_active (R : ℕ) (a : St ι) :
    ∃ s, Reach R a s ∧ ∀ t, Reach R s t → t.act = s.act ∧
      ∀ i ∈ s.act, ∃ x ∈ t.B i, ∃ y ∈ t.B i, x < y ∧ y - x ≤ R := by
  classical
  let P (k : ℕ) := ∃ s : St ι, Reach R a s ∧ s.act.card=k
  have hex : ∃ k, P k := ⟨a.act.card,a,Reach.refl,rfl⟩
  obtain ⟨s,hs,hc⟩ := Nat.find_spec hex
  refine ⟨s,hs,fun t ht => ?_⟩
  have hmin := Nat.find_min' hex (show P t.act.card from ⟨t,hs.trans ht,rfl⟩)
  have hact := Finset.eq_of_subset_of_card_le ht.active_subset (hc ▸ hmin)
  refine ⟨hact,fun i hi => ?_⟩
  by_contra hbad
  have hsep : Separated (t.B i) R := by
    intro x hx y hy hxy
    exact le_of_not_gt (fun hh => hbad ⟨x,hx,y,hy,hxy,hh.le⟩)
  have hi' : i ∈ t.act := hact.symm ▸ hi
  have hdt : Reach R a (t.drop i) := (hs.trans ht).drop i hi' hsep
  have hmin' := Nat.find_min' hex (show P (t.drop i).act.card from ⟨t.drop i,hdt,rfl⟩)
  have hc' : (t.drop i).act.card+1=t.act.card := Finset.card_erase_add_one hi'
  have hcard : t.act.card=s.act.card := by rw [hact]
  omega

abbrev Close (R : ℕ) (S : Set ℕ) :=
  ∃ x ∈ S, ∃ y ∈ S, x < y ∧ y-x ≤ R

def Fixed (R : ℕ) (s : St ι) : Prop :=
  ∀ t, Reach R s t → t.act = s.act ∧ ∀ i ∈ s.act, Close R (t.B i)

def Tame (R : ℕ) (s : St ι) (i : ι) : Prop :=
  ∃ p : ℕ+, 0 < Nat.setGcd (s.B i) ∧
    ∀ t, Reach R s t →
      HasGap (t.B i) p ∧ Nat.setGcd (t.B i) = Nat.setGcd (s.B i) ∧
        residues (p : ℕ) (t.B i) = residues (p : ℕ) (s.B i)

theorem Fixed.inherit {R : ℕ} {s t : St ι} (hs : Fixed R s) (ht : Reach R s t) :
    Fixed R t := by
  intro e he
  obtain ⟨ha, hb⟩ := hs e (ht.trans he)
  have hc := (hs t ht).1
  exact ⟨ha.trans hc.symm,fun i hi => hb i (hc ▸ hi)⟩

theorem Tame.inherit {R : ℕ} {s t : St ι} {i : ι} (hs : Tame R s i)
    (ht : Reach R s t) : Tame R t i := by
  obtain ⟨p,hpos,hs⟩ := hs
  obtain ⟨_,hg,hr⟩ := hs t ht
  refine ⟨p,hg.symm ▸ hpos,fun e he => ?_⟩
  obtain ⟨hp,hg',hr'⟩ := hs e (ht.trans he)
  exact ⟨hp,hg'.trans hg.symm,hr'.trans hr.symm⟩

theorem stable_one {R : ℕ} {s : St ι} (hs : Fixed R s) (hz : s.Valid)
    (i : ι) (hi : i ∈ s.act) :
    ∃ t, Reach R s t ∧ Tame R t i := by
  classical
  let G (g : ℕ) := ∃ t : St ι, Reach R s t ∧ Nat.setGcd (t.B i)=g
  let g := Nat.findGreatest G R
  have hb (t : St ι) (ht : Reach R s t) := setGcd_bounds_of_close_pair _ _ ((hs t ht).2 i hi)
  have init := hb s Reach.refl
  have hgpos : 0 < g := init.1.trans_le (Nat.le_findGreatest init.2 ⟨s,Reach.refl,rfl⟩)
  obtain ⟨t,ht,hg⟩ := Nat.findGreatest_of_ne_zero (show Nat.findGreatest G R = g from rfl) hgpos.ne'
  have hgstable (u : St ι) (hu : Reach R t u) : Nat.setGcd (u.B i) = g := by
    have hub := hb u (ht.trans hu)
    have hl : Nat.setGcd (u.B i) ≤ g := Nat.le_findGreatest hub.2 ⟨u,ht.trans hu,rfl⟩
    have hm := Nat.le_of_dvd hub.1 (Nat.setGcd_mono (hu.right_subset (ht.valid hz) i))
    omega
  let Q (q : ℕ) := ∃ u : St ι, Reach R t u ∧ Separated (u.B i) q ∧ HasGap (u.B i) q
  let q := Nat.findGreatest Q R
  obtain ⟨q₀,hq₀p,hq₀b,hq₀s,hq₀h⟩ := exists_minimum_gap (t.B i) R ((hs t ht).2 i hi)
  have hqpos : 0 < q := hq₀p.trans_le (Nat.le_findGreatest hq₀b ⟨t,Reach.refl,hq₀s,hq₀h⟩)
  obtain ⟨u,hu,hqsep,hqgap⟩ := Nat.findGreatest_of_ne_zero (show Nat.findGreatest Q R = q from rfl) hqpos.ne'
  have hqstable (v : St ι) (hv : Reach R u v) : HasGap (v.B i) q := by
    obtain ⟨d,hdp,hdb,hds,hdh⟩ := exists_minimum_gap (v.B i) R ((hs v (ht.trans (hu.trans hv))).2 i hi)
    have hupper : d ≤ q := Nat.le_findGreatest hdb ⟨v,hu.trans hv,hds,hdh⟩
    obtain ⟨x,hx,y,hy,hxy,hd⟩ := hdh
    have hlow := (hqsep.mono_set (hv.right_subset ((ht.trans hu).valid hz) i)) x hx y hy hxy
    exact ⟨x,hx,y,hy,hxy,by omega⟩
  haveI : NeZero q := NeZero.of_pos hqpos
  let H (v : ℕ) := ∃ p : St ι, Reach R u p ∧ (residues q (p.B i)).card=v
  have hex : ∃ v, H v := ⟨_,u,Reach.refl,rfl⟩
  obtain ⟨v,hv,hvR⟩ := Nat.find_spec hex
  refine ⟨v,ht.trans (hu.trans hv),⟨q,hqpos⟩, ?_,?_⟩
  · rw [hgstable v (hu.trans hv)]; exact hgpos
  · intro w hw
    refine ⟨hqstable w (hv.trans hw),
      (hgstable w (hu.trans (hv.trans hw))).trans (hgstable v (hu.trans hv)).symm,?_⟩
    have hsub : residues q (w.B i) ⊆ residues q (v.B i) := by
      intro r hr
      obtain ⟨x,hx,hxr⟩ := mem_residues.mp hr
      exact mem_residues.mpr ⟨x,hw.right_subset ((ht.trans (hu.trans hv)).valid hz) i hx,hxr⟩
    have hmin := Nat.find_min' hex (show H (residues q (w.B i)).card from ⟨w,hv.trans hw,rfl⟩)
    exact Finset.eq_of_subset_of_card_le hsub (hvR ▸ hmin)

theorem stable_all {R : ℕ} {s : St ι} (hs : Fixed R s) (hz : s.Valid)
    (J : Finset ι) (hJ : J ⊆ s.act) :
    ∃ t, Reach R s t ∧ ∀ i ∈ J, Tame R t i := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨s,Reach.refl,by simp⟩
  | @insert i J hi ih =>
    have hJ' : J ⊆ s.act := fun j hj => hJ (Finset.mem_insert_of_mem hj)
    obtain ⟨u,hu,huT⟩ := ih hJ'
    have hi' : i ∈ u.act := (hs u hu).1.symm ▸ hJ (Finset.mem_insert_self i J)
    obtain ⟨v,hv,hvT⟩ := stable_one (hs.inherit hu) (hu.valid hz) i hi'
    refine ⟨v,hu.trans hv,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hvT
    · exact (huT j hj).inherit hv

private theorem lift_one {R : ℕ} {s : St ι} {i : ι} (hi : i ∈ s.act)
    {E F : Set ℕ} (h : DysonDerived s.A (s.B i) E F) :
    ∃ t, Reach R s t ∧ t.A=E ∧ t.B i=F ∧ t.act=s.act := by
  induction h with
  | refl => exact ⟨s,Reach.refl,rfl,rfl,rfl⟩
  | @step C D h e he ih =>
    obtain ⟨t,ht,hA,hB,ha⟩ := ih
    have hv : e ∈ t.A := hA.symm ▸ he
    have hit : i ∈ t.act := ha.symm ▸ hi
    refine ⟨t.move i e,ht.step i e hit hv,?_ ,?_ ,ha⟩
    · simp [St.move,hA,hB]
    · simp [St.move,hA,hB]

theorem progress_one {R : ℕ} {s : St ι} {i : ι}
    (hi : i ∈ s.act) (hT : Tame R s i) (W : Finset ℕ)
    (hW : (W : Set ℕ) ⊆ s.A) (cap : ℕ) :
    ∃ (t : St ι) (z : ℕ), Reach R s t ∧
      ∀ w ∈ W, ∀ c ≤ cap, w+z+c*Nat.setGcd (s.B i) ∈ t.A := by
  obtain ⟨q,hpos,hq⟩ := hT
  have hstable (E F : Set ℕ) (hx : DysonDerived s.A (s.B i) E F) :
      HasGap F q ∧ Nat.setGcd F = Nat.setGcd (s.B i) ∧ residues (q : ℕ) F = residues (q : ℕ) (s.B i) := by
    obtain ⟨t,ht,_,hB,_⟩ := lift_one (R:=R) hi hx
    simpa only [hB] using hq t ht
  obtain ⟨E,F,z,hEF,hprog⟩ := exists_dysonDerived_progressions s.A (s.B i) q hpos hstable W hW cap
  obtain ⟨t,ht,hA,_,_⟩ := lift_one (R:=R) hi hEF
  exact ⟨t,z,ht,fun w hw c hc => hA.symm ▸ hprog w hw c hc⟩

noncomputable def donorStep (s : St ι) (i : ι) : ℕ := Nat.setGcd (s.B i)

theorem progress_box {R : ℕ} {s : St ι} (hs : Fixed R s)
    (hm : ∀ i ∈ s.act, Tame R s i) (x : ℕ) (hx : x ∈ s.A)
    (I : Finset ι) (hI : I ⊆ s.act) (cap : ℕ) :
    ∃ (t : St ι) (u : ℕ), Reach R s t ∧
      ∀ c : ι → ℕ, (∀ i ∈ I, c i ≤ cap) →
        u + ∑ i ∈ I, c i * donorStep s i ∈ t.A := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨s,x,Reach.refl,by simpa using hx⟩
  | @insert i I hi ih =>
    obtain ⟨t,u,ht,hbox⟩ := ih (fun j hj => hI (Finset.mem_insert_of_mem hj))
    have him := hI (Finset.mem_insert_self i I)
    have hit : i ∈ t.act := (hs t ht).1.symm ▸ him
    have htame : Tame R t i := (hm i him).inherit ht
    let W := (Finset.univ : Finset (ι → Fin (cap+1))).image
      (fun b => u + ∑ j ∈ I, (b j : ℕ) * donorStep s j)
    have hW : (W : Set ℕ) ⊆ t.A := by
      intro w hw
      change w ∈ W at hw
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hw
      exact hbox (fun j => (b j : ℕ)) (fun j _ => (b j).isLt.le |> fun h => by omega)
    obtain ⟨v,z,hv,hprog⟩ := progress_one hit htame W hW cap
    refine ⟨v,u+z,ht.trans hv,?_⟩
    intro c hc
    have hw : u + ∑ j ∈ I, c j * donorStep s j ∈ W := by
      let b : ι → Fin (cap+1) := fun j =>
        if hj : j ∈ I then ⟨c j,by have := hc j (Finset.mem_insert_of_mem hj); omega⟩
        else ⟨0,by omega⟩
      refine Finset.mem_image.mpr ⟨b,Finset.mem_univ _,?_⟩
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [b,hj]
    have hpr := hprog _ hw (c i) (hc i (Finset.mem_insert_self i I))
    have heq : Nat.setGcd (t.B i) = donorStep s i := by
      obtain ⟨q,_,hq⟩ := hm i him
      exact (hq t ht).2.1
    rw [heq] at hpr
    rw [Finset.sum_insert hi]
    convert hpr using 1; omega

private theorem eventual_mass_four {a s : St ι} (hz : a.Valid)
    (h : Reach (8 * Fintype.card ι + 1) a s)
    (hm : ∃ K, ∀ N ≥ K, 2*N ≤ mass a.A a.B N) :
    ∃ K, ∀ N ≥ K, 7*N ≤ 4 * mass s.A s.B N := by
  let R := 8 * Fintype.card ι + 1
  change Reach R a s at h
  obtain ⟨M,hM⟩ := h.mass_loss (show 0<R by dsimp [R]; omega) hz
  obtain ⟨K,hK⟩ := hm
  refine ⟨max K (8*M),fun N hN => ?_⟩
  have hmo : 2*N ≤ mass a.A a.B N := hK N (by omega)
  have hstep := Nat.mul_le_mul_left 8 (hM N)
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hstep
  have hc : a.act.card ≤ Fintype.card ι := Finset.card_le_univ _
  have hb : 8*(a.act.card-s.act.card) ≤ R := by dsimp [R]; omega
  have hcap : (8*(a.act.card-s.act.card))*(N/R) ≤ N := calc
    _ ≤ R*(N/R) := Nat.mul_le_mul_right _ hb
    _ ≤ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self N R
  omega

private theorem count_zero_singleton (N : ℕ) : count ({0} : Set ℕ) N = 0 := by
  classical
  unfold count
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hr,hn0⟩ := (@Finset.mem_filter ℕ (fun a => a ∈ ({0}: Set ℕ)) (fun _ => Classical.propDecidable _) _ _).mp hn
  have h1 := (Finset.mem_Icc.mp hr).1
  have h0 : n = 0 := by simpa using hn0
  omega

private theorem nonempty_active {s : St ι} (hz : s.Valid)
    (hm : ∃ K, ∀ N ≥ K, 7*N ≤ 4*mass s.A s.B N) : s.act.Nonempty := by
  classical
  by_contra! hn
  obtain ⟨K,hK⟩ := hm
  have hN := hK (K+1) (by omega)
  have hh (i : ι) : count (s.B i) (K+1) = 0 := by
    rw [hz.2.2 i (by simp [hn]),count_zero_singleton]
  have hc : count s.A (K+1) ≤ K+1 := by
    unfold count
    exact (Finset.card_filter_le _ _).trans (by simp)
  simp only [mass,hh,Finset.sum_const_zero,add_zero] at hN
  omega

/-- The only inverse step needed for the restricted-basis theorem:
a finite mixed system with total prefix mass ≥2N has a productive derived
system whose donors share a divisor and whose receiver has a long block in
one residue class of that divisor. The desired block length is arbitrary. -/
theorem mixed_progression_core_bounded (A : Set ℕ) (B : ι → Set ℕ)
    (hA : 0 ∈ A) (hB : ∀ i, 0 ∈ B i)
    (hmass : ∃ K, ∀ N ≥ K, 2*N ≤ mass A B N) (L : ℕ) (_hL : 0 < L) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ) (g u : ℕ), 0<g ∧ g≤8*Fintype.card ι+1 ∧ 0∈C ∧ (∀ i,0∈D i) ∧
      (∀ j<L,u+g*j∈C) ∧ (∀ i x,x∈D i→g∣x) ∧
      (∃ K,∀ N≥K,7*N≤4*mass C D N) ∧ mixed C D ⊆ mixed A B := by
  classical
  let a : St ι := ⟨A,B,Finset.univ⟩
  let R := 8*Fintype.card ι+1
  have hv : a.Valid := ⟨hA,hB,by simp [a]⟩
  obtain ⟨s,hs,hfixed⟩ := minimize_active R a
  obtain ⟨t,ht,htame⟩ := stable_all hfixed (hs.valid hv) s.act Finset.Subset.rfl
  have hts : t.act=s.act := (hfixed t ht).1
  have htame' (i) (hi : i ∈ t.act) : Tame R t i := htame i (hts ▸ hi)
  let g := t.act.gcd (donorStep t)
  have hvt := (hs.trans ht).valid hv
  obtain ⟨i,hi⟩ := nonempty_active hvt (eventual_mass_four hv (hs.trans ht) hmass)
  have hp := (htame' i hi).choose_spec.1
  have hg : 0 < g := by
    by_contra! hbad
    have hg0 : t.act.gcd (donorStep t) = 0 := by dsimp [g] at hbad; omega
    have hz := (Finset.gcd_eq_zero_iff.mp hg0) i hi
    change Nat.setGcd (t.B i) = 0 at hz
    omega
  have hgle : g ≤ R := by
    have hdiv : g ∣ donorStep t i := Finset.gcd_dvd hi
    have hcap := (setGcd_bounds_of_close_pair _ _ ((hfixed t ht).2 i (hts ▸ hi))).2
    exact (Nat.le_of_dvd hp hdiv).trans hcap
  obtain ⟨off,cap,hcoin⟩ := Erdos338.Coin.progression_box t.act (donorStep t) L
  obtain ⟨e,z,he,hbox⟩ := progress_box (Fixed.inherit (show Fixed R s from hfixed) ht) htame' 0 hvt.1 t.act Finset.Subset.rfl cap
  have hall := hs.trans (ht.trans he)
  have hev := hall.valid hv
  refine ⟨e.A,e.B,g,z+off,hg,hgle,hev.1,hev.2.1,?_,?_,
    eventual_mass_four hv hall hmass, hall.sum_subset hv⟩
  · intro j hj
    obtain ⟨c,hc,hsum⟩ := hcoin j hj.le
    have hl := hbox c hc
    rw [hsum] at hl
    simpa [g,Nat.add_assoc,Nat.mul_comm] using hl
  · intro i x hx
    by_cases hi : i∈t.act
    · have hgi : g ∣ donorStep t i := Finset.gcd_dvd hi
      have hi' : x ∈ t.B i := he.right_subset hvt i hx
      exact hgi.trans (Nat.setGcd_dvd_of_mem hi')
    · have hi' : i ∉ e.act := fun hh => hi (he.active_subset hh)
      have hx0 : x = 0 := by simpa [hev.2.2 i hi'] using hx
      simp [hx0]

theorem mixed_progression_core (A : Set ℕ) (B : ι → Set ℕ)
    (hA : 0 ∈ A) (hB : ∀ i, 0 ∈ B i)
    (hmass : ∃ K, ∀ N ≥ K, 2*N ≤ mass A B N) (L : ℕ) (hL : 0 < L) :
    ∃ (C : Set ℕ) (D : ι → Set ℕ) (g u : ℕ), 0<g ∧ 0∈C ∧ (∀ i,0∈D i) ∧
      (∀ j<L,u+g*j∈C) ∧ (∀ i x,x∈D i→g∣x) ∧
      (∃ K,∀ N≥K,7*N≤4*mass C D N) ∧ mixed C D ⊆ mixed A B := by
  obtain ⟨C,D,g,u,hg,_,h⟩ := mixed_progression_core_bounded A B hA hB hmass L hL
  exact ⟨C,D,g,u,hg,h⟩

#print axioms mixed_progression_core_bounded
#print axioms Reach.mass_loss
#print axioms minimize_active
#print axioms stable_all
#print axioms progress_box
#print axioms mixed_progression_core
end Erdos338.MixedStable
