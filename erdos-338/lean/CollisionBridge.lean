import PopularityCounting
import RobustLayers

/-! Integration of the finite collision estimates with CYZ's adaptive layers. -/
open scoped BigOperators
namespace Erdos338.Existence.CollisionBridge
open Erdos338.Growth Erdos338.Popularity Erdos338.Existence.Analytic

noncomputable def positivePrefix (P : ℕ → Prop) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N+1)).filter (fun n => 0<n ∧ P n)

theorem mem_positivePrefix {P : ℕ → Prop} {N n : ℕ} :
    n ∈ positivePrefix P N ↔ n ≤ N ∧ 0<n ∧ P n := by
  simp [positivePrefix, Nat.lt_succ_iff]

theorem prefix_card (P : ℕ → Prop) (N : ℕ) :
    (positivePrefix P N).card = hits P N := by
  classical
  induction N with
  | zero =>
    have eq : positivePrefix P 0 = ∅ := by ext x; simp [mem_positivePrefix]; omega
    simp [eq,hits]
  | succ n ih =>
    change ((Finset.range (n+1+1)).filter (fun m => 0<m ∧ P m)).card = hits P (n+1)
    have eq : hits P (n+1) = hits P n + (if P (n+1) then 1 else 0) := rfl
    rw [eq,Finset.range_add_one, Finset.filter_insert]
    by_cases h : P (n+1)
    · simp only [Nat.succ_pos, true_and,h,if_true]
      rw [Finset.card_insert_of_notMem (by simp),← ih]
      rfl
    · simpa [h,positivePrefix] using ih

private theorem pfx_le (P : ℕ → Prop) (N : ℕ) : (positivePrefix P N).card ≤ N := by
  have mem0 : 0 ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have sub : positivePrefix P N ⊆ (Finset.range (N+1)).erase 0 := by
    intro x hx
    obtain ⟨le,pos,_⟩ := mem_positivePrefix.mp hx
    exact Finset.mem_erase.mpr ⟨Nat.ne_of_gt pos, Finset.mem_range.mpr (by omega)⟩
  exact (Finset.card_le_card sub).trans_eq (by rw [Finset.card_erase_of_mem mem0,Finset.card_range]; omega)

private theorem rep_as_finset {A : Set ℕ} {r x : ℕ} (hx : R A r x) :
    ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ (∑ a ∈ S, a) = x := by
  obtain ⟨xs,nd,ha,sm,ln⟩ := hx
  have hl := Finset.sum_toList xs.toFinset
  have hsum := (List.toFinset_toList nd).sum_eq
  exact ⟨xs.toFinset, fun a h => ha a (by simpa using h), by simpa [List.toFinset_card_of_nodup nd] using ln,
    hl.symm.trans (hsum.trans sm)⟩

private theorem rep_as_list {A : Set ℕ} {r x : ℕ} (S : Finset ℕ)
    (ha : ∀ a ∈ S, a ∈ A) (hcard : S.card ≤ r) (hs : (∑ a ∈ S, a) = x) :
    R A r x :=
  ⟨S.toList,S.nodup_toList,fun a h => ha a (by simpa using h),S.sum_toList.trans hs,by simpa using hcard⟩

private theorem card_small_prefix (A : Set ℕ) (r N : ℕ) :
    (restrictedPrefix A r N).card = 1+hits (R A r) N := by
  classical
  have hn : 0 ∉ positivePrefix (R A r) N := by simp [mem_positivePrefix]
  have eq : restrictedPrefix A r N = insert 0 (positivePrefix (R A r) N) := by
    ext x
    by_cases hx : x=0
    · subst x
      have hm : 0 ∈ restrictedPrefix A r N := by
        unfold restrictedPrefix
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ∅, by simp⟩
      simp [hm]
    · have hxpos := Nat.pos_of_ne_zero hx
      change x ∈ (Finset.range (N+1)).filter _ ↔ _
      simp only [Finset.mem_filter,Finset.mem_range, Nat.lt_succ_iff, Finset.mem_insert,hx,
        false_or,mem_positivePrefix,hxpos,true_and]
      exact and_congr_right fun _ => ⟨fun ⟨S,ha,hr,hs⟩ => rep_as_list S ha hr hs, rep_as_finset⟩
  rw [eq,Finset.card_insert_of_notMem hn,prefix_card,Nat.add_comm]

private theorem source_fits {A : Set ℕ} {r n : ℕ}
    (U : Finset (ℕ×ℕ)) (F : ℕ → Finset ℕ)
    (sep : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → Disjoint (F x.1 ∪ F x.2) (F y.1 ∪ F y.2))
    (valid : ∀ x ∈ U, (∀ a ∈ F x.1, a ∈ A) ∧ (∀ a ∈ F x.2, a ∈ A) ∧
      (F x.1).card ≤ r ∧ (F x.2).card ≤ r ∧
      (∑ a ∈ F x.1, a) = x.1 ∧ (∑ a ∈ F x.2, a) = x.2 ∧
      Disjoint (F x.1) (F x.2) ∧ x.1+x.2=n) :
    Pack A ⟨r,U.card⟩ n := by
  let f (p : ℕ×ℕ) := (F p.1 ∪ F p.2).toList
  refine ⟨U.toList.map f, ?_, by simp, ?_⟩
  · rw [List.pairwise_map]
    apply List.Pairwise.imp ?_ (List.Pairwise.and_mem.mp U.nodup_toList)
    rintro x y ⟨hxU,hyU,hne⟩ a ha hb
    exact Finset.disjoint_left.mp (sep x (by simpa using hxU) y (by simpa using hyU) hne)
      (by simpa [f] using ha) (by simpa [f] using hb)
  · intro xs hx
    obtain ⟨p,hp,he⟩ := List.mem_map.mp hx
    subst xs
    obtain ⟨hL,hR,lL,lR,sL,sR,di,es⟩ := valid p (by simpa using hp)
    refine ⟨Finset.nodup_toList _, ?_, ?_, ?_⟩
    · intro a ha
      exact (Finset.mem_union.mp (by simpa [f] using ha)).elim (hL a) (hR a)
    · dsimp [f]
      rw [Finset.sum_toList,Finset.sum_union di,sL,sR,es]
    · have ca := (Finset.card_union_le (F p.1) (F p.2)).trans (Nat.add_le_add lL lR)
      simpa [f,Nat.two_mul] using ca

/-- The finite aggregate inequality needed for the adaptive rank descent. -/
theorem collisionBound (A : Set ℕ) : CollisionBound A := by
  classical
  intro r Q N _ hQ
  let X := positivePrefix (R A r) N
  let E := restrictedPrefix A (r-1) N
  let e := E.card
  let B := positivePrefix (fun _ => True) (2*N)
  let D := positivePrefix (Pack A ⟨r,Q⟩) (2*N)
  have xp : ∀ x ∈ X, 0<x ∧ x≤N ∧ R A r x := by
    intro x hx
    obtain ⟨hle,hpos,hR⟩ := mem_positivePrefix.mp hx
    exact ⟨hpos,hle,hR⟩
  have prep : ∀ x : ℕ, ∃ S : Finset ℕ, x ∈ X →
      (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ (∑ a ∈ S, a) = x := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨S,hS⟩ := rep_as_finset (xp x hx).2.2
      exact ⟨S,fun _ => hS⟩
    · exact ⟨∅,fun h => (hx h).elim⟩
  choose F v using prep
  let P := (X ×ˢ X).filter (fun p => Disjoint (F p.1) (F p.2))
  let s (p : ℕ×ℕ) := p.1+p.2
  let T (n : ℕ) := P.filter (fun p => s p=n)
  have attrs : ∀ n, ∀ p ∈ T n,
      p.1 ∈ X ∧ p.2 ∈ X ∧ Disjoint (F p.1) (F p.2) ∧ s p=n := by
    intro n p hp
    obtain ⟨hp,sm⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hL,hR⟩ := Finset.mem_product.mp hp
    exact ⟨hL,hR,hd,sm⟩
  have strips : ∀ x ∈ X, ∀ a ∈ F x, a≤x ∧ x-a ∈ E := fun x hx a ha =>
    strip_witness (xp x hx).2.1 (v x hx).1 (v x hx).2.1 (v x hx).2.2 ha
  have sumattrs : ∀ n, ∀ p ∈ T n, p.1+p.2=n := fun n p hp => (attrs n p hp).2.2.2
  have lower := global_noncollision_count X F r e
    (fun x hx => (v x hx).2.1)
    (fun a => global_incidence X F E a (fun x hx ha => strips x hx a ha))
  have inB : ∀ p ∈ P, s p ∈ B := by
    intro p hp
    obtain ⟨hL,hR⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have kl := xp _ hL
    have kr := xp _ hR
    exact mem_positivePrefix.mpr ⟨by dsimp [s]; omega,by dsimp [s]; omega,trivial⟩
  have sumT : (∑ n ∈ B, (T n).card) = P.card := by
    dsimp [T]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact congrArg Finset.card (Finset.filter_true_of_mem inB)
  have dsub : D ⊆ B := by
    intro n hn
    obtain ⟨hle,hpos,_⟩ := mem_positivePrefix.mp hn
    exact mem_positivePrefix.mpr ⟨hle,hpos,trivial⟩
  have classBound : ∀ n ∈ B, (T n).card ≤ if n ∈ D then N else 4*r*e*(Q-1) := by
    intro n hn
    by_cases md : n ∈ D
    · rw [if_pos md]
      have proj : (T n).card ≤ X.card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · exact fun p hp => (attrs n p hp).1
        · intro p hp q hq eq
          change p.1=q.1 at eq
          have psm := sumattrs n p hp
          have qsm := sumattrs n q hq
          apply Prod.ext <;> omega
      exact proj.trans (pfx_le (R A r) N)
    · rw [if_neg md]
      apply Nat.le_of_not_gt
      intro many
      have bw := fixed_sum_packing_from_fibers (T n) F r e (Q-1)
        (fun p hp => ⟨(v _ (attrs n p hp).1).2.1,(v _ (attrs n p hp).2.1).2.1⟩)
        ?_ ?_ ?_ many
      · obtain ⟨U,hu,hC,sep⟩ := bw
        have ep : U.card=Q := by omega
        have pkn := source_fits (A := A) (r := r) (n := n) U F sep (by
          intro p hp
          obtain ⟨hL,hR,hd,sm⟩ := attrs n p (hu hp)
          exact ⟨(v _ hL).1,(v _ hR).1,(v _ hL).2.1,(v _ hR).2.1,
            (v _ hL).2.2,(v _ hR).2.2,hd,sm⟩)
        have hpk : Pack A ⟨r,Q⟩ n := by simpa [ep] using pkn
        obtain ⟨hBn,hp,_⟩ := mem_positivePrefix.mp hn
        exact md (mem_positivePrefix.mpr ⟨hBn,hp,hpk⟩)
      · intro p hp
        have mem := (attrs n p hp).1
        have pp := (xp _ mem).1
        have su := (v _ mem).2.2
        have nemp : (F p.1).Nonempty := by
          by_contra hh
          have em := Finset.not_nonempty_iff_eq_empty.mp hh
          rw [em,Finset.sum_empty] at su
          omega
        exact nemp.mono (Finset.subset_union_left)
      · intro a
        exact fixed_sum_fiber (T n) F E n a (sumattrs n)
          (fun p hp ha => strips _ (attrs n p hp).1 _ ha)
      · intro a
        apply Finset.card_le_card_of_injOn (fun p : ℕ×ℕ => p.2-a)
        · intro p hp
          obtain ⟨ht,ha⟩ := Finset.mem_filter.mp hp
          exact (strips _ (attrs n p ht).2.1 _ ha).2
        · intro p hp q hq eq
          change p.2-a=q.2-a at eq
          obtain ⟨ht,ha⟩ := Finset.mem_filter.mp hp
          obtain ⟨hq',hb⟩ := Finset.mem_filter.mp hq
          have lp := (strips _ (attrs n p ht).2.1 _ ha).1
          have lq := (strips _ (attrs n q hq').2.1 _ hb).1
          have sp := sumattrs n p ht
          have sq := sumattrs n q hq'
          apply Prod.ext <;> omega
  let c := 4*r*e*(Q-1)
  have upper : P.card ≤ D.card*N + (2*N)*c := by
    rw [← sumT]
    calc
      ∑ n ∈ B, (T n).card ≤ ∑ n ∈ B, (if n ∈ D then N else c) :=
        Finset.sum_le_sum classBound
      _ ≤ ∑ n ∈ B, ((if n ∈ D then N else 0)+c) := by
        apply Finset.sum_le_sum
        intro n _
        by_cases h : n ∈ D <;> simp [h]
      _ = D.card*N + B.card*c := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        have filt : B.filter (fun n => n ∈ D) = D := by
          ext n
          exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨dsub h,h⟩⟩
        rw [filt,Finset.sum_const_nat (fun _ _ => rfl),Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ D.card*N + (2*N)*c :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (pfx_le _ _)) _
  have mz : X.card ≤ N := pfx_le _ _
  have maxCollision : X.card*r*e ≤ N*r*e := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ mz)
  have hfin : X.card*X.card ≤ (D.card*N + (2*N)*c) + (N*r*e) :=
    lower.trans (Nat.add_le_add upper maxCollision)
  have coeff : 2*c+r*e ≤ 9*r*Q*e := by
    have hmul : 8*(Q-1)+1 ≤ 9*Q := by omega
    calc
      2*c+r*e = (r*e)*(8*(Q-1)+1) := by
        dsimp [c]
        rw [Nat.mul_add, Nat.mul_one]
        congr 1
        have h8 : 8=2*4 := rfl
        simp only [h8,Nat.mul_assoc]
        ac_rfl
      _ ≤ (r*e)*(9*Q) := Nat.mul_le_mul_left _ hmul
      _ = _ := by ac_rfl
  have organized : (D.card*N + (2*N)*c) + N*r*e = N*(D.card+(2*c+r*e)) := by
    simp only [Nat.mul_add]
    ac_rfl
  have result := (organized ▸ hfin).trans
    (Nat.mul_le_mul_left N (Nat.add_le_add_left coeff D.card))
  change (positivePrefix (R A r) N).card * (positivePrefix (R A r) N).card ≤
    N*((positivePrefix (Pack A ⟨r,Q⟩) (2*N)).card + 9*r*Q*(restrictedPrefix A (r-1) N).card) at result
  simpa [prefix_card,card_small_prefix] using result

#print axioms collisionBound
#print axioms source_fits
end Erdos338.Existence.CollisionBridge
