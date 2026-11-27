import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

/-!
An independent label-promotion proof of positive lower density for
restricted at-most sums. No density or infinite sumset theorem imported.
For finite-rank bases, compare Hegyvári–Hennecart–Plagne (2003).
-/

namespace Erdos338.HHP

noncomputable def pref (P : Nat → Prop) (N : Nat) : Finset Nat := by
  classical
  exact (Finset.range (N+1)).filter (fun n => 0<n ∧ P n)

@[simp] theorem mem_prefix {P : Nat→Prop} {N n : Nat} :
    n ∈ pref P N ↔ 0<n ∧ n≤N ∧ P n := by
  classical
  simp [pref, Finset.mem_range, Nat.lt_succ_iff, and_left_comm, and_assoc]

private theorem card_insert_fresh {α : Type} [DecidableEq α] {a : α} {s : Finset α}
    (no : a∉s) : (insert a s).card=s.card+1 := by
  rw [← Finset.cons_eq_insert a s no, Finset.card_cons]

theorem pref_card_succ (P : Nat→Prop) (n : Nat) :
    (pref P (n+1)).card = (pref P n).card + (by classical exact if P (n+1) then 1 else 0) := by
  classical
  by_cases h : P (n+1)
  · have e : pref P (n+1) = insert (n+1) (pref P n) := by
      ext x
      simp only [mem_prefix, Finset.mem_insert]
      constructor
      · intro hx
        by_cases ne : x=n+1
        · exact Or.inl ne
        · exact Or.inr ⟨hx.1,by omega,hx.2.2⟩
      · rintro (rfl|hx)
        · exact ⟨by omega,le_rfl,h⟩
        · exact ⟨hx.1,by omega,hx.2.2⟩
    have no : n+1 ∉ pref P n := by simp
    rw [e,card_insert_fresh no]
    simp [h]
  · have e : pref P (n+1) = pref P n := by
      ext x
      simp only [mem_prefix]
      constructor
      · intro hx
        refine ⟨hx.1, ?_,hx.2.2⟩
        by_contra nle
        have eq : x=n+1 := by omega
        exact h (eq ▸ hx.2.2)
      · intro hx
        exact ⟨hx.1,by omega,hx.2.2⟩
    simp [e,h]

private theorem card_union_family {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (F : α → Finset β) (k : Nat)
    (bnd : ∀ a∈s, (F a).card≤k) : (s.biUnion F).card ≤ s.card*k := by
  revert bnd
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro bnd
    rw [Finset.biUnion_insert, card_insert_fresh ha, Nat.add_mul, Nat.one_mul]
    exact (Finset.card_union_le _ _).trans <|
        (Nat.add_le_add (bnd a (by simp)) (ih (fun b hb => bnd b (by simp [hb])))).trans (by omega)

structure Marked (A : Nat → Prop) (h k n : Nat) where
  fixed : List Nat
  free : List Nat
  distinct : fixed.Nodup
  separated : ∀ z∈fixed, z∉free
  labels : ∀ z∈fixed++free, A z
  total : fixed.sum+free.sum=n
  budget : fixed.length+free.length≤h
  todo : free.length≤k

def Stage (A : Nat → Prop) (h k n : Nat) : Prop := Nonempty (Marked A h k n)

noncomputable def support {A h k n} (w : Marked A h k n) : Finset Nat :=
  (w.fixed ++ w.free).toFinset

private theorem fresh {A h k n} (w : Marked A h k n) (F : Finset Nat)
    (size : F.card=h+1) : ∃ y∈F, y ∉ support w := by
  classical
  by_contra no
  have sub : F ⊆ support w := fun a ha => Classical.byContradiction (fun hna => no ⟨a,ha,hna⟩)
  have small := (Finset.card_le_card sub).trans
    ((List.toFinset_card_le _).trans (by simpa using w.budget))
  omega

private def HasRoom {A h k n} (w : Marked A h k n) : Prop :=
  w.fixed.length+w.free.length<h

private def Ready (A : Nat→Prop) (h k u : Nat) : Prop :=
  ∃ w : Marked A h k u, HasRoom w

private theorem promote {A h k u x} (w : Marked A h k u)
    (room : HasRoom w) (ha : A x) (notin : x ∉ support w) :
    Stage A h k (u+x) := by
  have no : x ∉ w.fixed ++ w.free := fun hin => notin (List.mem_toFinset.mpr hin)
  refine ⟨⟨x::w.fixed,w.free,List.nodup_cons.mpr ⟨
    fun hmem => no (List.mem_append_left _ hmem), w.distinct⟩,?_,?_,?_,?_,w.todo⟩⟩
  · intro z hz
    rcases List.mem_cons.mp hz with e|he
    · subst z
      exact fun hmem => no (List.mem_append_right _ hmem)
    · exact w.separated z he
  · intro z hz
    rcases List.mem_cons.mp hz with rfl|he
    · exact ha
    · exact w.labels z he
  · simp only [List.sum_cons]
    have eq := w.total
    omega
  · simp only [List.length_cons]
    change w.fixed.length+w.free.length<h at room
    omega

private theorem consume {A h k n} (w : Marked A h (k+1) n) :
    Stage A h k n ∨ ∃ u x, Ready A h k u ∧ A x ∧ n=u+x := by
  cases eq : w.free with
  | nil =>
    exact Or.inl ⟨⟨w.fixed,w.free,w.distinct,w.separated,w.labels,w.total,
      w.budget,by rw [eq]; simp⟩⟩
  | cons x tail =>
    have n_eq := w.total
    have hlen := w.budget
    have ht := w.todo
    simp only [eq, List.sum_cons, List.length_cons] at n_eq hlen ht
    have dist : ∀ z ∈ w.fixed, z ∉ tail := by
      intro z hz hin
      apply w.separated z hz
      rw [eq]
      exact List.mem_cons_of_mem _ hin
    have memb : ∀ z ∈ w.fixed ++ tail, A z := by
      intro z hz
      apply w.labels
      rw [eq]
      rcases List.mem_append.mp hz with hfix|htl
      · exact List.mem_append_left _ hfix
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ htl)
    have vx : A x := by
      apply w.labels
      rw [eq]
      exact List.mem_append_right _ List.mem_cons_self
    have room : w.fixed.length+tail.length<h := by omega
    let rem : Marked A h k (w.fixed.sum + tail.sum) :=
      ⟨w.fixed,tail,w.distinct,dist,memb,rfl,Nat.le_of_lt room,by omega⟩
    exact Or.inr ⟨_,x,⟨rem,room⟩,vx,by omega⟩

/-- One stage of the transfer. The upper window advances by a fixed additive
step M, rather than doubling, and the argument uses no equality patterns. -/
theorem step (A : Nat→Prop) (h k N M : Nat) (F : Finset Nat)
    (fcard : F.card=h+1) (pool : ∀ x∈F, 0<x ∧ x≤M ∧ A x) :
    (pref (Stage A h (k+1)) N).card ≤
      (1+h*(h+1)) * (pref (Stage A h k) (N+M)).card := by
  classical
  let O := pref (Stage A h (k+1)) N
  let G := pref (Stage A h k) (N+M)
  let B := O \ G
  let S := (Finset.range (N+1)).filter (Ready A h k)
  have valid (u : {u // u ∈ S}) : Ready A h k u.val :=
    (Finset.mem_filter.mp u.property).2
  let wit (u : {u // u ∈ S}) : Marked A h k u.val := Classical.choose (valid u)
  have room (u : {u // u ∈ S}) : HasRoom (wit u) := Classical.choose_spec (valid u)
  have opt (u : {u // u ∈ S}) : ∃ y∈F, y ∉ support (wit u) := fresh _ _ fcard
  let y (u : {u // u ∈ S}) := Classical.choose (opt u)
  have good (u : {u // u ∈ S}) : y u ∈ F ∧ y u ∉ support (wit u) :=
    Classical.choose_spec (opt u)
  have Sbound : S.card ≤ G.card * F.card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card_of_injective (f := fun u =>
      ⟨(u.val + y u, y u), by
        apply Finset.mem_product.mpr
        have hp := pool (y u) (good u).1
        have hu : u.val ≤ N := by
          have r := (Finset.mem_filter.mp u.property).1
          have rr := Finset.mem_range.mp r
          omega
        exact ⟨mem_prefix.mpr ⟨by omega,by omega,promote (wit u) (room u) hp.2.2 (good u).2⟩,
          (good u).1⟩⟩) (by
      intro u v e
      have p := congrArg Subtype.val e
      have e1 := congrArg Prod.fst p
      have e2 := congrArg Prod.snd p
      change u.val+y u=v.val+y v at e1
      change y u=y v at e2
      exact Subtype.ext (by omega))
  let exceptions (u : Nat) : Finset Nat :=
    if e : u ∈ S then (support (wit ⟨u,e⟩)).image (fun x => u+x) else ∅
  have exc_size (u : Nat) (hu : u∈S) : (exceptions u).card≤h := by
    simp only [exceptions,dif_pos hu]
    exact Finset.card_image_le.trans ((List.toFinset_card_le _).trans (by
      rw [List.length_append]; exact (wit _).budget))
  have Bsub : B ⊆ S.biUnion exceptions := by
    intro n hn
    obtain ⟨hnO,hnG⟩ := Finset.mem_sdiff.mp hn
    have ⟨positive,bounded,⟨w⟩⟩ := mem_prefix.mp hnO
    rcases consume w with ready|⟨u,x,v,hx,hux⟩
    · exact (hnG (mem_prefix.mpr ⟨positive,by omega,ready⟩)).elim
    · have hu : u∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),v⟩
      refine Finset.mem_biUnion.mpr ⟨u,hu,?_⟩
      simp only [exceptions,dif_pos hu]
      have xmem : x∈support (wit ⟨u,hu⟩) := by
        apply Classical.byContradiction
        intro xno
        apply hnG
        exact mem_prefix.mpr ⟨positive,by omega,
          hux ▸ promote (wit ⟨u,hu⟩) (room _) hx xno⟩
      exact Finset.mem_image.mpr ⟨x,xmem,hux.symm⟩
  have Bbound : B.card ≤ (h*(h+1))*G.card := by
    calc
      B.card ≤ (S.biUnion exceptions).card := Finset.card_le_card Bsub
      _ ≤ S.card*h := card_union_family S exceptions h exc_size
      _ ≤ (G.card*F.card)*h := Nat.mul_le_mul_right _ Sbound
      _ = (h*(h+1))*G.card := by rw [fcard]; ac_rfl
  have Osub : O ⊆ G ∪ B := by
    intro x hx
    by_cases g : x∈G
    · exact Finset.mem_union.mpr (Or.inl g)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx,g⟩))
  calc
    O.card ≤ (G∪B).card := Finset.card_le_card Osub
    _ ≤ G.card+B.card := Finset.card_union_le _ _
    _ ≤ G.card+(h*(h+1))*G.card := Nat.add_le_add_left Bbound _
    _ = (1+h*(h+1))*G.card := by rw [Nat.add_mul,Nat.one_mul]

theorem iterate (A : Nat→Prop) (h k N M : Nat) (F : Finset Nat)
    (fcard : F.card=h+1) (pool : ∀ x∈F, 0<x ∧ x≤M ∧ A x) :
    (pref (Stage A h k) N).card ≤
      (1+h*(h+1))^k * (pref (Stage A h 0) (N+k*M)).card := by
  induction k generalizing N with
  | zero => simp
  | succ k ih =>
    have t := (step A h k N M F fcard pool).trans
      (Nat.mul_le_mul_left (1+h*(h+1)) (ih (N+M)))
    rw [Nat.pow_succ,Nat.succ_mul]
    have same : N + (k*M+M) = N+M+k*M := by omega
    rw [same]
    simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using t

private theorem sum_le_len (M : Nat) (xs : List Nat)
    (bounded : ∀ x∈xs, x≤M) : xs.sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ih' := ih (fun x hx => bounded x (List.mem_cons_of_mem _ hx))
    have ha := bounded a List.mem_cons_self
    rw [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def Ordinary (A : Nat→Prop) (h : Nat) : Prop := ∃ L, ∀ n≥L,
  ∃ xs : List Nat, (∀ x∈xs, A x) ∧ xs.sum=n ∧ xs.length≤h

def Restricted (A : Nat→Prop) (h n : Nat) : Prop := ∃ xs : List Nat, xs.Nodup ∧
  (∀ x∈xs, A x) ∧ xs.sum=n ∧ xs.length≤h

private theorem pool_exists {A h} (basis : Ordinary A h) (k : Nat) :
    ∃ (M : Nat) (F : Finset Nat), F.card=k ∧ ∀ x∈F, 0<x ∧ x≤M ∧ A x := by
  classical
  have wide (M : Nat) : ∃ x, M<x ∧ A x := by
    obtain ⟨L,cof⟩ := basis
    obtain ⟨xs,mem,eq,len⟩ := cof (L+h*M+1) (by omega)
    by_contra nope
    have bef : ∀ x∈xs, x≤M := fun x hx =>
      Nat.le_of_not_gt (fun hi => nope ⟨x,hi,mem x hx⟩)
    have bnd := (sum_le_len M xs bef).trans (Nat.mul_le_mul_right M len)
    omega
  induction k with
  | zero => exact ⟨0,∅,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨M,F,c,pool⟩ := ih
    obtain ⟨x,hi,hx⟩ := wide M
    have fresh : x∉F := fun z => Nat.not_lt_of_ge (pool x z).2.1 hi
    refine ⟨x,insert x F,by rw [card_insert_fresh fresh,c],?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hf
    · exact ⟨by omega,le_rfl,hx⟩
    · have v := pool z hf
      exact ⟨v.1,by omega,v.2.2⟩

private theorem start {A h n} {xs : List Nat}
    (mem : ∀ x∈xs,A x) (eq : xs.sum=n) (len : xs.length≤h) : Stage A h h n :=
  ⟨⟨[],xs,List.Pairwise.nil,by simp,by simpa using mem,by simpa using eq,by simpa using len,len⟩⟩

theorem terminal (A : Nat→Prop) (h : Nat) : Stage A h 0 = Restricted A h := by
  funext n
  apply propext
  constructor
  · rintro ⟨w⟩
    have empty := List.length_eq_zero_iff.mp (Nat.le_zero.mp w.todo)
    refine ⟨w.fixed,w.distinct,?_,?_,?_⟩
    · simpa [empty] using w.labels
    · simpa [empty] using w.total
    · simpa [empty] using w.budget
  · rintro ⟨xs,nd,mem,eq,len⟩
    exact ⟨⟨xs,[],nd,by simp,by simpa using mem,by simpa using eq,by simpa using len,by simp⟩⟩

/-- HHP for the same at-most conventions as #338, with a purely integer prefix
form. The eventual bound uses coefficient 2*(1+h*(h+1))^h. -/
def densityFactor (h : ℕ) : ℕ := 2 * (1 + h*(h+1))^h

theorem densityFactor_pos (h : ℕ) : 0 < densityFactor h := by
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by omega))

/-- Here the multiplicative prefix-density constant depends only on
the ordinary rank; only the onset may depend on the basis itself. -/
theorem uniform_positive_lower_density {A h} (basis : Ordinary A h) :
    ∃ N₀ : Nat, ∀ n≥N₀, n≤densityFactor h*(pref (Restricted A h) n).card := by
  classical
  obtain ⟨M,F,size,pool⟩ := pool_exists basis (h+1)
  obtain ⟨L,cof⟩ := basis
  let H := max 1 L
  let c := (1+h*(h+1))^h
  refine ⟨2*(H+h*M)+1,?_⟩
  intro n gn
  let N := n-h*M
  have Npos : H≤N := by dsimp [N]; omega
  have Nscale : N+h*M=n := by dsimp [N]; omega
  have Ho : 0<H := lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)
  have HL : L≤H := Nat.le_max_right _ _
  have coverage : N+1-H ≤ (pref (Stage A h h) N).card := by
    simpa only [Finset.card_range] using
      Finset.card_le_card_of_injOn (s:=Finset.range (N+1-H)) (t:=pref (Stage A h h) N)
        (fun z=>H+z)
        (fun z hz=>by
          have small := Finset.mem_range.mp hz
          change H+z ∈ pref (Stage A h h) N
          obtain ⟨xs,ha,total,len⟩ := cof (H+z) (by omega)
          exact mem_prefix.mpr ⟨by omega,by omega,start ha total len⟩)
        (fun _ _ _ _ eq => by dsimp at eq; omega)
  have stepdown := iterate A h h N M F size pool
  rw [Nscale, terminal] at stepdown
  have cts : N+1-H ≤ c*(pref (Restricted A h) n).card := coverage.trans stepdown
  calc
    n ≤ 2*(N+1-H) := by omega
    _ ≤ 2*(c*(pref (Restricted A h) n).card) := Nat.mul_le_mul_left 2 cts
    _ = (2*c)*(pref (Restricted A h) n).card := (Nat.mul_assoc _ _ _).symm

theorem positive_lower_density {A h} (basis : Ordinary A h) :
    ∃ D N₀ : Nat, 0<D ∧ ∀ n≥N₀, n≤D*(pref (Restricted A h) n).card := by
  obtain ⟨N, hN⟩ := uniform_positive_lower_density basis
  exact ⟨densityFactor h,N,densityFactor_pos h,hN⟩

#print axioms uniform_positive_lower_density
#print axioms iterate
#print axioms positive_lower_density
end Erdos338.HHP
