import CatalogueAdapter
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.Finite

/-! Global sparse ordinary-sum traces for the at-most convention in #338(iii). -/
open Filter
open scoped BigOperators
namespace Erdos338.SparseTrace
open CatalogueAdapter

/-- Unbounded in the usual integers, independently of any choice of representation. -/
def Unbounded (S : Set ℕ) : Prop := ∀ N, ∃ n > N, n ∈ S

/-- An ordinary rectangular sumset. There are no distinctness conditions on the choices. -/
def box {k : ℕ} (B : Fin k → Set ℕ) : Set ℕ :=
  {n | ∃ f : Fin k → ℕ, (∀ i, f i ∈ B i) ∧ ∑ i, f i = n}

/-- Prescribed global separation among *all* members of a single column. -/
def Sparse (g : ℕ → ℕ) (S : Set ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → g x < y

def TraceProperty (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ T : Set ℕ, Unbounded T → ∀ g : ℕ → ℕ,
    ∃ (k : ℕ) (_ : k ≤ h) (B : Fin k → Set ℕ),
      (∀ i, B i ⊆ A) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, Sparse g (B i)) ∧ Unbounded (T ∩ box B)

private theorem canon_one (a : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∃ c, ∀ n, a (f n) = c) ∨ Tendsto (a ∘ f) atTop atTop) := by
  classical
  by_cases H : ∃ c, ∀ N, ∃ n > N, a n = c
  · obtain ⟨c, hc⟩ := H
    obtain ⟨f,hf,hc'⟩ := Nat.exists_strictMono_subsequence hc
    exact ⟨f,hf, Or.inl ⟨c,hc'⟩⟩
  · push Not at H
    choose b hb using H
    refine ⟨id,strictMono_id, Or.inr ?_⟩
    apply tendsto_atTop.2
    intro K
    rw [eventually_atTop]
    refine ⟨(Finset.range K).sup b + 1, ?_⟩
    intro n hn
    change K ≤ a n
    by_contra! ha
    have hx := Finset.le_sup (f:=b) (Finset.mem_range.mpr ha)
    exact (hb (a n) n (by omega)) rfl

private theorem canon_cols {k : ℕ} (a : ℕ → Fin k → ℕ) (I : Finset (Fin k)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i ∈ I,
      (∃ c, ∀ n, a (f n) i = c) ∨ Tendsto (fun n => a (f n) i) atTop atTop := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨id,strictMono_id,by simp⟩
  | @insert i I _ ih =>
    obtain ⟨f,hf,H⟩ := ih
    obtain ⟨p,hp,hp'⟩ := canon_one (fun n => a (f n) i)
    refine ⟨f ∘ p,hf.comp hp, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact hp'
    · rcases H j hj with ⟨c,hc⟩|ht
      · exact Or.inl ⟨c,fun n => hc (p n)⟩
      · exact Or.inr (ht.comp hp.tendsto_atTop)

private theorem block_extract {k : ℕ} (a : ℕ → Fin k → ℕ) (g : ℕ → ℕ)
    (H : ∀ i, (∃ c, ∀ n, a n i = c) ∨ Tendsto (fun n => a n i) atTop atTop) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ i j p q, p < q → (¬ ∃ c, ∀ n, a n j = c) →
        max (a (f p) i) (g (a (f p) i)) < a (f q) j := by
  classical
  let b (p : ℕ) := (Finset.range (p+1)).sup (fun n => Finset.univ.sup (fun i => max (a n i) (g (a n i))))
  have bound (p n : ℕ) (hn : n ≤ p) (i : Fin k) :
      max (a n i) (g (a n i)) ≤ b p := by
    exact (Finset.le_sup (f:= fun i => max (a n i) (g (a n i))) (Finset.mem_univ i)).trans
      (Finset.le_sup (f:=fun n => Finset.univ.sup (fun i => max (a n i) (g (a n i))))
        (Finset.mem_range.mpr (by omega)))
  have nxt (p : ℕ) : ∃ q > p, ∀ i, (¬ ∃ c, ∀ n, a n i = c) → b p < a q i := by
    have ev (i : Fin k) : ∀ᶠ n : ℕ in atTop, (¬ ∃ c, ∀ m, a m i = c) → b p < a n i := by
      by_cases hi : ∃ c, ∀ n, a n i = c
      · exact Eventually.of_forall fun _ h => (h hi).elim
      · exact ((tendsto_atTop.1 ((H i).resolve_left hi)) (b p+1)).mono fun _ h _ => by omega
    have all := (Filter.eventually_all.2 ev).and (eventually_gt_atTop p)
    obtain ⟨q,hq,hqp⟩ := all.exists
    exact ⟨q,hqp,hq⟩
  choose next hn hp using nxt
  let f : ℕ → ℕ := Nat.rec 0 (fun _ prev => next prev)
  have fs (n : ℕ) : f (n+1) = next (f n) := rfl
  have hf : StrictMono f := strictMono_nat_of_lt_succ fun n => hn (f n)
  refine ⟨f,hf,?_⟩
  intro i j p q hpq hj
  obtain _|q := q
  · omega
  · rw [fs]
    exact lt_of_le_of_lt (bound (f q) (f p) (hf.monotone (by omega)) i) (hp (f q) j hj)

theorem sparse_columns_with_escape {k : ℕ} (a : ℕ → Fin k → ℕ)
    (hi : ∀ n, Function.Injective (a n)) (g : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      let B (i : Fin k) := Set.range (fun n => a (f n) i)
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, Sparse g (B i)) ∧
        (∀ i, (∃ c, ∀ n, a (f n) i = c) ∨
          Tendsto (fun n => a (f n) i) atTop atTop) := by
  classical
  obtain ⟨p,hp,can⟩ := canon_cols a Finset.univ
  let v := fun n i => a (p n) i
  obtain ⟨q,hq,sep⟩ := block_extract v g fun i => can i (Finset.mem_univ i)
  refine ⟨p ∘ q,hp.comp hq,?_⟩
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨m,rfl⟩ ⟨n,e⟩
    change v (q n) j = v (q m) i at e
    by_cases cj : ∃ c, ∀ n, v n j = c
    · obtain ⟨c,hc⟩ := cj
      exact hij (hi (p (q m)) (e.symm.trans ((hc _).trans (hc _).symm)))
    by_cases ci : ∃ c, ∀ n, v n i = c
    · obtain ⟨c,hc⟩ := ci
      exact hij (hi (p (q n)) (((hc _).trans (hc _).symm).trans e.symm))
    rcases lt_trichotomy m n with l|rfl|r
    · have h := sep i j m n l cj; omega
    · exact hij (hi _ e.symm)
    · have h := sep j i n m r ci; omega
  · intro i x hx y hy hxy
    obtain ⟨m,rfl⟩ := hx
    obtain ⟨n,rfl⟩ := hy
    change v (q m) i < v (q n) i at hxy
    change g (v (q m) i) < v (q n) i
    by_cases ci : ∃ c, ∀ n, v n i = c
    · obtain ⟨c,hc⟩ := ci
      rw [hc, hc] at hxy; omega
    rcases lt_trichotomy m n with l|rfl|r
    · have h := sep i i m n l ci; omega
    · omega
    · have h := sep i i n m r ci; omega
  · intro i
    rcases can i (Finset.mem_univ i) with ⟨c,hc⟩|ht
    · exact Or.inl ⟨c,fun n => hc (q n)⟩
    · exact Or.inr (ht.comp hq.tendsto_atTop)


theorem sparse_columns {k : ℕ} (a : ℕ → Fin k → ℕ)
    (hi : ∀ n, Function.Injective (a n)) (g : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      let B (i : Fin k) := Set.range (fun n => a (f n) i)
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, Sparse g (B i)) := by
  obtain ⟨f,hf,hd,hs,_⟩ := sparse_columns_with_escape a hi g
  exact ⟨f,hf,hd,hs⟩


/-- The unrestricted pointwise property, used only to identify the orthogonal ideal. -/
def hit (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ ∑ x ∈ S, x = n}

/-- A sparse rectangular trace is one family of columns chosen before the
 infinitely many targets, not a different choice for each target. -/
def TraceAt (A : Set ℕ) (h : ℕ) (T : Set ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ (k : ℕ) (_ : k ≤ h) (B : Fin k → Set ℕ),
    (∀ i, B i ⊆ A) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, Sparse g (B i)) ∧ Unbounded (T ∩ box B)

/-- Keep the same singleton anchors for all cutoffs, while simultaneously
    pushing all the other summands above an arbitrary cutoff. -/
def AnchoredTraceAt (A : Set ℕ) (h : ℕ) (T : Set ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ (k : ℕ) (_ : k ≤ h) (B : Fin k → Set ℕ),
    (∀ i, B i ⊆ A) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, Sparse g (B i)) ∧
    (∀ i, (∃ c, B i = {c}) ∨ Unbounded (B i)) ∧
    ∀ D : ℕ, Unbounded (T ∩ box (fun i => {x | x ∈ B i ∧
      ((∃ c, B i = {c}) ∨ D ≤ x)}))

def AnchoredTraceProperty (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ T : Set ℕ, Unbounded T → ∀ g : ℕ → ℕ, AnchoredTraceAt A h T g

private theorem extract_anchored_trace {A : Set ℕ} {h : ℕ} {T : Set ℕ}
    (H : Unbounded (T ∩ hit A h)) (g : ℕ → ℕ) : AnchoredTraceAt A h T g := by
    classical
    obtain ⟨t,ht,hTs⟩ := Nat.exists_strictMono_subsequence H
    choose U hU hcard hsum using (fun n => (hTs n).2)
    let size (n : ℕ) : Fin (h+1) := ⟨(U n).card, by have := hcard n; omega⟩
    have recSize : ∃ j, ∃ᶠ n : ℕ in atTop, size n = j := by
      apply Filter.frequently_exists.mp
      exact Frequently.of_forall fun n => ⟨size n,rfl⟩
    obtain ⟨j,hj⟩ := recSize
    have occ (n : ℕ) : ∃ z > n, size z = j := by
      exact ((hj.and_eventually (eventually_gt_atTop n)).exists.imp fun _ p => p.symm)
    obtain ⟨p,hp,hs⟩ := Nat.exists_strictMono_subsequence occ
    have hc (n : ℕ) : (U (p n)).card = j.val := congrArg Fin.val (hs n)
    let e (n : ℕ) := (U (p n)).orderIsoOfFin (hc n)
    let a (n : ℕ) (i : Fin j.val) : ℕ := (e n i).val
    have hi (n : ℕ) : Function.Injective (a n) := fun _ _ eq => (e n).injective (Subtype.ext eq)
    have hasSum (n : ℕ) : ∑ i, a n i = t (p n) := by
      calc
        _ = ∑ i : (U (p n)), (i : ℕ) := (e n).toEquiv.sum_comp (fun i => i.val)
        _ = ∑ x ∈ U (p n), x := by simpa only [Finset.attach_eq_univ] using (Finset.sum_attach (U (p n)) (fun x : ℕ => x))
        _ = _ := hsum _
    obtain ⟨q,hq,hdis,hsp,hEsc⟩ := sparse_columns_with_escape a hi g
    let B (i : Fin j.val) := Set.range (fun n => a (q n) i)
    refine ⟨j.val,by omega,B,?_,hdis,hsp,?_,?_⟩
    · rintro i _ ⟨n,rfl⟩
      exact hU (p (q n)) _ (e _ i).property
    · intro i
      rcases hEsc i with ⟨c, hc⟩ | infl
      · left
        refine ⟨c,?_⟩
        ext x
        simp [B,hc]
      · right
        intro N
        obtain ⟨r,hr⟩ := (tendsto_atTop.mp infl (N+1)).exists
        exact ⟨a (q r) i, by omega, ⟨r,rfl⟩⟩
    · intro D N
      have ev (i : Fin j.val) : ∀ᶠ r : ℕ in atTop,
          (∃ c, B i = {c}) ∨ D ≤ a (q r) i := by
        rcases hEsc i with ⟨c,hc⟩|hinf
        · have hc' : B i = {c} := by
            ext x
            simp [B,hc]
          exact Eventually.of_forall fun _ => Or.inl ⟨c,hc'⟩
        · exact (tendsto_atTop.mp hinf D).mono fun _ hh => Or.inr hh
      obtain ⟨r,hr,hr'⟩ := ((Filter.eventually_all.2 ev).and
        (eventually_gt_atTop N)).exists
      have high := (ht.comp (hp.comp hq)).id_le r
      refine ⟨t (p (q r)), ?_, (hTs _).1,?_⟩
      · change r ≤ t (p (q r)) at high
        omega
      · exact ⟨a (q r),fun i => ⟨⟨r,rfl⟩,hr i⟩,hasSum _⟩

theorem anchored_to_trace {A T : Set ℕ} {h : ℕ} {g : ℕ → ℕ}
    (H : AnchoredTraceAt A h T g) : TraceAt A h T g := by
  obtain ⟨k,hk,B,hA,hD,hS,_,hU⟩ := H
  refine ⟨k,hk,B,hA,hD,hS,?_⟩
  intro N
  obtain ⟨n,hn,hTn,f,hf,hs⟩ := hU 0 N
  exact ⟨n,hn,hTn,f,fun i => (hf i).1,hs⟩

private theorem extract_trace {A : Set ℕ} {h : ℕ} {T : Set ℕ}
    (H : Unbounded (T ∩ hit A h)) (g : ℕ → ℕ) : TraceAt A h T g :=
  anchored_to_trace (extract_anchored_trace H g)

private theorem box_subset_hit {A : Set ℕ} {k h : ℕ} {B : Fin k → Set ℕ}
    (hk : k ≤ h) (hBA : ∀ i, B i ⊆ A) (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    box B ⊆ hit A h := by
    classical
    rintro n ⟨f,hf,sm⟩
    have inj : Function.Injective f := by
      intro i j e
      by_contra hij
      exact (Set.disjoint_left.mp (hd i j hij)) (hf i) (e ▸ hf j)
    refine ⟨Finset.univ.image f,?_,?_,?_⟩
    · rintro _ hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hBA i (hf i)
    · exact le_trans Finset.card_image_le (by simpa using hk)
    · simpa [Finset.sum_image (s:=Finset.univ) (f:=fun x => x)
        (fun _ _ _ _ eq => inj eq)] using sm


/-- Hereditary trace extraction: no basis hypothesis, and the whole ideal of
 sets orthogonal to rectangular sumsets is identified, not just cofiniteness. -/
theorem unbounded_hits_iff_trace {A T : Set ℕ} {h : ℕ} (g : ℕ → ℕ) :
    Unbounded (T ∩ hit A h) ↔ TraceAt A h T g := by
  refine ⟨fun H => extract_trace H g, ?_⟩
  rintro ⟨k,hk,B,hBA,hd,_,H⟩ N
  obtain ⟨n,hn,ht,hb⟩ := H N
  exact ⟨n,hn,ht,box_subset_hit hk hBA hd hb⟩

theorem unbounded_hits_iff_anchored_trace {A T : Set ℕ} {h : ℕ} (g : ℕ → ℕ) :
    Unbounded (T ∩ hit A h) ↔ AnchoredTraceAt A h T g :=
  ⟨fun H => extract_anchored_trace H g,
    fun H => (unbounded_hits_iff_trace g).mpr (anchored_to_trace H)⟩

/-- On global target tests, the orthogonal ideal of the ordinary boxes consists
 exactly of families with only a bounded set of rank-h restricted hits. -/
theorem orthogonal_ideal {A T : Set ℕ} {h : ℕ} (g : ℕ → ℕ) :
    (¬ TraceAt A h T g) ↔ ∃ N, ∀ n > N, n ∈ T → n ∉ hit A h := by
  rw [← unbounded_hits_iff_trace g]
  unfold Unbounded
  push Not
  simp [Set.mem_inter_iff, not_and]

/-- Every escaping set has a genuinely global ordinary sumset trace on disjoint,
arbitrarily widely spaced subcollections. Conversely failure gives an escaping
set orthogonal to every such rectangular sumset. -/
theorem restricted_iff_sparse_trace (A : Set ℕ) (h : ℕ) :
    HasRestrictedOrder A h ↔ TraceProperty A h := by
  classical
  constructor
  · intro H T hT g
    rw [HasRestrictedOrder, eventually_atTop] at H
    obtain ⟨M,H⟩ := H
    apply (unbounded_hits_iff_trace g).mp
    intro N
    obtain ⟨n,hn,hTn⟩ := hT (max N M)
    exact ⟨n,by omega,hTn,H n (by omega)⟩
  · intro H
    rw [HasRestrictedOrder, eventually_atTop]
    by_contra! ne
    let T := (hit A h)ᶜ
    have unb : Unbounded T := by
      intro N
      obtain ⟨n, hn, ne⟩ := ne (N+1)
      refine ⟨n,by omega,?_⟩
      change ¬ ∃ S : Finset ℕ, _
      push Not
      exact ne
    obtain ⟨n,_,hnT,hnA⟩ := (unbounded_hits_iff_trace id).mpr (H T unb id) 0
    exact hnT hnA

private theorem restricted_implies_ordinary {A : Set ℕ} {k : ℕ} (H : HasRestrictedOrder A k) :
    HasOrder A k := by
  apply ordinary_iff_list.mpr
  obtain ⟨N,H⟩ := restricted_iff_list.mp H
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨xs, _, ha, sm, len⟩ := H n hn
  exact ⟨xs,ha,sm,len⟩

private theorem restrictedOrder_le {A : Set ℕ} {k : ℕ} (H : HasRestrictedOrder A k) :
    restrictedOrder A ≤ (k : ℕ∞) :=
  iInf_le_of_le k (iInf_le_of_le H le_rfl)

private theorem least_le_ranks (A : Set ℕ) (h : ℕ) (ord : basisOrder A = (h : ℕ∞))
    {k : ℕ} (H : HasRestrictedOrder A k) : h ≤ k := by
  apply ENat.natCast_le_natCast.mp
  rw [← ord]
  exact iInf_le_of_le k (iInf_le_of_le (restricted_implies_ordinary H) le_rfl)

private theorem least_restricted (A : Set ℕ) {h : ℕ} (ord : basisOrder A = (h : ℕ∞)) :
    restrictedOrder A = basisOrder A ↔ HasRestrictedOrder A h := by
  classical
  constructor
  · intro he
    have nt : restrictedOrder A ≠ ⊤ := by rw [he,ord]; exact ENat.natCast_ne_top _
    have ex := (restrictedOrder_ne_top_iff A).mp nt
    let m := Nat.find ex
    have hm : HasRestrictedOrder A m := Nat.find_spec ex
    have low : (m : ℕ∞) ≤ restrictedOrder A := by
      apply le_iInf; intro k; apply le_iInf; intro hk
      exact ENat.natCast_le_natCast.mpr (Nat.find_min' ex hk)
    rw [he,ord] at low
    have mh := ENat.natCast_le_natCast.mp low
    exact (le_antisymm mh (least_le_ranks A h ord hm)) ▸ hm
  · intro hh
    rw [ord]
    refine le_antisymm (restrictedOrder_le hh) ?_
    apply le_iInf; intro k; apply le_iInf; intro hk
    exact ENat.natCast_le_natCast.mpr (least_le_ranks A h ord hk)

/-- All finite exact ordinary orders, with no other hypothesis on the basis. -/
theorem equal_orders_iff_sparse_trace {A : Set ℕ} {h : ℕ}
    (ord : basisOrder A = (h : ℕ∞)) :
    restrictedOrder A = basisOrder A ↔ TraceProperty A h :=
  (least_restricted A ord).trans (restricted_iff_sparse_trace A h)

/-- A single family of columns per probe works even after imposing every
    cutoff on the moving summands; its finite anchors never change. -/
theorem equal_orders_iff_anchored_trace {A : Set ℕ} {h : ℕ}
    (ord : basisOrder A = (h : ℕ∞)) :
    restrictedOrder A = basisOrder A ↔ AnchoredTraceProperty A h := by
  rw [equal_orders_iff_sparse_trace ord]
  constructor
  · intro H T ht g
    exact (unbounded_hits_iff_anchored_trace g).mp
      ((unbounded_hits_iff_trace g).mpr (H T ht g))
  · intro H T ht g
    exact anchored_to_trace (H T ht g)

#print axioms sparse_columns
#print axioms restricted_iff_sparse_trace
#print axioms equal_orders_iff_sparse_trace
#print axioms equal_orders_iff_anchored_trace
end Erdos338.SparseTrace
