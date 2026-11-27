import Std

/-!
# Truncated blockers and virtual supports

A support is a predicate on arbitrary labels (extensional sets). `Small A k`
means that at most `k` labels suffice to enumerate `A`; no enumeration of the
ground type is required. Thus the results apply in particular to the finite
hypergraphs at each integer weight of the Erdős #338 draft. The definitions
are independent of additive representations.
-/
namespace Erdos338.Blockers
universe u
abbrev Support (α : Type u) := α → Prop
abbrev Family (α : Type u) := Support α → Prop
variable {α : Type u}

def Sub (A B : Support α) := ∀ ⦃x⦄, A x → B x
def Union (A B : Support α) : Support α := fun x => A x ∨ B x
def Disj (A B : Support α) := ∀ ⦃x⦄, A x → B x → False
def Small (A : Support α) (k : Nat) := ∃ xs : List α, xs.length ≤ k ∧ ∀ ⦃x⦄, A x → x ∈ xs
def Rank (F : Family α) (k : Nat) := ∀ ⦃S⦄, F S → Small S k
def Hits (F : Family α) (E : Support α) := ∀ ⦃S⦄, F S → ∃ x, S x ∧ E x
def Avoid (F : Family α) (E : Support α) := ∃ S, F S ∧ Disj S E
def Minimal (P : Family α) (S : Support α) :=
  P S ∧ ∀ ⦃T⦄, Sub T S → P T → Sub S T
def Block (t : Nat) (F : Family α) : Family α := fun E => Small E t ∧ Minimal (Hits F) E
def Virtual (k t : Nat) (F : Family α) : Family α := Block k (Block t F)
def SameQueries (t : Nat) (F G : Family α) :=
  ∀ E, Small E t → (Avoid F E ↔ Avoid G E)

theorem small_sub {S T : Support α} {k} (ST : Sub S T) (tk : Small T k) : Small S k := by
  obtain ⟨xs, h, cov⟩ := tk
  exact ⟨xs, h, fun _ hs => cov (ST hs)⟩

theorem small_union {A B : Support α} {k t} (ak : Small A k) (bt : Small B t) :
    Small (Union A B) (k+t) := by
  obtain ⟨xs,hx,xmem⟩ := ak
  obtain ⟨ys,hy,ymem⟩ := bt
  refine ⟨xs++ys, by simp; omega, ?_⟩
  intro x h
  rcases h with h|h
  · exact List.mem_append_left ys (xmem h)
  · exact List.mem_append_right xs (ymem h)

theorem disj_comm {A B : Support α} : Disj A B ↔ Disj B A :=
  ⟨fun h _ b a => h a b, fun h _ a b => h b a⟩

theorem disj_sub {A B S T : Support α} (a : Sub A S) (b : Sub B T) (h : Disj S T) :
    Disj A B := fun _ ha hb => h (a ha) (b hb)

theorem avoid_iff_not_hits {F : Family α} {E} : Avoid F E ↔ ¬ Hits F E := by
  classical
  constructor
  · rintro ⟨S,hS,hs⟩ hh
    obtain ⟨x,hx,he⟩ := hh hS
    exact hs hx he
  · intro h
    apply Classical.byContradiction
    intro no
    apply h
    intro S hS
    apply Classical.byContradiction
    intro bad
    exact no ⟨S,hS,fun x hs he => bad ⟨x,hs,he⟩⟩

/-- Finite descent within a small support; `P` need not be monotone. -/
theorem contains_minimal (P : Family α) {k} (S : Support α) (sk : Small S k) (hS : P S) :
    ∃ T, Sub T S ∧ Minimal P T := by
  classical
  induction k using Nat.strongRecOn generalizing S with
  | ind k ih =>
    by_cases ismin : Minimal P S
    · exact ⟨S, fun _ x => x, ismin⟩
    · have smaller : ∃ T, Sub T S ∧ P T ∧ ¬ Sub S T := by
        apply Classical.byContradiction
        intro hn
        apply ismin
        refine ⟨hS,?_⟩
        intro T s p
        exact Classical.byContradiction (fun n => hn ⟨T,s,p,n⟩)
      obtain ⟨T,ts,pt,notst⟩ := smaller
      have missing : ∃ x, S x ∧ ¬ T x := by
        apply Classical.byContradiction
        intro none
        exact notst (fun x sx => Classical.byContradiction (fun nt => none ⟨x,sx,nt⟩))
      obtain ⟨x,sx,nt⟩ := missing
      obtain ⟨xs,len,cov⟩ := sk
      have xm := cov sx
      have xspos : xs.length > 0 := List.length_pos_of_mem xm
      have lt : (xs.erase x).length < k := by rw [List.length_erase_of_mem xm]; omega
      have tk : Small T (xs.erase x).length := by
        refine ⟨xs.erase x, Nat.le_refl _, ?_⟩
        intro y ty
        have ne : y ≠ x := fun eq => nt (eq ▸ ty)
        exact (List.mem_erase_of_ne ne).mpr (cov (ts ty))
      obtain ⟨U,ut,pu⟩ := ih _ lt T tk pt
      exact ⟨U,fun _ hu => ts (ut hu),pu⟩

theorem support_contains_virtual {F : Family α} {k t : Nat} (rk : Rank F k) {S} (mem : F S) :
    ∃ X, Virtual k t F X ∧ Sub X S := by
  have hs : Hits (Block t F) S := by
    intro E he
    obtain ⟨x,hx,hy⟩ := he.2.1 mem
    exact ⟨x,hy,hx⟩
  obtain ⟨X,sub,m⟩ := contains_minimal _ S (rk mem) hs
  exact ⟨X,⟨small_sub sub (rk mem),m⟩,sub⟩

/-- Lemma 6.1, equivalence (avoid). -/
theorem exact_interface {F : Family α} {k t} (rk : Rank F k) :
    SameQueries t F (Virtual k t F) := by
  classical
  intro E bound
  constructor
  · rintro ⟨S,hs,ds⟩
    obtain ⟨X,vx,sub⟩ := support_contains_virtual rk hs (t:=t)
    exact ⟨X,vx,fun _ hx he => ds (sub hx) he⟩
  · rintro ⟨X,vx,dis⟩
    apply avoid_iff_not_hits.mpr
    intro hits
    obtain ⟨T,te,minT⟩ := contains_minimal _ E bound hits
    have dT : Block t F T := ⟨small_sub te bound,minT⟩
    obtain ⟨x,tx,xx⟩ := vx.2.1 dT
    exact dis xx (te tx)

theorem block_eq_of_queries {F G : Family α} {t} (q : SameQueries t F G) :
    Block t F = Block t G := by
  classical
  have heq : ∀ S : Support α, Small S t → (Hits F S ↔ Hits G S) := by
    intro S hs
    have h := q S hs
    rw [avoid_iff_not_hits,avoid_iff_not_hits] at h
    exact ⟨fun f => Classical.byContradiction (fun ng => (h.mpr ng) f),
           fun g => Classical.byContradiction (fun nf => (h.mp nf) g)⟩
  funext E
  apply propext
  constructor
  · rintro ⟨small,hits,minimal⟩
    exact ⟨small,(heq E small).mp hits,
      fun T sub th => minimal sub ((heq T (small_sub sub small)).mpr th)⟩
  · rintro ⟨small,hits,minimal⟩
    exact ⟨small,(heq E small).mpr hits,
      fun T sub th => minimal sub ((heq T (small_sub sub small)).mp th)⟩

theorem queries_iff_block_eq {F G : Family α} {t} :
    SameQueries t F G ↔ Block t F = Block t G := by
  classical
  refine ⟨block_eq_of_queries,?_⟩
  intro he E bound
  have characterization (K : Family α) : Hits K E ↔ ∃ T, Block t K T ∧ Sub T E := by
    constructor
    · intro hits
      obtain ⟨T,te,minT⟩ := contains_minimal _ E bound hits
      exact ⟨T,⟨small_sub te bound,minT⟩,te⟩
    · rintro ⟨T,ht,te⟩ S hs
      obtain ⟨x,hx,tx⟩ := ht.2.1 hs
      exact ⟨x,hx,te tx⟩
  rw [avoid_iff_not_hits,avoid_iff_not_hits,characterization F,he,←characterization G]

theorem block_virtual {F : Family α} {k t} (rk : Rank F k) :
    Block t (Virtual k t F) = Block t F :=
  (block_eq_of_queries (exact_interface rk)).symm

theorem virtual_idempotent {F : Family α} {k t} (rk : Rank F k) :
    Virtual k t (Virtual k t F) = Virtual k t F :=
  congrArg (Block k) (block_virtual rk)

theorem queries_iff_virtual_eq {F G : Family α} {k t} (rf : Rank F k) (rg : Rank G k) :
    SameQueries t F G ↔ Virtual k t F = Virtual k t G := by
  constructor
  · exact fun h => congrArg (Block k) (block_eq_of_queries h)
  · intro h
    apply queries_iff_block_eq.mpr
    rw [← block_virtual (t:=t) rf, ← block_virtual (t:=t) rg, h]

def Compatible (F G : Family α) (E : Support α) :=
  ∃ S T, F S ∧ G T ∧ Disj S T ∧ Disj S E ∧ Disj T E

/-- The two-stage lifting also applies to arbitrary deletion-equivalent abstractions,
provided the retained supports respect their rank bounds. -/
theorem composition_of_queries {F G U V : Family α} {p q e}
    (f : Rank F p) (g : Rank G q) (u : Rank U p) (v : Rank V q)
    (fu : SameQueries (q+e) F U) (gv : SameQueries (p+e) G V) {E}
    (eb : Small E e) : Compatible F G E ↔ Compatible U V E := by
  let liftOne {F G U V : Family α} (f : Rank F p) (v : Rank V q)
      (fu : SameQueries (q+e) F U) (gv : SameQueries (p+e) G V) :
      Compatible U V E → Compatible F G E := by
    rintro ⟨X,Y,hx,hy,dxy,dxE,dyE⟩
    have ey : Small (Union Y E) (q+e) := small_union (v hy) eb
    obtain ⟨S,hs,ds⟩ := (fu _ ey).mpr ⟨X,hx, fun z x h => h.elim (dxy x) (dxE x)⟩
    have es : Small (Union S E) (p+e) := small_union (f hs) eb
    obtain ⟨T,ht,dt⟩ := (gv _ es).mpr ⟨Y,hy, fun z y h => h.elim (fun s => ds s (Or.inl y)) (dyE y)⟩
    exact ⟨S,T,hs,ht,fun _ s t => dt t (Or.inl s),
      fun _ s e => ds s (Or.inr e), fun _ t e => dt t (Or.inr e)⟩
  exact ⟨liftOne u g (fun E he => (fu E he).symm) (fun E he => (gv E he).symm),
         liftOne f v fu gv⟩

/-- ZIP Lemma 6.2, with no arithmetic assumptions. -/
theorem budgeted_composition {F G : Family α} {p q e}
    (f : Rank F p) (g : Rank G q) {E} (eb : Small E e) :
    Compatible F G E ↔ Compatible (Virtual p (q+e) F) (Virtual q (p+e) G) E :=
  composition_of_queries f g (fun _ hx => hx.1) (fun _ hy => hy.1)
    (exact_interface f) (exact_interface g) eb


section Sizes
def Empty : Support α := fun _ => False
def Insert (x : α) (S : Support α) : Support α := fun y => y = x ∨ S y
def Remove (x : α) (S : Support α) : Support α := fun y => y ≠ x ∧ S y
def Miss (x : α) (F : Family α) : Family α := fun S => F S ∧ ¬ S x

theorem disj_empty (S : Support α) : Disj S Empty := fun _ _ h => h.elim

theorem small_empty : Small (Empty : Support α) 0 :=
  ⟨[], Nat.le_refl _, fun _ h => h.elim⟩

theorem small_zero {S : Support α} (h : Small S 0) : S = Empty := by
  funext x
  apply propext
  refine ⟨fun hx => ?_,fun he => he.elim⟩
  obtain ⟨xs,len,cov⟩ := h
  have hp := List.length_pos_of_mem (cov hx)
  omega

theorem small_remove {E : Support α} {x t} (xe : E x) (h : Small E (t+1)) :
    Small (Remove x E) t := by
  classical
  obtain ⟨xs,len,cov⟩ := h
  have xm := cov xe
  refine ⟨xs.erase x, by rw [List.length_erase_of_mem xm]; omega, ?_⟩
  intro y hy
  exact (List.mem_erase_of_ne hy.1).mpr (cov hy.2)

/-- Every label of a minimal transversal belongs to some input edge. -/
theorem label_from_edge {F : Family α} {E x} (m : Minimal (Hits F) E) (xe : E x) :
    ∃ S, F S ∧ S x := by
  classical
  apply Classical.byContradiction
  intro no
  have hh : Hits F (Remove x E) := by
    intro S hs
    obtain ⟨y,sy,ey⟩ := m.1 hs
    exact ⟨y,sy,fun eyx => no ⟨S,hs,eyx ▸ sy⟩,ey⟩
  exact (m.2 (T:=Remove x E) (fun _ hy => hy.2) hh xe).1 rfl

theorem blocker_remove {F : Family α} {E : Support α} {x : α} {t}
    (h : Block (t+1) F E) (xe : E x) : Block t (Miss x F) (Remove x E) := by
  classical
  refine ⟨small_remove xe h.1, ?_, ?_⟩
  · intro S hs
    obtain ⟨y,sy,ey⟩ := h.2.1 hs.1
    exact ⟨y,sy,fun eq => hs.2 (eq ▸ sy),ey⟩
  · intro T ts hitsT y rem
    have ins_in : Sub (Insert x T) E := by
      rintro z (rfl|zt)
      · exact xe
      · exact (ts zt).2
    have ins_hits : Hits F (Insert x T) := by
      intro S fs
      by_cases sx : S x
      · exact ⟨x,sx,Or.inl rfl⟩
      · obtain ⟨z,sz,tz⟩ := hitsT ⟨fs,sx⟩
        exact ⟨z,sz,Or.inr tz⟩
    exact (h.2.2 ins_in ins_hits rem.2).resolve_left rem.1

private theorem insert_remove {S : Support α} {x} (sx : S x) : Insert x (Remove x S) = S := by
  classical
  funext y
  apply propext
  constructor
  · rintro (rfl|⟨_,sy⟩)
    · exact sx
    · exact sy
  · intro sy
    by_cases he : y=x
    · exact Or.inl he
    · exact Or.inr ⟨he,sy⟩

private theorem bounded_flatMap {β : Type u} (xs : List α) (L : α → List β) {k}
    (h : ∀ a, (L a).length ≤ k) : (xs.flatMap L).length ≤ xs.length * k := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.succ_mul]
    have hy := h y
    omega

/-- The bounded-branching tree, proved on deletion budget. No decidability
assumption and no ground-universe size enters the count. -/
theorem blocker_count (F : Family α) {k} (rk : Rank F k) (pos : 0 < k) (t : Nat) :
    Small (Block t F) (k^t) := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨[Empty],by simp,?_⟩
    intro S hs
    simp [small_zero hs.1]
  | succ t ih =>
    by_cases any : ∃ S, F S
    · obtain ⟨S,fs⟩ := any
      obtain ⟨xs,len,cov⟩ := rk fs
      have branch (x : α) := ih (Miss x F) (fun _ hs => rk hs.1)
      let L (x : α) : List (Support α) := Classical.choose (branch x)
      have lcov (x : α) := Classical.choose_spec (branch x)
      let children := fun x => (L x).map (Insert x)
      have cb : ∀ x, (children x).length ≤ k^t := by
        intro x
        simpa [children,L] using (lcov x).1
      refine ⟨xs.flatMap children,?_,?_⟩
      · calc
          (xs.flatMap children).length ≤ xs.length * k^t := bounded_flatMap xs children cb
          _ ≤ k * k^t := Nat.mul_le_mul_right _ len
          _ = k^(t+1) := by rw [Nat.pow_succ, Nat.mul_comm]
      · intro E eh
        obtain ⟨x,sx,ex⟩ := eh.2.1 fs
        apply List.mem_flatMap.mpr
        refine ⟨x,cov sx,List.mem_map.mpr ?_⟩
        exact ⟨Remove x E,(lcov x).2 (blocker_remove eh ex),insert_remove ex⟩
    · have pospow : 0 < k^(t+1) := Nat.pow_pos pos
      refine ⟨[Empty], by simp only [List.length_singleton]; omega, ?_⟩
      intro E eh
      have h0 : Hits F (Empty : Support α) := fun S s => False.elim (any ⟨S,s⟩)
      have sub : Sub E Empty := eh.2.2 (fun _ he => he.elim) h0
      have eq : E = Empty := funext (fun _ => propext ⟨fun he => sub he, fun h0 => h0.elim⟩)
      simp [eq]

/-- Both numerical bounds in Lemma 6.1(1) are cardinal bounds on sets: `Small`
permits a covering list but does not count repeated representations as distinct. -/
theorem virtual_count (F : Family α) {k t} (tpos : 0 < t) :
    Small (Virtual k t F) (t^k) :=
  blocker_count (Block t F) (fun _ h => h.1) tpos k

def Labels (F : Family α) : Support α := fun x => ∃ S, F S ∧ S x

theorem labels_count {F : Family α} {N k} (fc : Small F N) (rk : Rank F k) :
    Small (Labels F) (k*N) := by
  classical
  obtain ⟨xs,len,cov⟩ := fc
  have choose (S : Support α) : ∃ ys : List α, ys.length ≤ k ∧
      (F S → ∀ ⦃x⦄, S x → x ∈ ys) := by
    by_cases h : F S
    · obtain ⟨ys,lb,hh⟩ := rk h
      exact ⟨ys,lb,fun _ _ sx => hh sx⟩
    · exact ⟨[], Nat.zero_le _,fun fs => (h fs).elim⟩
  let L (S : Support α) := Classical.choose (choose S)
  have spec (S : Support α) := Classical.choose_spec (choose S)
  refine ⟨xs.flatMap L,?_,?_⟩
  · calc
      (xs.flatMap L).length ≤ xs.length*k := bounded_flatMap xs L (fun S => (spec S).1)
      _ ≤ N*k := Nat.mul_le_mul_right _ len
      _ = k*N := Nat.mul_comm _ _
  · rintro x ⟨S,fs,sx⟩
    exact List.mem_flatMap.mpr ⟨S,cov fs,(spec S).2 fs sx⟩

theorem virtual_label_count (F : Family α) {k t} (rk : Rank F k)
    (kp : 0 < k) (tp : 0 < t) :
    Small (Labels (Virtual k t F)) (min (t*k^t) (k*t^k)) := by
  have dBound := labels_count (blocker_count F rk kp t) (fun _ h => h.1)
  have vBound := labels_count (virtual_count F (k:=k) tp) (fun _ h => h.1)
  have subset : Sub (Labels (Virtual k t F)) (Labels (Block t F)) := by
    rintro x ⟨S,hS,sx⟩
    exact label_from_edge hS.2 sx
  rcases Nat.le_total (t*k^t) (k*t^k) with a|a
  · rw [Nat.min_eq_left a]
    exact small_sub subset dBound
  · rw [Nat.min_eq_right a]
    exact vBound

end Sizes


section Weighted
abbrev Fiber (α : Type u) := Nat → Family α

/-- Weighted product of genuinely disjoint supports. -/
def Join (F G : Fiber α) : Fiber α := fun n S =>
  ∃ i j X Y, i+j=n ∧ F i X ∧ G j Y ∧ Disj X Y ∧ Union X Y=S

theorem join_rank {F G : Fiber α} {p q} (f : ∀ n, Rank (F n) p) (g : ∀ n, Rank (G n) q)
    (n) : Rank (Join F G n) (p+q) := by
  rintro S ⟨i,j,X,Y,_,hx,hy,_,rfl⟩
  exact small_union (f i hx) (g j hy)

theorem avoid_join_iff (F G : Fiber α) (n E) :
    Avoid (Join F G n) E ↔ ∃ i j, i+j=n ∧ Compatible (F i) (G j) E := by
  constructor
  · rintro ⟨_,⟨i,j,X,Y,ij,hx,hy,dis,rfl⟩,away⟩
    exact ⟨i,j,ij,X,Y,hx,hy,dis,fun _ x => away (Or.inl x),fun _ y => away (Or.inr y)⟩
  · rintro ⟨i,j,ij,X,Y,hx,hy,dis,dx,dy⟩
    exact ⟨_,⟨i,j,X,Y,ij,hx,hy,dis,rfl⟩,fun _ h => h.elim (fun x => dx x) (fun y => dy y)⟩

theorem weighted_queries {F G U V : Fiber α} {p q e}
    (f : ∀ n, Rank (F n) p) (g : ∀ n, Rank (G n) q)
    (u : ∀ n, Rank (U n) p) (v : ∀ n, Rank (V n) q)
    (fu : ∀ n, SameQueries (q+e) (F n) (U n)) (gv : ∀ n, SameQueries (p+e) (G n) (V n))
    (n) : SameQueries e (Join F G n) (Join U V n) := by
  intro E eb
  rw [avoid_join_iff,avoid_join_iff]
  constructor
  · rintro ⟨i,j,ij,comp⟩
    exact ⟨i,j,ij,(composition_of_queries (f i) (g j) (u i) (v j) (fu i) (gv j) eb).mp comp⟩
  · rintro ⟨i,j,ij,comp⟩
    exact ⟨i,j,ij,(composition_of_queries (f i) (g j) (u i) (v j) (fu i) (gv j) eb).mpr comp⟩

/-- Restricted support, allowing repetitions *only* outside B. -/
def fringeSupport (B : Nat → Prop) (xs : List Nat) : Support Nat := fun x => B x ∧ x ∈ xs
def FringeDistinct (B : Nat → Prop) (xs : List Nat) :=
  xs.Pairwise (fun x y => x = y → ¬ B x)

/-- Concrete bridge to the repeat condition of arithmetic repair. -/
theorem fringeDistinct_iff_counts (B : Nat → Prop) (xs : List Nat) :
    FringeDistinct B xs ↔ ∀ x, B x → xs.count x ≤ 1 := by
  induction xs with
  | nil => simp [FringeDistinct]
  | cons a as ih =>
    change (a::as).Pairwise _ ↔ _
    rw [List.pairwise_cons]
    constructor
    · rintro ⟨first,rest⟩ x bx
      by_cases eq : a=x
      · subst x
        have absent : a ∉ as := fun ha => first a ha rfl bx
        simp [List.count_eq_zero_of_not_mem absent]
      · rw [List.count_cons_of_ne eq]
        exact ih.mp rest x bx
    · intro all
      constructor
      · intro y hy eq ba
        subst y
        have lim := all a ba
        have pos := List.count_pos_iff.mpr hy
        simp only [List.count_cons_self] at lim
        omega
      · apply ih.mpr
        intro x bx
        have lim := all x bx
        by_cases eq : a=x
        · subst x; simp only [List.count_cons_self] at lim; omega
        · simpa [List.count_cons_of_ne eq] using lim

theorem fringeDistinct_of_nodup (B : Nat → Prop) {xs : List Nat} (dist : xs.Nodup) :
    FringeDistinct B xs :=
  dist.imp (fun ne eq => (ne eq).elim)

def Actual (A B : Nat → Prop) (k : Nat) : Fiber Nat := fun n S =>
  ∃ xs : List Nat, xs.length ≤ k ∧ xs.sum = n ∧ (∀ x ∈ xs, A x) ∧
    FringeDistinct B xs ∧ fringeSupport B xs = S

theorem actual_rank (A B : Nat → Prop) (k n) : Rank (Actual A B k n) k := by
  rintro S ⟨xs,len,_,_,_,rfl⟩
  exact ⟨xs,len,fun _ h => h.2⟩

private theorem sum_append_nat (xs ys : List Nat) : (xs++ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih,Nat.add_assoc]

private theorem fringe_append (B : Nat → Prop) (xs ys : List Nat) :
    Union (fringeSupport B xs) (fringeSupport B ys) = fringeSupport B (xs++ys) := by
  funext x
  apply propext
  constructor
  · rintro (⟨b,xx⟩|⟨b,yy⟩)
    · exact ⟨b,List.mem_append_left ys xx⟩
    · exact ⟨b,List.mem_append_right xs yy⟩
  · rintro ⟨b,m⟩
    exact (List.mem_append.mp m).elim (fun l => Or.inl ⟨b,l⟩) (fun r => Or.inr ⟨b,r⟩)

theorem actual_split (A B : Nat → Prop) (p q) :
    Actual A B (p+q) = Join (Actual A B p) (Actual A B q) := by
  funext n S
  apply propext
  constructor
  · rintro ⟨xs,hl,wt,ok,fr,rfl⟩
    let l := xs.take p
    let r := xs.drop p
    have cat : l++r=xs := List.take_append_drop p xs
    have cut := List.pairwise_append.mp (cat ▸ fr : FringeDistinct B (l++r))
    refine ⟨l.sum,r.sum,fringeSupport B l,fringeSupport B r, by rw [← sum_append_nat,cat,wt], ?_, ?_, ?_, ?_⟩
    · exact ⟨l, by simpa [l,List.length_take] using Nat.min_le_left p xs.length,rfl,
        fun a m => ok a (cat ▸ List.mem_append_left r m),cut.1,rfl⟩
    · exact ⟨r,by dsimp [r]; rw [List.length_drop]; omega,rfl,
        fun a m => ok a (cat ▸ List.mem_append_right l m),cut.2.1,rfl⟩
    · exact fun x xl xr => cut.2.2 x xl.2 x xr.2 rfl xl.1
    · rw [fringe_append,cat]
  · rintro ⟨i,j,L,R,ij,⟨l,hl,wl,la,ld,rfl⟩,⟨r,hr,wr,ra,rd,rfl⟩,dis,rfl⟩
    refine ⟨l++r,by simp; omega, by rw [sum_append_nat,wl,wr,ij], ?_, ?_,(fringe_append B l r).symm⟩
    · intro a h
      exact (List.mem_append.mp h).elim (la a) (ra a)
    · apply List.pairwise_append.mpr
      exact ⟨ld,rd,fun a aa b bb eq ba => dis ⟨ba,aa⟩ ⟨ba,eq ▸ bb⟩⟩

/-- The raw starting interface at rank one, requiring just membership. `Empty`
at weight 0 is the unused slot; good summands contribute no fringe labels. -/
def Atom (A B : Nat → Prop) : Fiber Nat := fun n S =>
  (n = 0 ∧ S = Empty) ∨ (A n ∧ S = fun x => B x ∧ x=n)

theorem actual_one (A B : Nat → Prop) : Actual A B 1 = Atom A B := by
  funext n S
  apply propext
  constructor
  · rintro ⟨xs,hl,wt,ok,_,rfl⟩
    cases xs with
    | nil =>
      exact Or.inl ⟨wt.symm,funext (fun x => propext ⟨fun h => by simpa using h.2, fun h => h.elim⟩)⟩
    | cons a tail =>
      cases tail with
      | nil =>
        simp at wt
        subst n
        exact Or.inr ⟨ok a (by simp),funext (fun x => propext (by simp [fringeSupport]))⟩
      | cons b rest => simp at hl
  · rintro (⟨rfl,rfl⟩|⟨an,rfl⟩)
    · exact ⟨[],by simp,rfl,by simp,by simp [FringeDistinct],funext (fun x =>
        propext ⟨fun h => by simpa using h.2,fun h => h.elim⟩)⟩
    · exact ⟨[n],by simp,by simp,by simpa using an,by simp [FringeDistinct],
        funext (fun x => propext (by simp [fringeSupport]))⟩

inductive Shape
| leaf | node (left right : Shape)
deriving Repr

def leaves : Shape → Nat
  | .leaf => 1
  | .node l r => leaves l + leaves r

/-- Recursion with arbitrary binary splits (the balanced splits in the text are one choice).
We apply the virtual constructor to `Atom` at leaves as well. -/
def summary (A B : Nat → Prop) : Shape → Nat → Fiber Nat
  | .leaf,t,n => Virtual 1 t (Atom A B n)
  | .node l r,t,n => Virtual (leaves l+leaves r) t
      (Join (summary A B l (leaves r+t)) (summary A B r (leaves l+t)) n)

theorem summary_canonical (A B : Nat → Prop) (tree : Shape) (t n) :
    summary A B tree t n = Virtual (leaves tree) t (Actual A B (leaves tree) n) := by
  induction tree generalizing t n with
  | leaf => simp [summary,leaves,actual_one]
  | node l r il ir =>
    simp only [summary,leaves]
    rw [actual_split A B (leaves l) (leaves r)]
    apply Eq.symm
    apply (queries_iff_virtual_eq ?_ ?_).mp
    · apply weighted_queries (actual_rank A B _) (actual_rank A B _)
        (fun i => ?_) (fun j => ?_) (fun i => ?_) (fun j => ?_)
      · rw [il]; exact fun _ v => v.1
      · rw [ir]; exact fun _ v => v.1
      · rw [il]; exact exact_interface (actual_rank A B _ i)
      · rw [ir]; exact exact_interface (actual_rank A B _ j)
    · exact join_rank (actual_rank A B _) (actual_rank A B _) n
    · apply join_rank
      · intro i; rw [il]; exact fun _ v => v.1
      · intro j; rw [ir]; exact fun _ v => v.1

/-- At positive deletion budget the virtual interface fixes both absent and
single-witness fibers (the rank-one starting states of the source theorem). -/
theorem virtual_unique {F : Family α} {k t} (rk : Rank F k) (pos : 0 < t)
    (uniq : ∀ S T, F S → F T → S=T) : Virtual k t F = F := by
  classical
  have eq_of {X S} (vx : Virtual k t F X) (fs : F S) : X=S := by
    have s_in_x : Sub S X := by
      intro a sa
      by_cases yes : X a
      · exact yes
      · let D : Support α := fun y => y=a
        have bound : Small D t := ⟨[a],by simp only [List.length_singleton]; omega,fun _ h => List.mem_singleton.mpr h⟩
        have av : Avoid (Virtual k t F) D :=
          ⟨X,vx,fun y xy (d : y=a) => yes (d ▸ xy)⟩
        obtain ⟨T,ft,dis⟩ := (exact_interface rk D bound).mpr av
        have es := uniq S T fs ft
        exact False.elim (dis (es ▸ sa) rfl)
    obtain ⟨Y,vy,ys⟩ := support_contains_virtual (t:=t) rk fs
    have yx : Sub Y X := fun _ yy => s_in_x (ys yy)
    have xy := vx.2.2 yx vy.2.1
    exact funext (fun _ => propext ⟨fun xx => ys (xy xx),fun ss => s_in_x ss⟩)
  funext X
  apply propext
  constructor
  · intro vx
    have small : Small (Empty : Support α) t := ⟨[],Nat.zero_le _,fun _ h => h.elim⟩
    obtain ⟨S,fs,_⟩ := (exact_interface rk Empty small).mpr ⟨X,vx,disj_empty X⟩
    exact (eq_of vx fs).symm ▸ fs
  · intro fx
    obtain ⟨Y,vy,_⟩ := support_contains_virtual (t:=t) rk fx
    exact eq_of vy fx ▸ vy

theorem summary_leaf (A B : Nat → Prop) (positive : ¬ A 0) {t} (tp : 0<t) (n) :
    summary A B .leaf t n = Atom A B n := by
  refine virtual_unique ?_ tp ?_
  · rw [← actual_one A B]
    exact actual_rank A B 1 n
  · intro S T s a
    rcases s with ⟨z,s⟩|⟨an,s⟩ <;> rcases a with ⟨zz,u⟩|⟨aa,u⟩
    · exact s.trans u.symm
    · exact False.elim (positive (z ▸ aa))
    · exact False.elim (positive (zz ▸ an))
    · exact s.trans u.symm

/-- The intermediate states depend only on rank, not tree shape. -/
theorem summary_independent (A B : Nat → Prop) (l r : Shape)
    (eq : leaves l = leaves r) (t n) :
    summary A B l t n = summary A B r t n := by
  rw [summary_canonical,summary_canonical,eq]

theorem summary_count (A B : Nat → Prop) (T : Shape) {t} (tp : 0 < t) (n) :
    Small (summary A B T t n) (t^(leaves T)) := by
  rw [summary_canonical]
  exact virtual_count _ tp

/-- Uppermost split of the arithmetic multiset/list criterion, before sparse-fringe
repair. An actual representation is a list with no duplicate label in `B`. -/
theorem split_exact (A B : Nat → Prop) (l r : Shape) (n) :
    (∃ xs : List Nat, xs.length ≤ leaves l+leaves r ∧ xs.sum=n ∧
      (∀ x ∈ xs, A x) ∧ FringeDistinct B xs) ↔
    ∃ i j X Y, i+j=n ∧ summary A B l (leaves r) i X ∧
      summary A B r (leaves l) j Y ∧ Disj X Y := by
  let p := leaves l
  let q := leaves r
  have atroot : Avoid (Actual A B (p+q) n) Empty ↔
      (∃ xs : List Nat, xs.length ≤ p+q ∧ xs.sum=n ∧ (∀ x ∈ xs, A x) ∧ FringeDistinct B xs) := by
    constructor
    · rintro ⟨S,⟨xs,len,wt,ok,fr,_⟩,_⟩
      exact ⟨xs,len,wt,ok,fr⟩
    · rintro ⟨xs,len,wt,ok,fr⟩
      exact ⟨_,⟨xs,len,wt,ok,fr,rfl⟩,disj_empty _⟩
  rw [← atroot,actual_split,avoid_join_iff]
  constructor
  · rintro ⟨i,j,ij,comp⟩
    have b := (budgeted_composition (e:=0) (actual_rank A B p i) (actual_rank A B q j)
      small_empty).mp comp
    obtain ⟨X,Y,hx,hy,dis,_,_⟩ := b
    exact ⟨i,j,X,Y,ij,summary_canonical A B l q i ▸ hx,summary_canonical A B r p j ▸ hy,dis⟩
  · rintro ⟨i,j,X,Y,ij,hx,hy,dis⟩
    refine ⟨i,j,ij,(budgeted_composition (e:=0) (actual_rank A B p i) (actual_rank A B q j)
      small_empty).mpr ⟨X,Y,?_,?_,dis,disj_empty _,disj_empty _⟩⟩
    · rw [summary_canonical] at hx
      exact hx
    · rw [summary_canonical] at hy
      exact hy

end Weighted

end Erdos338.Blockers
