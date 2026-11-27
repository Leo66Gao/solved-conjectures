import Std

/-! # Conflict-graph criterion from §7

All lists below represent at most the indicated number of positive summands.
A list of fringe labels is a vertex support. "Avoid" expresses nonadjacency.
Immune slots disclose no labels; a weak slot selects one explicit reflected
alternative. The final bridge from fringe-clean sums to distinct sums is a
separate theorem argument (symmetric-pair repair), never an added axiom.
-/
namespace Erdos338.Pair

def All (A : Nat → Prop) (l : List Nat) := ∀ x, x ∈ l → A x
def Clean (B : Nat → Bool) (l : List Nat) := (l.filter B).Nodup
def Avoid (p q : List Nat) := ∀ x, x ∈ p → x ∈ q → False

def Repair (A : Nat → Prop) (B : Nat → Bool) (h : Nat) :=
  ∀ xs : List Nat, xs.length ≤ h → All A xs → Clean B xs →
    ∃ ys : List Nat, ys.length ≤ h ∧ All A ys ∧ ys.Nodup ∧ ys.sum = xs.sum

private theorem avoids_symm (h : Avoid p q) : Avoid q p :=
  fun x hx hy => h x hy hx

private theorem avoidAppR : Avoid p (q ++ r) ↔ Avoid p q ∧ Avoid p r := by
  simp [Avoid, List.mem_append, or_imp, forall_and]

private theorem avoidAppL : Avoid (p ++ q) r ↔ Avoid p r ∧ Avoid q r := by
  simp [Avoid, List.mem_append, or_imp, forall_and]

private theorem nodupApp (x y : List Nat) :
    (x ++ y).Nodup ↔ x.Nodup ∧ y.Nodup ∧ Avoid x y := by
  rw [List.Nodup, List.pairwise_append]
  constructor
  · rintro ⟨a,b,c⟩
    exact ⟨a,b,fun z hz hw => c z hz z hw rfl⟩
  · rintro ⟨a,b,c⟩
    exact ⟨a,b,fun z hz w hw e => c z hz (e ▸ hw)⟩

private theorem natSumApp (x y : List Nat) : (x ++ y).sum = x.sum + y.sum := by
  induction x with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.add_assoc]

private theorem allApp : All A (x ++ y) ↔ All A x ∧ All A y := by
  simp [All, List.mem_append, or_imp, forall_and]

/-- The three positive reflected alternatives: a fringe singleton, a mixed
pair with just its fringe end exposed, or a distinct pair of fringe points.
The last support can be listed in either order, which does not affect packing
or the existence of an independent transversal. -/
inductive Alt (A : Nat → Prop) (B : Nat → Bool) : Nat → List Nat → Prop where
  | single {b} : A b → B b = true → Alt A B b [b]
  | mixed {b g} : A b → B b = true → A g → B g = false → Alt A B (b+g) [b]
  | double {b c} : A b → B b = true → A c → B c = true → b ≠ c → Alt A B (b+c) [b,c]

theorem Alt.realize (t : Alt A B s p) : ∃ xs : List Nat,
    xs.length ≤ 2 ∧ All A xs ∧ xs.sum = s ∧ xs.filter B = p ∧ xs.Nodup := by
  cases t with
  | @single b ab hb =>
    exact ⟨[s], by simp [All,ab,hb]⟩
  | @mixed b g ab hb ag hg =>
    have ne : b ≠ g := by rintro rfl; simp_all
    exact ⟨[b,g], by simp [All,ab,ag,hb,hg,ne] <;> grind [All]⟩
  | @double b c ab hb ac hc ne =>
    exact ⟨[b,c], by simp [All,ab,ac,hb,hc,ne] <;> grind [All]⟩

private theorem Alt.width (t : Alt A B s p) : p.length ≤ 2 := by cases t <;> simp

/-- At least h−1 pairwise disjoint nonempty reflected alternatives. Using
packings instead of dividing the number of oriented doubletons by two
makes the expression independent of how vertices are enumerated. -/
def Popular (A : Nat → Prop) (B : Nat → Bool) (h s : Nat) :=
  ∃ L : List (List Nat), h-1 ≤ L.length ∧ L.Pairwise Avoid ∧ ∀ p ∈ L, Alt A B s p

def GoodPair (A : Nat → Prop) (B : Nat → Bool) (s : Nat) :=
  ∃ xs : List Nat, xs.length ≤ 2 ∧ All A xs ∧ xs.sum = s ∧ xs.filter B = []

def Immune (A : Nat → Prop) (B : Nat → Bool) (h s : Nat) :=
  GoodPair A B s ∨ Popular A B h s

/-- Pigeonhole lemma: deleting b labels cannot hit more than b members of a
disjoint packing. The deletion list need not be duplicate-free. -/
private theorem escape {L : List (List Nat)} {E : List Nat}
    (hp : L.Pairwise Avoid) (hb : E.length < L.length) :
    ∃ p ∈ L, Avoid p E := by
  classical
  induction L generalizing E with
  | nil => simp at hb
  | cons p ps ih =>
    rcases List.pairwise_cons.mp hp with ⟨hcross,htail⟩
    by_cases ha : Avoid p E
    · exact ⟨p, by simp, ha⟩
    · obtain ⟨b,hbp,hbe⟩ : ∃ b, b ∈ p ∧ b ∈ E := by
        apply Classical.byContradiction
        intro h
        apply ha
        exact fun x h₁ h₂ => h ⟨x,h₁,h₂⟩
      have el := List.length_erase_of_mem hbe
      have ep : 0 < E.length := List.length_pos_of_mem hbe
      simp only [List.length_cons] at hb
      obtain ⟨q,hq,ha'⟩ := ih htail (E := E.erase b) (by omega)
      refine ⟨q,List.mem_cons_of_mem _ hq,?_⟩
      intro x hx he
      by_cases heq : x = b
      · subst x; exact hcross q hq b hbp hx
      · exact ha' x hx ((List.mem_erase_of_ne heq).mpr he)

theorem immune_realize (hh : 2 ≤ h) (z : Immune A B h s)
    (he : E.length ≤ h-2) : ∃ xs : List Nat, xs.length ≤ 2 ∧
    All A xs ∧ xs.sum = s ∧ Clean B xs ∧ Avoid (xs.filter B) E := by
  rcases z with ⟨xs,hl,ha,hs,hf⟩ | ⟨L,hl,hp,ht⟩
  · exact ⟨xs,hl,ha,hs,by simp [Clean,hf],by simp [Avoid,hf]⟩
  · obtain ⟨p,hp',ha⟩ := escape hp (E := E) (by omega)
    obtain ⟨xs,hxl,hxa,hxs,hxf,hxn⟩ := (ht p hp').realize
    exact ⟨xs,hxl,hxa,hxs,hxn.sublist List.filter_sublist,by rwa [hxf]⟩

/-- Construct the weak-slot conflict graph one index class at a time. The
indices count ALL pair slots, including immune slots; the unused part of a
singleton slot (e=1) or of a pair slot is simply padding. A successful
expression records only its exposed labels U, not the full witnesses. -/
inductive Cert (A : Nat → Prop) (B : Nat → Bool) (h e : Nat) :
    Nat → Nat → List Nat → Prop where
  | base (a : List Nat) : a.length ≤ e → All A a → (a.filter B).Nodup →
      Cert A B h e 0 a.sum (a.filter B)
  | immune {m n U s} : Immune A B h s → Cert A B h e m n U →
      Cert A B h e (m+1) (s+n) U
  | weak {m n U s p} : ¬Immune A B h s → Alt A B s p →
      Avoid p U → Cert A B h e m n U → Cert A B h e (m+1) (s+n) (p++U)

/-- Reconstruct a fringe-clean raw sum. The strengthened deletion budget
accounts simultaneously for earlier weak and later immune slots. -/
theorem Cert.realize (hh : 2 ≤ h) (t : Cert A B h e m n u)
    (hr : E.length + 2*m+e ≤ h) (hu : Avoid u E) :
    ∃ xs : List Nat, xs.length ≤ 2*m+e ∧ All A xs ∧ xs.sum = n ∧
      Clean B xs ∧ Avoid (xs.filter B) E := by
  induction t generalizing E with
  | base a hl ha hd =>
    exact ⟨a, by simpa using hl, ha,rfl,hd,hu⟩
  | @immune m n u s imm tail ih =>
    obtain ⟨r,rl,ra,rs,rc,re⟩ := ih (E := E) (by omega) hu
    have bl := List.length_filter_le B r
    obtain ⟨l,ll,la,ls,lc,avoid⟩ := immune_realize hh imm (E := r.filter B ++ E)
        (by simp only [List.length_append]; omega)
    rcases avoidAppR.mp avoid with ⟨cross,le⟩
    refine ⟨l++r, ?_,allApp.mpr ⟨la,ra⟩,by simp [natSumApp, ls, rs], ?_,?_⟩
    · simp only [List.length_append]; omega
    · rw [Clean,List.filter_append,nodupApp]; exact ⟨lc,rc,cross⟩
    · rw [List.filter_append,avoidAppL]; exact ⟨le,re⟩
  | @weak m n u s p ni alt cross tail ih =>
    obtain ⟨pe,ue⟩ := avoidAppL.mp hu
    have pw := alt.width
    obtain ⟨r,rl,ra,rs,rc,re⟩ := ih (E := p++E)
      (by simp only [List.length_append]; omega) (avoidAppR.mpr ⟨avoids_symm cross,ue⟩)
    obtain ⟨rp,rE⟩ := avoidAppR.mp re
    obtain ⟨l,ll,la,ls,lf,ln⟩ := alt.realize
    refine ⟨l++r,?_,allApp.mpr ⟨la,ra⟩,by simp [natSumApp,ls,rs], ?_,?_⟩
    · simp only [List.length_append]; omega
    · rw [Clean, List.filter_append,nodupApp]
      exact ⟨ln.sublist List.filter_sublist,rc,by rw [lf]; exact avoids_symm rp⟩
    · rw [List.filter_append,avoidAppL,lf]; exact ⟨pe,rE⟩

private theorem readSlot {xs : List Nat} (hl : xs.length ≤ 2)
    (ha : All A xs) (hd : xs.Nodup) :
    GoodPair A B xs.sum ∨ Alt A B xs.sum (xs.filter B) := by
  classical
  have good (hf : xs.filter B = []) : GoodPair A B xs.sum :=
    ⟨xs,hl,ha,rfl,hf⟩
  cases xs with
  | nil => exact Or.inl (good rfl)
  | cons a tail =>
    have aa := ha a (by simp)
    cases tail with
    | nil =>
      cases ba : B a with
      | false => exact Or.inl (good (by simp [ba]))
      | true => exact Or.inr (by simpa [ba] using Alt.single aa ba)
    | cons b r =>
      have ab := ha b (by simp)
      have ne : a ≠ b := by have hg := (List.nodup_cons.mp hd).1; exact fun eq => hg (by simp [eq])
      cases r with
      | cons c l => simp at hl
      | nil =>
        cases ba : B a <;> cases bb : B b
        · exact Or.inl (good (by simp [ba,bb]))
        · exact Or.inr (by simpa [ba,bb,Nat.add_comm] using Alt.mixed ab bb aa ba)
        · exact Or.inr (by simpa [ba,bb] using Alt.mixed aa ba ab bb)
        · exact Or.inr (by simpa [ba,bb] using Alt.double aa ba ab bb ne)

/-- Read the conflict-graph certificate from any globally distinct list,
padding the last pair or singleton when necessary. -/
theorem cert_of_distinct (e m : Nat) (xs : List Nat) (lh : xs.length ≤ 2*m+e)
    (ha : All A xs) (hd : xs.Nodup) :
    ∃ u, Cert A B h e m xs.sum u ∧ ∀ x ∈ u, x ∈ xs := by
  induction m generalizing xs with
  | zero =>
    exact ⟨xs.filter B,.base xs (by simpa using lh) ha (hd.sublist List.filter_sublist),
                fun _ hx => (List.mem_filter.mp hx).1⟩
  | succ m ih =>
    let l := xs.take 2
    let r := xs.drop 2
    have eq : l ++ r = xs := List.take_append_drop 2 xs
    have len : r.length ≤ 2*m+e := by simp only [r,List.length_drop]; omega
    rw [←eq] at ha hd
    obtain ⟨la,ra⟩ := allApp.mp ha
    obtain ⟨ld,rd,disj⟩ := (nodupApp l r).mp hd
    obtain ⟨u,cu,us⟩ := ih r len ra rd
    have rsub : ∀ x ∈ r, x ∈ xs := by rw [←eq]; exact fun _ hx => List.mem_append_right _ hx
    have lsub : ∀ x ∈ l, x ∈ xs := by rw [←eq]; exact fun _ hx => List.mem_append_left _ hx
    have eqs : xs.sum = l.sum + r.sum := by rw [←eq, natSumApp]
    rw [eqs]
    by_cases ip : Immune A B h l.sum
    · exact ⟨u,.immune ip cu, fun _ hx => rsub _ (us _ hx)⟩
    · have alt := (readSlot (B := B) (xs := l)
                      (by simp [l]; omega) la ld).resolve_left (fun gp => ip (Or.inl gp))
      refine ⟨l.filter B ++ u, .weak ip alt ?_ cu, ?_⟩
      · exact fun _ hxl hxr => disj _ (List.mem_filter.mp hxl).1 (us _ hxr)
      · intro x hx
        rcases List.mem_append.mp hx with hl|hr
        · exact lsub x (List.mem_filter.mp hl).1
        · exact rsub x (us x hr)

/-- Representation by at most h distinct elements. No assumption on A's
order or density, and empty lists are allowed. -/
def Restricted (A : Nat → Prop) (h n : Nat) :=
  ∃ xs : List Nat, xs.length ≤ h ∧ All A xs ∧ xs.Nodup ∧ xs.sum = n

/-- Direct rank-two criterion, in an ordered-slot presentation of the union
over the admissible number of weak slots. Taking m=h/2 and e=h%2 recovers
the intended singleton/zero-slot convention. -/
theorem pair_criterion (hh : 2 ≤ h) (size : h = 2*m+e) (repair : Repair A B h) :
    Restricted A h n ↔ ∃ u, Cert A B h e m n u := by
  constructor
  · rintro ⟨xs,hl,ha,hd,rfl⟩
    obtain ⟨u,hu,-⟩ := cert_of_distinct (A := A) (B := B) (h := h) e m xs (size ▸ hl) ha hd
    exact ⟨u,hu⟩
  · rintro ⟨u,hu⟩
    obtain ⟨xs,hl,ha,hs,hc,-⟩ := hu.realize hh (E := []) (by simp [size]) (by simp [Avoid])
    obtain ⟨ys,yl,ya,yd,ysum⟩ := repair xs (size ▸ hl) ha hc
    exact ⟨ys,yl,ya,yd,ysum.trans hs⟩


/-- Canonical identifier: a singleton's fringe label, or the smaller fringe
endpoint of an unordered doubleton. -/
def key : List Nat → Nat
  | [b,c] => min b c
  | b::_ => b
  | [] => 0

/-- Recover the identifier from any one fringe endpoint and the weight, with
no higher-rank representation queries. -/
def owner (B : Nat → Bool) (s x : Nat) : Nat :=
  if x = s ∨ B (s-x) = false then x else min x (s-x)

theorem Alt.key_mem (t : Alt A B s p) : key p ∈ p := by
  cases t with
  | single => simp [key]
  | mixed => simp [key]
  | @double b c => by_cases le : b ≤ c <;> simp [key, Nat.min_def,le]

theorem Alt.owner_eq (apos : ∀ x, A x → 0 < x) (t : Alt A B s p) {x} (hx : x ∈ p) :
    owner B s x = key p := by
  cases t with
  | single => simp_all [key,owner]
  | @mixed b g ab hb ag hg =>
    simp at hx; subst x
    have u : b+g-b = g := by omega
    simp [key,owner,hg,u]
  | @double b c ab hb ac hc ne =>
    have pb := apos _ ab
    have pc := apos _ ac
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx|hx
    · subst x
      have e : b ≠ b+c := by omega
      have u : b+c-b = c := by omega
      simp only [owner, key, e, u, hc, Bool.true_eq_false,or_self,if_false]
    · subst x
      have e : c ≠ b+c := by omega
      have u : b+c-c = b := by omega
      simp only [owner, key, e, u, hb, Bool.true_eq_false,or_self,if_false,Nat.min_comm]

/-- A lower endpoint in the reflected intersection, excluding the diagonal
and choosing a single representative from each two-cycle. -/
def KeyOK (A : Nat → Prop) (B : Nat → Bool) (s b : Nat) :=
  A b ∧ B b = true ∧
    (b = s ∨ b < s ∧ A (s-b) ∧ (B (s-b) = false ∨ b < s-b))

theorem Alt.key_ok (apos : ∀ x, A x → 0 < x) (v : Alt A B s p) :
    KeyOK A B s (key p) := by
  cases v with
  | single => simp_all [KeyOK,key]
  | @mixed b g ab hb ag hg =>
    have hg' := apos _ ag
    have sub : b+g-b=g := by omega
    simp [KeyOK,key,ab,hb,ag,hg,hg',sub]
  | @double b c ab hb ac hc ne =>
    have bp := apos _ ab
    have cp := apos _ ac
    by_cases le : b ≤ c
    · have bc : b < c := by omega
      have sub : b+c-b=c := by omega
      simp [KeyOK,key,Nat.min_eq_left le,ab,hb,ac,bc,cp,sub]
    · have cb : c < b := by omega
      simp [KeyOK,key,Nat.min_eq_right (Nat.le_of_lt cb),ac,hc,ab,cb,bp]

def fromKey (B : Nat → Bool) (s k : Nat) :=
  if k = s ∨ B (s-k) = false then [k] else [k,s-k]

theorem fromKey_valid (o : KeyOK A B s k) :
    Alt A B s (fromKey B s k) ∧ key (fromKey B s k) = k := by
  rcases o with ⟨ak,bk,h⟩
  rcases h with rfl | ⟨lt,ag,e⟩
  · simp [fromKey,key,Alt.single ak bk]
  · have heq : k + (s-k) = s := by omega
    have hne : k ≠ s := by omega
    cases bg : B (s-k)
    · exact ⟨by simpa only [heq,fromKey,bg,or_true,if_true] using Alt.mixed ak bk ag bg,
             by simp [fromKey,bg,key]⟩
    · have st : k < s-k := by rcases e with h|h <;> simp_all
      have ne : k ≠ s-k := by omega
      exact ⟨by simpa only [heq,fromKey,bg,hne,Bool.true_eq_false,or_self,if_false] using
                  Alt.double ak bk ag bg ne,
             by simp [fromKey,bg,hne,key,Nat.min_eq_left (Nat.le_of_lt st)]⟩

/-- Lists exactly once the canonical keys from the three reflected cases of
§7. In particular its length is the pair multiplicity with doubletons
counted once, not twice. -/
noncomputable def keys (A : Nat → Prop) (B : Nat → Bool) (s : Nat) : List Nat :=
  (List.range (s+1)).filter (fun k => @decide (KeyOK A B s k) (Classical.propDecidable _))

theorem mem_keys : k ∈ keys A B s ↔ KeyOK A B s k := by
  classical
  simp only [keys,List.mem_filter,decide_eq_true_eq,List.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    rcases h.2.2 with e|e
    · omega
    · have := e.1; omega

private theorem nodup_subset_length {l r : List Nat} (n : l.Nodup)
    (sub : ∀ x ∈ l, x ∈ r) : l.length ≤ r.length := by
  induction l generalizing r with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hn⟩ := List.nodup_cons.mp n
    have xm := sub x (by simp)
    have sub' : ∀ y ∈ xs, y ∈ r.erase x := by
      intro y hy
      have ne : y ≠ x := by rintro rfl; exact hx hy
      exact (List.mem_erase_of_ne ne).mpr (sub y (List.mem_cons_of_mem _ hy))
    have ihh := ih hn sub'
    have el := List.length_erase_of_mem xm
    have pos := List.length_pos_of_mem xm
    simp only [List.length_cons]
    omega

/-- Exact arithmetic validity of the immune threshold: packing size is
equivalent to counting the explicitly reflected keys, without any search
for a packing or a representation of rank greater than two. -/
theorem popular_iff_reflected_count (apos : ∀ x, A x → 0 < x) :
    Popular A B h s ↔ h-1 ≤ (keys A B s).length := by
  constructor
  · rintro ⟨L,hl,hp,ht⟩
    have hq : (L.map key).Nodup := by
      rw [List.Nodup,List.pairwise_map]
      apply hp.imp_of_mem
      intro p q lp lq dis heq
      exact dis _ (ht p lp).key_mem (heq ▸ (ht q lq).key_mem)
    have sl : ∀ x ∈ L.map key, x ∈ keys A B s := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      exact mem_keys.mpr ((ht p hp).key_ok apos)
    have := nodup_subset_length hq sl
    simp only [List.length_map] at this
    omega
  · intro hl
    let K := keys A B s
    let f := fromKey B s
    have nd : K.Nodup := List.nodup_range.sublist List.filter_sublist
    refine ⟨K.map f,by simpa [K],?_,?_⟩
    · rw [List.pairwise_map]
      apply nd.imp_of_mem
      intro k k' hk hk' ne x hx hy
      obtain ⟨vk,idk⟩ := fromKey_valid (mem_keys.mp hk)
      obtain ⟨vk',idk'⟩ := fromKey_valid (mem_keys.mp hk')
      have e₁ := vk.owner_eq apos hx
      have e₂ := vk'.owner_eq apos hy
      exact ne (idk.symm.trans ((e₁.symm.trans e₂).trans idk'))
    · intro p hp
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
      exact (fromKey_valid (mem_keys.mp hk)).1

theorem immune_iff_reflected_count (apos : ∀ x, A x → 0 < x) :
    Immune A B h s ↔ GoodPair A B s ∨ h-1 ≤ (keys A B s).length := by
  rw [Immune,popular_iff_reflected_count apos]

/-- Weak part Q: each slot class supplies one allowed vertex and records its
support. The base is the optional singleton (length ≤e, with e=0 or 1).
Avoiding the aggregate of already selected supports is precisely an
independent transversal of these slot classes. -/
inductive WeakCert (A : Nat → Prop) (B : Nat → Bool) (h e : Nat) :
    Nat → Nat → List Nat → Prop where
  | base (a : List Nat) : a.length ≤ e → All A a → (a.filter B).Nodup →
      WeakCert A B h e 0 a.sum (a.filter B)
  | next {j n U s p} : ¬Immune A B h s → Alt A B s p → Avoid p U →
      WeakCert A B h e j n U → WeakCert A B h e (j+1) (s+n) (p++U)

private theorem WeakCert.toCert (q : WeakCert A B h e j n U) : Cert A B h e j n U := by
  induction q with
  | base a ha hb hc => exact .base a ha hb hc
  | next h1 h2 h3 _ ih => exact .weak h1 h2 h3 ih

/-- The manuscript's expanded RHS: an ordinary (m-j)-fold sum of immune
weights, plus the sum of j compatible weak slots and the optional singleton.
In contrast with the restricted sumset there is no distinctness requirement
on the immune weights or on the weak weights themselves. -/
def SumsetRHS (A : Nat → Prop) (B : Nat → Bool) (h m e n : Nat) :=
  ∃ j ≤ m, ∃ ps : List Nat, ∃ q u, ps.length = m-j ∧ All (Immune A B h) ps ∧
    WeakCert A B h e j q u ∧ n = ps.sum + q

private theorem Cert.expand (c : Cert A B h e m n u) :
    ∃ j ≤ m, ∃ ps : List Nat, ∃ q, ps.length = m-j ∧ All (Immune A B h) ps ∧
    WeakCert A B h e j q u ∧ n = ps.sum + q := by
  induction c with
  | base a al av an =>
    exact ⟨0,by omega, [],a.sum,rfl,by simp [All],.base a al av an,by simp⟩
  | @immune m n u s imm _ ih =>
    obtain ⟨j,jm,p,q,pl,pa,w,en⟩ := ih
    refine ⟨j,by omega,s::p,q,by simp only [List.length_cons]; omega,?_,w,?_⟩
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hp
      · exact imm
      · exact pa x hp
    · simp [en,Nat.add_assoc]
  | @weak m n u s v ni alt cross _ ih =>
    obtain ⟨j,jm,p,q,pl,pa,w,en⟩ := ih
    refine ⟨j+1,by omega,p,s+q,by omega,pa,.next ni alt cross w,?_⟩
    omega

private theorem cert_add_immune_list (c : Cert A B h e j q u)
    (ps : List Nat) (pa : All (Immune A B h) ps) :
    Cert A B h e (ps.length+j) (ps.sum+q) u := by
  induction ps with
  | nil => simpa using c
  | cons s ps ih =>
    have cs := Cert.immune (pa s (by simp)) (ih (fun x hx => pa x (by simp [hx])))
    simpa only [List.length_cons,List.sum_cons,Nat.add_assoc,Nat.succ_add,Nat.add_succ] using cs

theorem cert_iff_sumset_rhs : (∃ u, Cert A B h e m n u) ↔ SumsetRHS A B h m e n := by
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨j,jm,p,q,pl,pa,w,hn⟩ := hu.expand
    exact ⟨j,jm,p,q,u,pl,pa,w,hn⟩
  · rintro ⟨j,jm,p,q,u,pl,pa,w,rfl⟩
    have c := cert_add_immune_list w.toCert p pa
    have mm : p.length+j=m := by omega
    exact ⟨u,mm ▸ c⟩

theorem rank_two_sumset_identity (hh : 2 ≤ h) (size : h = 2*m+e) (repair : Repair A B h) :
    Restricted A h n ↔ SumsetRHS A B h m e n :=
  (pair_criterion hh size repair).trans cert_iff_sumset_rhs

/-- Ordinary representation allowing repeated labels. -/
def Ordinary (A : Nat → Prop) (h n : Nat) :=
  ∃ xs : List Nat, xs.length ≤ h ∧ All A xs ∧ xs.sum = n

/-- The doubled fringe plus the ordinary (h-2)-fold at-most sumset. -/
def Footprint (A : Nat → Prop) (B : Nat → Bool) (h n : Nat) :=
  ∃ b t, A b ∧ B b = true ∧ Ordinary A (h-2) t ∧ n=b+b+t

private theorem permutation_sum {u v : List Nat} (p : u.Perm v) : u.sum=v.sum := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp; omega
  | trans _ _ i j => exact i.trans j

private theorem find_repeat {xs : List Nat} (dirty : ¬Clean B xs) :
    ∃ b ys, B b = true ∧ xs.Perm (b::b::ys) := by
  induction xs with
  | nil => simp [Clean] at dirty
  | cons a xs ih =>
    by_cases dt : Clean B xs
    · have ba : B a = true := by
        cases z : B a <;> simp_all [Clean]
      have am : a ∈ xs.filter B := by
        apply Classical.byContradiction
        intro hm
        exact dirty (by simpa [Clean,ba,hm] using dt)
      have perm := List.perm_cons_erase (List.mem_filter.mp am).1
      exact ⟨a,xs.erase a,ba,perm.cons a⟩
    · obtain ⟨b,x,bb,hp⟩ := ih dt
      exact ⟨b,a::x,bb, (hp.cons a).trans ((List.Perm.swap b a _).trans
        ((List.Perm.swap b a x).cons b))⟩

/-- A failed ordinary target is necessarily in the doubled-fringe footprint.
This is a set inclusion, not a classification of how often failures occur. -/
theorem defect_in_footprint (repair : Repair A B h)
    (o : Ordinary A h n) (hole : ¬Restricted A h n) : Footprint A B h n := by
  obtain ⟨xs,xl,xa,rfl⟩ := o
  have dirt : ¬ Clean B xs := fun c => hole (repair xs xl xa c)
  obtain ⟨b,ys,bb,hp⟩ := find_repeat dirt
  have size := hp.length_eq
  simp only [List.length_cons] at size
  have all' : All A (b::b::ys) := fun x hx => xa x (hp.mem_iff.mpr hx)
  have eq := permutation_sum hp
  simp only [List.sum_cons] at eq
  exact ⟨b,ys.sum,all' b (by simp),bb,⟨ys,by omega,
    fun x hx => all' x (by simp [hx]),rfl⟩,by omega⟩

/-- Exact tail reduction of §7.2: in the presence of ordinary coverage it
suffices to test the explicit pair union just on the fringe footprint. -/
theorem tail_footprint_iff (hh : 2 ≤ h) (size : h = 2*m+e) (repair : Repair A B h)
    (base : ∃ N, ∀ n ≥ N, Ordinary A h n) :
    (∃ N, ∀ n ≥ N, Restricted A h n) ↔
      ∃ N, ∀ n ≥ N, Footprint A B h n → SumsetRHS A B h m e n := by
  classical
  constructor
  · rintro ⟨N,hhit⟩
    exact ⟨N,fun n hn _ => (rank_two_sumset_identity hh size repair).mp (hhit n hn)⟩
  · rintro ⟨N,hgood⟩
    obtain ⟨N₀,ho⟩ := base
    refine ⟨max N N₀,fun n hn => ?_⟩
    apply Classical.byContradiction
    intro hnr
    have ord := ho n (Nat.le_trans (Nat.le_max_right _ _) hn)
    have f := defect_in_footprint repair ord hnr
    have hit := hgood n (Nat.le_trans (Nat.le_max_left _ _) hn) f
    exact hnr ((rank_two_sumset_identity hh size repair).mpr hit)


/-- All actual weak choices can be replaced by the canonically oriented
support computed from the key; only the order of its endpoints may change. -/
theorem Alt.normalize (apos : ∀ x, A x → 0 < x) (v : Alt A B s p) :
    (fromKey B s (key p)).Perm p := by
  cases v with
  | single => simp [fromKey,key]
  | @mixed b g ab hb ag hg =>
    have sub : b+g-b=g := by omega
    simp [key,fromKey,sub,hg]
  | @double b c ab hb ac hc ne =>
    have bp := apos _ ab
    have cp := apos _ ac
    by_cases le : b ≤ c
    · have u : b+c-b=c := by omega
      have d : b ≠ b+c := by omega
      simp [fromKey,key,Nat.min_eq_left le,u,hc,d]
    · have u : b+c-c=b := by omega
      have d : c ≠ b+c := by omega
      simpa only [fromKey,key,Nat.min_eq_right (by omega : c ≤ b),d,
                      u,hb,Bool.true_eq_false,or_self,if_false] using List.Perm.swap b c []

/-- Finite graph given exclusively by the input membership tests and
finite lists of reflected keys. Each weak-slot vertex class here has
literally at most h−2 vertices, with no duplicate orientations. -/
inductive KeyGraph (A : Nat → Prop) (B : Nat → Bool) (h e : Nat) :
    Nat → Nat → List Nat → Prop where
  | base (a : List Nat) : a.length ≤ e → All A a → (a.filter B).Nodup →
      KeyGraph A B h e 0 a.sum (a.filter B)
  | next {j n U s k} : ¬GoodPair A B s → (keys A B s).length ≤ h-2 →
      k ∈ keys A B s → Avoid (fromKey B s k) U → KeyGraph A B h e j n U →
      KeyGraph A B h e (j+1) (s+n) (fromKey B s k ++ U)

private theorem weak_to_keygraph (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x)
    (w : WeakCert A B h e j q u) :
    ∃ v, KeyGraph A B h e j q v ∧ v.Perm u := by
  induction w with
  | base a al aa an => exact ⟨_,.base a al aa an,.refl _⟩
  | @next j n U s p notI alt cross _ ih =>
    obtain ⟨v,kgraph,vperm⟩ := ih
    have notP : ¬(GoodPair A B s ∨ h-1 ≤ (keys A B s).length) :=
      fun hp => notI ((immune_iff_reflected_count apos).mpr hp)
    have hg : ¬GoodPair A B s := fun z => notP (Or.inl z)
    have hsize : (keys A B s).length ≤ h-2 := by
      have hbad : ¬ h-1 ≤ (keys A B s).length := fun z => notP (Or.inr z)
      omega
    have norm := alt.normalize apos
    have nohit : Avoid (fromKey B s (key p)) v := fun x x₁ x₂ =>
      cross x (norm.mem_iff.mp x₁) (vperm.mem_iff.mp x₂)
    exact ⟨_,.next hg hsize (mem_keys.mpr (alt.key_ok apos)) nohit kgraph,norm.append vperm⟩

private theorem KeyGraph.toWeak (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x)
    (w : KeyGraph A B h e j q u) : WeakCert A B h e j q u := by
  induction w with
  | base a al aa an => exact .base a al aa an
  | @next j n U s k ng ls kin dis _ ih =>
    have notI : ¬Immune A B h s := by
      intro im
      rcases (immune_iff_reflected_count apos).mp im with g|b
      · exact ng g
      · omega
    exact .next notI (fromKey_valid (mem_keys.mp kin)).1 dis ih

/-- Completely reflected version of the expanded RHS. Each immutable weight
is queried by a good-only two-term sum or the reflected count; every weak
vertex is computed from one key of its finite reflected list. -/
def ReflectedRHS (A : Nat → Prop) (B : Nat → Bool) (h m e n : Nat) :=
  ∃ j ≤ m, ∃ ps : List Nat, ∃ q u, ps.length = m-j ∧
    All (fun s => GoodPair A B s ∨ h-1 ≤ (keys A B s).length) ps ∧
    KeyGraph A B h e j q u ∧ n = ps.sum + q

theorem sumset_rhs_iff_reflected_rhs (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x) :
    SumsetRHS A B h m e n ↔ ReflectedRHS A B h m e n := by
  constructor
  · rintro ⟨j,jm,p,q,u,pl,pa,w,hn⟩
    obtain ⟨v,kg,_⟩ := weak_to_keygraph hh apos w
    exact ⟨j,jm,p,q,v,pl,fun s hs => (immune_iff_reflected_count apos).mp (pa s hs),kg,hn⟩
  · rintro ⟨j,jm,p,q,v,pl,pa,kg,hn⟩
    exact ⟨j,jm,p,q,v,pl,fun s hs => (immune_iff_reflected_count apos).mpr (pa s hs),
      kg.toWeak hh apos,hn⟩

theorem rank_two_reflected_identity (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x)
    (repair : Repair A B h) :
    Restricted A h n ↔ ReflectedRHS A B h (h/2) (h%2) n :=
  (rank_two_sumset_identity hh (by omega) repair).trans (sumset_rhs_iff_reflected_rhs hh apos)

theorem tail_reflected_footprint_iff (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x)
    (repair : Repair A B h) (base : ∃ N, ∀ n ≥ N, Ordinary A h n) :
    (∃ N, ∀ n ≥ N, Restricted A h n) ↔
      ∃ N, ∀ n ≥ N, Footprint A B h n → ReflectedRHS A B h (h/2) (h%2) n := by
  rw [tail_footprint_iff (m := h/2) (e := h%2) hh (by omega) repair base]
  constructor
  · rintro ⟨N,hn⟩
    exact ⟨N,fun n hN hf => (sumset_rhs_iff_reflected_rhs hh apos).mp (hn n hN hf)⟩
  · rintro ⟨N,hn⟩
    exact ⟨N,fun n hN hf => (sumset_rhs_iff_reflected_rhs hh apos).mpr (hn n hN hf)⟩


/-- Operationally fresh ordinary good centers. This is supplied by the
arithmetic centered-pair theorem at the canonical choice of B. -/
def GoodFresh (A : Nat → Prop) (B : Nat → Bool) (h : Nat) :=
  ∀ a, A a → B a = false → ∀ E : List Nat, E.length ≤ h-2 →
    ∃ b c, A b ∧ A c ∧ b ≠ c ∧ b ∉ E ∧ c ∉ E ∧ b+c = a+a

def After (A : Nat → Prop) (E : List Nat) (x : Nat) := A x ∧ x ∉ E

private theorem avoids_all_after {xs E : List Nat} (a : All A xs)
    (b : All (fun x => B x = true) E) (q : Avoid (xs.filter B) E) :
    All (After A E) xs := by
  intro x hx
  refine ⟨a x hx,?_⟩
  intro he
  exact q x (List.mem_filter.mpr ⟨hx,b x he⟩) he

private theorem good_after {s h} (fresh : GoodFresh A B h) (gp : GoodPair A B s)
    (eb : All (fun x => B x = true) E) (el : E.length ≤ h-2) :
    Restricted (After A E) 2 s := by
  obtain ⟨xs,xl,xa,rfl,xf⟩ := gp
  have goodall := avoids_all_after xa eb (by simp [xf,Avoid])
  by_cases xn : xs.Nodup
  · exact ⟨xs,xl,goodall,xn,rfl⟩
  · cases xs with
    | nil => simp at xn
    | cons a r =>
      cases r with
      | nil => simp at xn
      | cons c t =>
        cases t with
        | cons _ _ => simp at xl
        | nil =>
          have ac : a = c := by simpa using xn
          subst c
          have ba : B a = false := by cases k : B a <;> simp_all
          obtain ⟨b,c,ab,ac,ne,bE,cE,eq⟩ := fresh a (xa a (by simp)) ba E el
          refine ⟨[b,c],by simp,?_,by simp [ne],by simpa using eq⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact ⟨ab,bE⟩
          · have e : x=c := by simpa using hx
            exact e ▸ ⟨ac,cE⟩

/-- Lemma 7.1, including arbitrary protected fringe deletions. This is
a genuine two-summand distinct realization after deleting the labels, not
just a statement about a clean ordinary representation. -/
theorem reflected_deletion_iff (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x)
    (fresh : GoodFresh A B h) (eb : All (fun x => B x = true) E) (el : E.length ≤ h-2) :
    Restricted (After A E) 2 s ↔
      GoodPair A B s ∨ h-1 ≤ (keys A B s).length ∨
        ∃ k ∈ keys A B s, Avoid (fromKey B s k) E := by
  constructor
  · rintro ⟨xs,xl,xa,xn,rfl⟩
    have or' := readSlot (B := B) xl (fun x hx => (xa x hx).1) xn
    rcases or' with gp | alt
    · exact Or.inl gp
    · refine Or.inr (Or.inr ⟨_,mem_keys.mpr (alt.key_ok apos),?_⟩)
      intro x hx he
      have orig := (alt.normalize apos).mem_iff.mp hx
      exact (xa x (List.mem_filter.mp orig).1).2 he
  · rintro (gp|pop|⟨k,kin,kavoid⟩)
    · exact good_after fresh gp eb el
    · obtain ⟨L,hl,pack,ok⟩ := (popular_iff_reflected_count apos).mpr pop
      obtain ⟨p,pm,avoid⟩ := escape pack (E := E) (by omega)
      obtain ⟨xs,xl,xa,xs',xf,xn⟩ := (ok p pm).realize
      exact ⟨xs,xl,avoids_all_after xa eb (xf ▸ avoid),xn,xs'⟩
    · obtain ⟨xs,xl,xa,xs',xf,xn⟩ := (fromKey_valid (mem_keys.mp kin)).1.realize
      exact ⟨xs,xl,avoids_all_after xa eb (xf ▸ kavoid),xn,xs'⟩

/-- Exact maximality of the immune class: a nonimmune weight has a killing
deletion of at most h−2 fringe labels (the list of its canonical keys). -/
theorem immune_exact (hh : 2 ≤ h) (apos : ∀ x, A x → 0 < x)
    (fresh : GoodFresh A B h) :
    Immune A B h s ↔ ∀ E : List Nat, All (fun x => B x = true) E →
      E.length ≤ h-2 → Restricted (After A E) 2 s := by
  classical
  constructor
  · intro im E eb el
    apply (reflected_deletion_iff hh apos fresh eb el).mpr
    rcases (immune_iff_reflected_count apos).mp im with gp|cnt
    · exact Or.inl gp
    · exact Or.inr (Or.inl cnt)
  · intro robust
    apply Classical.byContradiction
    intro notim
    have no : ¬(GoodPair A B s ∨ h-1 ≤ (keys A B s).length) :=
      fun hp => notim ((immune_iff_reflected_count apos).mpr hp)
    have eb : All (fun x => B x = true) (keys A B s) :=
      fun _ hx => (mem_keys.mp hx).2.1
    have el : (keys A B s).length ≤ h-2 := by
      have neg : ¬h-1 ≤ (keys A B s).length := fun hf => no (Or.inr hf)
      omega
    have event := (reflected_deletion_iff hh apos fresh eb el).mp (robust _ eb el)
    rcases event with gp|cnt|⟨k,mk,avoid⟩
    · exact no (Or.inl gp)
    · exact no (Or.inr cnt)
    · have info := fromKey_valid (mem_keys.mp mk)
      have keymem := info.1.key_mem
      rw [info.2] at keymem
      exact avoid k keymem mk

end Erdos338.Pair
