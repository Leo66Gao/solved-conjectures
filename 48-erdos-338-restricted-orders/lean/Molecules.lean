import Thinning

/-! # Isolation and equal ordinary counts in the lacunary stencil family
These lemmas work for all h≥3 and all allowed placements, and concern
ordinary arithmetic information rather than lifted endpoint searches.
-/
namespace Erdos338.Thinning.Stencils

def GoodTags : List ℕ := [1,2,6]
def BadTags : List ℕ := [1,4,7]
def filterWords (B : List ℕ) (k n : ℕ) : List (List ℕ) :=
  (words B k).filter (fun w => w.sum == n)

-- Kernel reduction on 3³ words; no external/native evaluation.
theorem raw_offsets_identical :
  (filterWords GoodTags 3 9).length = 6 ∧ (filterWords BadTags 3 9).length = 6 := by decide

theorem separate_supports :
    (∀ w ∈ filterWords GoodTags 3 9, w.toFinset.card = 3) ∧
    (∀ w ∈ filterWords BadTags 3 9, w.toFinset.card = 2) := by decide

private theorem twoUniform (b : ℕ) (F : List (List ℕ))
    (H : ∀ w ∈ F, w.toFinset.card = b) :
    (F.map (fun w => (Polynomial.X : Poly)^w.toFinset.card)).sum = F.length • (Polynomial.X : Poly)^b := by
  induction F with
  | nil => simp
  | cons w l ih =>
    have h := List.forall_mem_cons.mp H
    simp only [List.map_cons,List.sum_cons,h.1, List.length_cons, ih h.2, succ_nsmul, add_comm]

noncomputable def argResponse (B : List ℕ) : Poly :=
  ((filterWords B 3 9).map (fun w => (Polynomial.X : Poly)^w.toFinset.card)).sum

theorem two_response_polynomials :
    argResponse GoodTags = 6 • (Polynomial.X : Poly)^3 ∧
    argResponse BadTags = 6 • (Polynomial.X : Poly)^2 := by
  constructor
  · rw [argResponse,twoUniform 3 _ separate_supports.1,raw_offsets_identical.1]
  · rw [argResponse,twoUniform 2 _ separate_supports.2,raw_offsets_identical.2]

private theorem normResidues (q : ℕ) (L : List ℕ) :
    (L.map (· % q)).sum % q = L.sum % q := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    calc (a % q + (l.map (· % q)).sum) % q = (a % q + (l.map (· % q)).sum % q) % q := by
           rw [Nat.add_mod (a % q), Nat.mod_mod, Nat.add_mod (a % q) ((l.map (· % q)).sum % q)]
         _ = (a+l.sum)%q := by rw [ih,Nat.add_mod a]

private theorem sumBound (L : List ℕ) (H : ∀ a∈L, a≤7) : L.sum ≤ 7 * L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.forall_mem_cons.mp H
    simp only [List.sum_cons,List.length_cons,Nat.mul_succ]
    have := ih hl; omega

private theorem rawThree (L : List ℕ) (hp : ∀ a ∈ L, a=1 ∨ 3≤a)
    (hs : L.sum = 3) : L = [3] ∨ L = [1,1,1] := by
  have sumPos (K : List ℕ) (H : ∀ a ∈ K, a=1 ∨ 3≤a) : K.length ≤ K.sum := by
    induction K with
    | nil => simp
    | cons a l ih =>
      obtain ⟨q,r⟩ := List.forall_mem_cons.mp H
      have hv := ih r
      simp only [List.length_cons,List.sum_cons]
      omega
  have len := sumPos L hp
  cases L with
  | nil => simp at hs
  | cons a l =>
    cases l with
    | nil => simp_all
    | cons b l =>
      cases l with
      | nil =>
        obtain ⟨pa, pb, -⟩ := List.forall_mem_cons.mp hp |>.imp_right List.forall_mem_cons.mp
        simp at hs; omega
      | cons c l =>
        have hl : l = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at len; omega
        subst l
        simp only [List.sum_cons, List.sum_nil, add_zero] at hs
        obtain ⟨pa, hb⟩ := List.forall_mem_cons.mp hp
        obtain ⟨pb, hc⟩ := List.forall_mem_cons.mp hb
        have pc := hc c (by simp)
        have : a=1 ∧ b=1 ∧ c=1 := by omega
        simp [this.1,this.2.1,this.2.2]

/-- At a marked target only a singleton of residue 3 or three labels of
residue 1 can occur. This is valid uniformly in arbitrary finite h≥3. -/
theorem forced_shape (h : ℕ) (hh : 3≤h) (L : List ℕ) (hlen : L.length ≤h)
    (small : ∀ a∈L, a % (7*h-2) ≤ 7)
    (tags : ∀ a∈L, a % (7*h-2) = 1 ∨ 3≤a % (7*h-2))
    (mark : L.sum % (7*h-2) = 3) :
    L.map (· % (7*h-2)) = [3] ∨ L.map (· % (7*h-2)) = [1,1,1] := by
  let q := 7*h-2
  let s := (L.map (· % q)).sum
  have hs : s ≤ 7*h := by
    have b := sumBound (L.map (· % q)) (by simpa using small)
    simp at b
    exact b.trans (Nat.mul_le_mul_left 7 hlen)
  have hm : s % q = 3 := (normResidues q L).trans mark
  have hq : 19 ≤ q := by dsimp [q]; omega
  have cap : 7*h = q+2 := by dsimp [q]; omega
  have raw : s=3 := by
    by_cases hsq : s < q
    · rwa [Nat.mod_eq_of_lt hsq] at hm
    · have t : s-q < q := by omega
      rw [Nat.mod_eq_sub_mod (by omega : q ≤ s), Nat.mod_eq_of_lt t] at hm
      omega
  exact rawThree _ (by simpa using tags) raw

/-- `window C D t` separates all earlier and later blocks, retaining
only the actual local offset choices D in the current shell. -/
def window (C : ℕ) (D : List ℕ) (t : ℕ) : Prop :=
    t ≤ C/10+7 ∨ (∃ a∈D, t=C+a) ∨ 10*C ≤ t

theorem isolate_three (C : ℕ) (hC : 100≤C) (D : List ℕ) (hd : ∀ v∈D, v≤7)
    (x y z : ℕ) (hx : window C D x) (hy : window C D y) (hz : window C D z)
    (hs : x+y+z = 3*C+9) :
    (∃ a∈D, x=C+a) ∧ (∃ b∈D, y=C+b) ∧ (∃ c∈D, z=C+c) := by
  have cut (t : ℕ) (ht : window C D t) (hn : t < 10*C) :
      t ≤ C/10+7 ∨ (∃ a∈D, t=C+a) := ht.elim Or.inl (fun h => h.elim Or.inr (fun hh => False.elim (by omega)))
  have cx := cut x hx (by omega)
  have cy := cut y hy (by omega)
  have cz := cut z hz (by omega)
  have bound (t : ℕ) (H : t≤C/10+7 ∨ ∃ a∈D,t=C+a) : t≤C+7 := by
    rcases H with H|⟨a,ha,rfl⟩
    · omega
    · have := hd a ha; omega
  have bx := bound _ cx; have by' := bound _ cy; have bz := bound _ cz
  exact ⟨cx.resolve_left (by omega),cy.resolve_left (by omega),cz.resolve_left (by omega)⟩

#print axioms two_response_polynomials
#print axioms forced_shape
#print axioms isolate_three
end Erdos338.Thinning.Stencils
