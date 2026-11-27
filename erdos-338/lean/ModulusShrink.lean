import Erdos335.FiniteKneser
import Mathlib.Tactic

/-!
If a donor is frequently dense compared with its allowed multiplicity, it
shortens the period of a known eventual ray. Uses the pinned finite Kneser
theorem of Bakšys and Dillies.
-/

open scoped Pointwise BigOperators
open Filter Topology Erdos335
namespace Erdos338.Shrink

def copies (C : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | j+1 => copies C j + C

private def fc {G : Type*} [AddCommMonoid G] [DecidableEq G] (B : Finset G) : ℕ → Finset G
  | 0 => {0}
  | j+1 => fc B j + B

private theorem zero_fc {G : Type*} [AddCommMonoid G] [DecidableEq G] {B : Finset G}
    (hB : 0∈B) (j : ℕ) : 0∈fc B j := by
  induction j with
  | zero => simp [fc]
  | succ j ih => simpa only [fc, add_zero] using Finset.add_mem_add ih hB

private theorem fc_add {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (B : Finset G) (i j : ℕ) : fc B (i+j) = fc B i + fc B j := by
  induction j with
  | zero =>
    change fc B i = fc B i + 0
    simp
  | succ j ih =>
    rw [Nat.add_succ]
    simp only [fc, ih, add_assoc]

private theorem stab_mono_copies {G : Type*} [AddCommGroup G] [DecidableEq G]
    {B : Finset G} (hB : 0∈B) {i j : ℕ} (hij : i≤j) :
    (fc B i).addStab ⊆ (fc B j).addStab := by
  have he : j=i+(j-i) := by omega
  conv_rhs => rw [he,fc_add]
  exact Finset.subset_addStab_add_left ⟨0,zero_fc hB _⟩

private theorem lc_subset_add_right {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A H : Finset G) (hH : 0∈H) : A ⊆ A+H := by
  intro a ha
  simpa only [add_zero] using Finset.add_mem_add ha hH

/-- In a finite group, a high-cardinality donor generates its whole subgroup
within the allowed number of repetitions. -/
private theorem copies_eq_stab {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    {B : Finset G} (hB : 0∈B) (L : ℕ)
    (dense : 2*Fintype.card G < L*B.card) :
    fc B L = (fc B L).addStab := by
  classical
  let U := fc B L
  let K := U.addStab
  have hU0 := zero_fc hB L
  have hK0 : 0∈K := Finset.zero_mem_addStab.mpr ⟨0,hU0⟩
  have hKU : K ⊆ U := by
    intro k hk
    have hc := Finset.add_mem_add hU0 hk
    change 0 + k ∈ U+U.addStab at hc
    simpa [Finset.add_addStab] using hc
  suffices hBK : B ⊆ K by
    have h : ∀ j, fc B j ⊆ K := by
      intro j
      induction j with
      | zero => simpa [fc] using hK0
      | succ j ih =>
        have hh := Finset.add_subset_add ih hBK
        change fc B j + B ⊆ U.addStab+U.addStab at hh
        rw [Finset.addStab_add_addStab] at hh
        exact hh
    exact Finset.Subset.antisymm (h L) hKU
  by_contra h'
  change ¬ (∀ b, b∈B → b∈K) at h'
  push Not at h'
  obtain ⟨b,hb,hbK⟩ := h'
  have step (j : ℕ) (hj : j+1≤L) :
      B.card + 2*(fc B j).card ≤ 2*(fc B (j+1)).card := by
    let P := fc B j
    let V := fc B (j+1)
    let H := V.addStab
    have hH0 : 0∈H := Finset.zero_mem_addStab.mpr ⟨0,zero_fc hB _⟩
    have hh : H ⊆ K := stab_mono_copies hB hj
    have hbH : b∉H := fun hm => hbK (hh hm)
    have hHB : H ⊆ B+H := by
      intro x hx
      simpa only [zero_add] using Finset.add_mem_add hB hx
    have hbBH : b∈B+H := by simpa only [add_zero] using Finset.add_mem_add hb hH0
    have hstrict : H ⊂ B+H := Finset.ssubset_iff_subset_ne.mpr
      ⟨hHB, fun he => hbH (he.symm ▸ hbBH)⟩
    have hA := Finset.card_lt_card hstrict
    have hdiv : H.card ∣ (B+H).card := Finset.card_addStab_dvd_card_add_addStab B V
    obtain ⟨u,hu⟩ := hdiv
    have hbig : 2*H.card ≤ (B+H).card := by
      by_cases hc : 2≤u
      · rw [hu,Nat.mul_comm 2 H.card]
        exact Nat.mul_le_mul_left _ hc
      · interval_cases u <;> simp_all
    have hBc := Finset.card_le_card (lc_subset_add_right B H hH0)
    have hPc := Finset.card_le_card (lc_subset_add_right P H hH0)
    have hk := Finset.add_kneser P B
    change (P+H).card+(B+H).card≤V.card+H.card at hk
    change B.card + 2*P.card ≤ 2*V.card
    omega
  have h : ∀ j≤L, j*B.card≤2*(fc B j).card := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hs := step j hj
      rw [Nat.succ_mul]
      omega
  have hu : U.card≤Fintype.card G := Finset.card_le_univ _
  have hh := h L le_rfl
  change L*B.card≤2*U.card at hh
  omega

private theorem copies_residues (m : ℕ) [NeZero m] (C : Set ℕ) (j : ℕ) :
    residues m (copies C j) = fc (residues m C) j := by
  classical
  induction j with
  | zero => ext x; simp [copies,fc,eq_comm]
  | succ j ih => simp only [copies,fc,residues_add,ih]

private theorem dense_residues (m : ℕ) [NeZero m] (C : Set ℕ) (L : ℕ)
    (dense : ∀ K, ∃ N≥K, 3*N≤L*count C N) :
    3*m≤L*(residues m C).card := by
  classical
  let P := periodicSet (residues m C)
  have hc (N : ℕ) : count C N ≤ count P N := by
    apply count_le_count_add C P 0 _ N |>.trans_eq
    · simp
    intro n hn hC
    exact ⟨hn,mem_residues.mpr ⟨n,hC,rfl⟩⟩
  by_contra! hh
  have hm : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hreal : (L:ℝ)*(↑(residues m C).card / m) < 3 := by
    rw [← mul_div_assoc]; apply (div_lt_iff₀ hm).mpr
    exact_mod_cast hh
  have hd : Tendsto (fun N : ℕ => (L:ℝ)*((count P N : ℝ)/N)) atTop
      (𝓝 ((L:ℝ)*(↑(residues m C).card / m))) :=
    (hasDensity_periodicSet (residues m C)).const_mul _
  have hEv := (tendsto_order.mp hd).2 3 hreal
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hEv
  obtain ⟨N,hN,hcnt⟩ := dense (max 1 N₀)
  have hlt := hN₀ N (by omega)
  have hp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  rw [← mul_div_assoc] at hlt
  have hbad := (div_lt_iff₀ hp).mp hlt
  have hcomp := (Nat.mul_le_mul_left L (hc N))
  have hn := hcnt.trans hcomp
  exact (not_lt_of_ge (by exact_mod_cast hn)) hbad

private theorem cyclic_subgroup_lattice (m : ℕ) [NeZero m]
    (U : Finset (ZMod m)) (h0 : 0∈U) (hU : U=U.addStab) :
    ∃ g e : ℕ, 0<g ∧ 0<e ∧ m=g*e ∧ U.card≤e ∧
      ∀ n : ℕ, ((n:ZMod m)∈U ↔ g∣n) := by
  classical
  let H := AddAction.stabilizer (ZMod m) (↑U : Set (ZMod m))
  have hmatch (x : ZMod m) : x∈U ↔ x∈H := by
    change x∈(↑U : Set (ZMod m)) ↔ x∈(↑H : Set (ZMod m))
    rw [← Finset.coe_addStab (show U.Nonempty from ⟨0,h0⟩)]
    rw [← hU]
  let P (n : ℕ) : Prop := 0<n ∧ (n:ZMod m)∈H
  have hex : ∃ n, P n :=
    ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), by simp⟩
  let g := Nat.find hex
  have hp : P g := Nat.find_spec hex
  have hg : 0<g := hp.1
  have hmul (k : ℕ) : ((g*k:ℕ):ZMod m)∈H := by
    have h := H.nsmul_mem hp.2 k
    simpa [nsmul_eq_mul,Nat.cast_mul,mul_comm] using h
  have hh (n : ℕ) : ((n:ZMod m)∈H ↔ g∣n) := by
    constructor
    · intro hn
      have hr : ((n%g:ℕ):ZMod m)∈H := by
        have hh' := H.sub_mem hn (hmul (n/g))
        have he : ((n%g:ℕ):ZMod m) + ((g*(n/g):ℕ):ZMod m) = (n:ZMod m) := by
          rw [← Nat.cast_add,Nat.mod_add_div]
        rwa [← he, add_sub_cancel_right] at hh'
      have hzero : n%g=0 := by
        by_contra hne
        have hp' : P (n%g) := ⟨Nat.pos_of_ne_zero hne,hr⟩
        have hb := Nat.find_min' hex hp'
        have hc := Nat.mod_lt n hg
        omega
      exact Nat.dvd_of_mod_eq_zero hzero
    · rintro ⟨k,rfl⟩
      exact hmul k
  have hgd : g∣m := (hh m).mp (by simp)
  obtain ⟨e,he⟩ := hgd
  have hep : 0<e := by
    by_contra! hbad
    have hz : e=0 := by omega
    exact NeZero.ne m (by simpa [hz] using he)
  have sub : U ⊆ (Finset.range e).image (fun k : ℕ => ((g*k:ℕ):ZMod m)) := by
    intro r hr
    have hmem : (r.val : ZMod m) ∈ U := by simpa using hr
    obtain ⟨u, hu⟩ := (hh r.val).1 ((hmatch _).1 hmem)
    have hul : g*u < g*e := by rw [← hu,← he]; exact ZMod.val_lt r
    have hl : u<e := Nat.lt_of_mul_lt_mul_left hul
    exact Finset.mem_image.mpr ⟨u,Finset.mem_range.mpr hl,
      by rw [← hu,ZMod.natCast_zmod_val]⟩
  have hcard := (Finset.card_le_card sub).trans Finset.card_image_le
  rw [Finset.card_range] at hcard
  exact ⟨g,e,hg,hep,he,hcard,fun n => (hmatch _).trans (hh n)⟩

/-- Shrink the modulus of an eventual ray by appending a fixed number
of copies of one recurrently dense donor. The same starting residue
representative a works modulo the new modulus. -/
theorem shrink_eventual_ray (S C : Set ℕ) (m a T L : ℕ)
    (hm : 0<m) (h0 : 0∈C)
    (hS : ∀ n≥T, n%m=a%m → n∈S)
    (dense : ∀ K, ∃ N≥K, 3*N≤L*count C N) :
    ∃ g K : ℕ, 0<g ∧ 3*g≤L ∧ ∀ n≥K, n%g=a%g → n∈S+copies C L := by
  classical
  let _ : NeZero m := NeZero.of_pos hm
  let B := residues m C
  let U := residues m (copies C L)
  have hB0 : 0∈B := mem_residues.mpr ⟨0,h0,by simp⟩
  have hUeq : U=fc B L := copies_residues m C L
  have hd : 3*m≤L*B.card := dense_residues m C L dense
  have hcG : Fintype.card (ZMod m) = m := by
    rw [← Nat.card_eq_fintype_card,Nat.card_zmod]
  have hlarge : 2*Fintype.card (ZMod m)<L*B.card := by rw [hcG]; omega
  have hUstab : U=U.addStab := by
    rw [hUeq]
    exact copies_eq_stab hB0 L hlarge
  have hU0 : 0∈U := by rw [hUeq]; exact zero_fc hB0 L
  obtain ⟨g,e,hg,hep,he,hcap,hchar⟩ := cyclic_subgroup_lattice m U hU0 hUstab
  have hL : 0<L := by
    by_contra! hh
    have hzero : L=0 := by omega
    simp [hzero] at hd
    omega
  have hsub : B ⊆ U := by
    intro b hb
    rw [hUeq]
    have hmem := Finset.add_mem_add (zero_fc hB0 (L-1)) hb
    change (0:ZMod m)+b ∈ fc B (L-1+1) at hmem
    simpa only [Nat.sub_add_cancel (Nat.succ_le_of_lt hL),zero_add] using hmem
  have hdcard := (Finset.card_le_card hsub).trans hcap
  have hmul := hd.trans (Nat.mul_le_mul_left L hdcard)
  have hgle : 3*g≤L := by
    rw [he,← Nat.mul_assoc] at hmul
    exact Nat.le_of_mul_le_mul_right hmul hep
  have hx (r : ZMod m) (hr : r∈U) : ∃ w∈copies C L, (w:ZMod m)=r :=
    mem_residues.mp hr
  let f (r : ZMod m) : ℕ := if hr : r∈U then (hx r hr).choose else 0
  have spec {r : ZMod m} (hr : r∈U) : f r∈copies C L ∧ (f r:ZMod m)=r := by
    simpa [f,hr] using (hx r hr).choose_spec
  obtain ⟨r0,_,hM⟩ := Finset.exists_max_image U f ⟨0,hU0⟩
  refine ⟨g,T+f r0+a,hg,hgle,?_⟩
  intro n hn heq
  have han : a≤n := by omega
  have nh := Nat.mod_add_div n g
  have ah := Nat.mod_add_div a g
  have hdif : n-a = g*(n/g-a/g) := by
    rw [Nat.mul_sub]
    omega
  have hmemb : ((n-a:ℕ):ZMod m)∈U := (hchar (n-a)).mpr ⟨_,hdif⟩
  let w := f ((n-a:ℕ):ZMod m)
  have hmw : w≤f r0 := hM _ hmemb
  obtain ⟨hw,hcast⟩ := spec hmemb
  have hwn : w≤n := by omega
  have hwt : T≤n-w := by omega
  have ha' : ((n-w:ℕ):ZMod m)=(a:ZMod m) := by
    have hew : (w:ZMod m)=((n-a:ℕ):ZMod m) := hcast
    rw [Nat.cast_sub hwn,hew,Nat.cast_sub han]
    abel
  have hres : (n-w)%m = a%m := (ZMod.natCast_eq_natCast_iff _ _ _).mp ha'
  exact ⟨n-w,hS _ hwt hres,w,hw,Nat.sub_add_cancel hwn⟩

/-- Public interface relating pointwise copies to exact-length lists.
Zero may be used for padding when it belongs to the donor. -/
theorem mem_copies_iff (C : Set ℕ) (L n : ℕ) :
    n ∈ copies C L ↔
      ∃ xs : List ℕ, xs.length=L ∧ (∀ x∈xs, x∈C) ∧ xs.sum=n := by
  induction L generalizing n with
  | zero => simp [copies,eq_comm]
  | succ k ih =>
    constructor
    · rintro ⟨a,ha,b,hb,hab⟩
      obtain ⟨xs,hx,hm,hs⟩ := (ih a).mp ha
      refine ⟨b::xs,by simp [hx],?_ ,?_⟩
      · intro x h
        rcases List.mem_cons.mp h with rfl | hh
        · exact hb
        · exact hm x hh
      · change a+b=n at hab
        simp [hs,add_comm,hab]
    · rintro ⟨xs,hx,hm,hs⟩
      cases xs with
      | nil => simp at hx
      | cons b xs =>
        have hlen : xs.length=k := by simpa using hx
        have hx' : xs.sum ∈ copies C k := (ih _).2
          ⟨xs,hlen,fun x h => hm x (List.mem_cons_of_mem _ h),rfl⟩
        exact ⟨xs.sum,hx',b,hm b (by simp),by simpa [List.sum_cons,add_comm] using hs⟩

#print axioms copies_eq_stab
#print axioms dense_residues
#print axioms cyclic_subgroup_lattice
#print axioms shrink_eventual_ray
#print axioms mem_copies_iff
end Erdos338.Shrink
