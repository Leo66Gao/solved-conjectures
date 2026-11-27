import CatalogueAdapter
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos338.Structural.ResidueCore
open Erdos338.CatalogueAdapter

/-- The distinguished core is a full residue class. The complement may
    have infinitely many elements and need not be eventually periodic. -/
def Outside (A : Set ℕ) (q c : ℕ) : Set ℕ := {a | a ∈ A ∧ a % q ≠ c}

/-- At every residue there are arbitrarily large integers not covered by
    a sum of at most h outside elements, even with repetition. -/
def Escapes (S : Set ℕ) (q h : ℕ) : Prop :=
  ∀ r < q, ∀ M, ∃ n ≥ M, n % q = r ∧ ¬ Erdos338.Ordinary S h n

/-- Compress each representation having a core element to one weighted
    outside payload and a number of core slots, forgetting all core labels.
    The outside payload will be reduced to capped residue counts below. -/
def Payload (S : Set ℕ) (q c h r : ℕ) (distinct : Bool) : Prop :=
  ∃ (k : ℕ) (xs : List ℕ), 0 < k ∧ k + xs.length ≤ h ∧
    (∀ x ∈ xs, x ∈ S) ∧ (distinct = true → xs.Nodup) ∧
    (k*c + xs.sum) % q = r

private theorem sum_mod_of_constant {q c : ℕ} (xs : List ℕ)
    (hm : ∀ x ∈ xs, x % q = c) : xs.sum % q = (xs.length*c) % q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hm x (by simp)
    have ht := ih (fun y hy => hm y (by simp [hy]))
    have hcc : c % q = c := by rw [←hx, Nat.mod_mod]
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_mod x xs.sum, hx, ht, Nat.add_mod (xs.length*c) c, hcc, Nat.add_comm c]

private theorem filterTotals (p : ℕ → Bool) (xs : List ℕ) :
    (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length ∧
    (xs.filter p).sum + (xs.filter (fun x => !p x)).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases e : p x <;> simp [e] <;> obtain ⟨h1,h2⟩ := ih <;> omega

private theorem split_payload {A : Set ℕ} {q c h n : ℕ} {xs : List ℕ}
    (hc : ∃ x ∈ xs, x % q = c) (hm : ∀ x ∈ xs, x ∈ A)
    (hb : xs.length ≤ h) (hs : xs.sum = n) {d : Bool}
    (hd : d = true → xs.Nodup) : Payload (Outside A q c) q c h (n % q) d := by
  let ys := xs.filter (fun x => decide (x % q = c))
  let zs := xs.filter (fun x => !decide (x % q = c))
  have hy : ys ≠ [] := by
    obtain ⟨x,hx,he⟩ := hc
    have hx' : x ∈ ys := by simp [ys,hx,he]
    intro e
    simp [e] at hx'
  obtain ⟨hl, hsum⟩ := filterTotals (fun x => decide (x % q = c)) xs
  change ys.length + zs.length = xs.length at hl
  change ys.sum + zs.sum = xs.sum at hsum
  refine ⟨ys.length,zs,List.length_pos_iff.mpr hy, by omega, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ xs ∧ x % q ≠ c := by simpa [zs] using hx
    exact ⟨hm x hx'.1,hx'.2⟩
  · intro he
    exact (hd he).filter _
  · have hyc : ∀ x ∈ ys, x % q = c := by
      intro x hx
      exact of_decide_eq_true (List.mem_filter.mp hx).2
    rw [←hs, ←hsum, Nat.add_mod (ys.length*c) zs.sum, Nat.add_mod ys.sum zs.sum,
      sum_mod_of_constant ys hyc]

/-- Distinct core labels can always be installed: preselect k-1, and let the
    last label absorb all of the unbounded target. -/
private theorem lift_payload {A : Set ℕ} {q c h r : ℕ} {d : Bool}
    (hq : 0 < q) (hrc : c < q) (core : ∀ a, a % q = c → a ∈ A)
    (hp : Payload (Outside A q c) q c h r d) :
    ∃ N, ∀ n ≥ N, n % q = r → ∃ xs : List ℕ, xs.length ≤ h ∧
      (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n ∧ (d = true → xs.Nodup) := by
  obtain ⟨k,xs,hk,hkxs,hxs,hnd,hr⟩ := hp
  let ys := (List.range (k-1)).map (fun i => q*i+c)
  have ly : ys.length = k-1 := by simp [ys]
  have ymod : ∀ y ∈ ys, y % q = c := by
    intro y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hy
    simp [Nat.add_mod, Nat.mod_eq_of_lt hrc, Nat.mul_mod_right]
  have ynd : ys.Nodup := by
    exact List.Nodup.map (fun i j he => Nat.eq_of_mul_eq_mul_left hq (by omega)) List.nodup_range
  have disj : List.Disjoint ys xs := by
    intro x hy hx
    exact (hxs x hx).2 (ymod x hy)
  have sumMod : (ys.sum + xs.sum + c) % q = r := by
    calc
      _ = (ys.sum + c + xs.sum) % q := by congr 1; omega
      _ = (k*c + xs.sum) % q := by
        have hk' : ys.length + 1 = k := by omega
        have hp' : ys.length*c + c = k*c := by rw [←Nat.succ_mul, Nat.succ_eq_add_one, hk']
        have hy' : (ys.sum + c) % q = (k*c) % q := by
          rw [Nat.add_mod ys.sum c, sum_mod_of_constant ys ymod, ←Nat.add_mod, hp']
        rw [Nat.add_mod (ys.sum+c) xs.sum, Nat.add_mod (k*c) xs.sum, hy']
      _ = r := hr
  refine ⟨ys.sum + xs.sum + (ys.sum + xs.sum + 1), ?_⟩
  intro n hn hnr
  let z := n - (ys.sum + xs.sum)
  have hzsum : z + (ys.sum + xs.sum) = n := by dsimp [z]; omega
  have hzmod : z % q = c := by
    have equ : (z + (ys.sum + xs.sum)) % q = (c + (ys.sum + xs.sum)) % q := by
      rw [hzsum,hnr, ←sumMod]; congr 1; omega
    have hi : z % q = c % q := (Nat.ModEq.add_right_cancel' (ys.sum + xs.sum) equ)
    simpa [Nat.mod_eq_of_lt hrc] using hi
  refine ⟨z :: (ys ++ xs), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_append]; omega
  · intro x hx
    rcases List.mem_cons.mp hx with he| he
    · exact he ▸ core _ hzmod
    · rcases List.mem_append.mp he with hy| hx
      · exact core _ (ymod _ hy)
      · exact (hxs _ hx).1
  · simp only [List.sum_cons, List.sum_append]; omega
  · intro hd
    have hlarge : ∀ x ∈ ys ++ xs, x < z := by
      intro x hx
      have hh' : x ≤ (ys ++ xs).sum := List.le_sum_of_mem hx
      rw [List.sum_append] at hh'
      dsimp [z]
      omega
    exact List.nodup_cons.mpr
      ⟨fun hx => (Nat.lt_irrefl z) (hlarge _ hx), List.nodup_append.mpr ⟨ynd, hnd hd, fun _ hy _ hx he => disj hy (he.symm ▸ hx)⟩⟩

theorem profile_iff {A : Set ℕ} {q c h : ℕ} (hq : 0 < q) (hc : c < q)
    (core : ∀ a, a % q = c → a ∈ A) (escape : Escapes (Outside A q c) q h)
    (d : Bool) :
    (Erdos338.Cofinite (fun n => ∃ xs : List ℕ, xs.length ≤ h ∧
      (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n ∧ (d = true → xs.Nodup))) ↔
    ∀ r < q, Payload (Outside A q c) q c h r d := by
  constructor
  · rintro ⟨N,hN⟩ r hr
    obtain ⟨n,hn,hres,hbad⟩ := escape r hr N
    obtain ⟨xs,hxs,hm,hs,hd⟩ := hN n hn
    by_cases he : ∃ x ∈ xs, x % q = c
    · rw [← hres]
      exact split_payload he hm hxs hs hd
    · exact False.elim (hbad ⟨xs,hxs,
        fun x hx => ⟨hm x hx, fun hh => he ⟨x,hx,hh⟩⟩,hs⟩)
  · intro profile
    classical
    have H : ∀ r : Fin q, ∃ N, ∀ n ≥ N, n % q = r.val → ∃ xs : List ℕ,
        xs.length ≤ h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n ∧ (d = true → xs.Nodup) :=
      fun r => lift_payload hq hc core (profile r r.isLt)
    choose cutoff ht using H
    refine ⟨∑ r : Fin q, cutoff r, ?_⟩
    intro n hn
    let r : Fin q := ⟨n % q,Nat.mod_lt n hq⟩
    have hh : cutoff r ≤ ∑ j : Fin q, cutoff j :=
      Finset.single_le_sum (fun (j : Fin q) _ => Nat.zero_le (cutoff j)) (Finset.mem_univ r)
    exact ht r n (hh.trans hn) rfl


/-- A residue's capacity is the amount of inventory it supplies, queried
    only at demand k ≤ h. It does not record the identities of any labels. -/
def Supplies (S : Set ℕ) (q r k : ℕ) : Prop :=
  ∃ s : Finset ℕ, k ≤ s.card ∧ ∀ a ∈ s, a ∈ S ∧ a % q = r

def Profile (S : Set ℕ) (q c h r : ℕ) (d : Bool) : Prop :=
  ∃ (k : ℕ) (rs : List ℕ), 0 < k ∧ k + rs.length ≤ h ∧
    (∀ u ∈ rs, Supplies S q u 1) ∧
    (d = true → ∀ u, Supplies S q u (rs.count u)) ∧
    (k*c + rs.sum) % q = r

private theorem supply_mono {S : Set ℕ} {q r i j : ℕ}
    (h : i ≤ j) : Supplies S q r j → Supplies S q r i := by
  rintro ⟨s,hs,H⟩
  exact ⟨s,h.trans hs,H⟩

private theorem zero_supply (S : Set ℕ) (q r : ℕ) : Supplies S q r 0 :=
  ⟨∅,by simp, by simp⟩

private theorem filter_count (xs : List ℕ) (q r : ℕ) :
    (xs.filter (fun x => x % q == r)).length = (xs.map (· % q)).count r := by
  rw [List.count_eq_length_filter, List.filter_map, List.length_map]
  rfl

private theorem modSum (xs : List ℕ) (q : ℕ) :
    xs.sum % q = (xs.map (· % q)).sum % q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons,List.map_cons]
    rw [Nat.add_mod x xs.sum, ih, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem lift_residue_word {S : Set ℕ} {q : ℕ} {d : Bool} (rs : List ℕ)
    (members : ∀ u ∈ rs, Supplies S q u 1)
    (caps : d = true → ∀ u, Supplies S q u (rs.count u)) :
    ∃ xs : List ℕ, xs.map (· % q) = rs ∧ (∀ x ∈ xs, x ∈ S) ∧
      (d = true → xs.Nodup) := by
  induction rs with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons r rs ih =>
    have tailCaps : d = true → ∀ u, Supplies S q u (rs.count u) := by
      intro hd u
      apply supply_mono (j := (r::rs).count u)
      · by_cases h : r = u
        · subst r; simp
        · simp [List.count_cons_of_ne h]
      · exact caps hd u
    obtain ⟨xs,hmap,hmem,hnd⟩ := ih (fun u hu => members u (by simp [hu])) tailCaps
    have hx : ∃ a, a ∈ S ∧ a % q = r ∧ (d = true → a ∉ xs) := by
      by_cases hd : d = true
      · obtain ⟨s,hs,hspec⟩ := caps hd r
        have hnew : ∃ a ∈ s, a ∉ xs := by
          by_contra! hAll
          let t := xs.filter (fun a => a % q == r)
          have hst : s ⊆ t.toFinset := by
            intro a ha
            exact List.mem_toFinset.mpr (List.mem_filter.mpr
              ⟨hAll a ha, by simpa using (hspec a ha).2⟩)
          have hcard := Finset.card_le_card hst
          have hfilter : t.Nodup := (hnd hd).filter _
          rw [List.toFinset_card_of_nodup hfilter] at hcard
          have hcount : t.length = rs.count r := by
            change (xs.filter (fun x => x % q == r)).length = rs.count r
            rw [filter_count, hmap]
          rw [hcount] at hcard
          simp only [List.count_cons_self] at hs
          omega
        obtain ⟨a,ha,hout⟩ := hnew
        exact ⟨a,(hspec a ha).1,(hspec a ha).2,fun _ => hout⟩
      · obtain ⟨s,hs,hspec⟩ := members r (by simp)
        obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
        exact ⟨a,(hspec a ha).1,(hspec a ha).2,fun he => (hd he).elim⟩
    obtain ⟨a,ha,har,hfresh⟩ := hx
    refine ⟨a::xs,by simp [har,hmap],?_,fun hd => List.nodup_cons.mpr ⟨hfresh hd,hnd hd⟩⟩
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · exact hx ▸ ha
    · exact hmem x hx

theorem payload_iff_profile {S : Set ℕ} {q c h r : ℕ} {d : Bool} :
    Payload S q c h r d ↔ Profile S q c h r d := by
  constructor
  · rintro ⟨k,xs,hk,hb,hmem,hnd,hr⟩
    refine ⟨k,xs.map (· % q),hk,by simpa,?_,?_,?_⟩
    · intro u hu
      obtain ⟨x,hx,hxu⟩ := List.mem_map.mp hu
      refine ⟨{x},by simp,?_⟩
      simpa using ⟨hmem x hx,hxu⟩
    · intro hd u
      let t := xs.filter (fun x => x % q == u)
      refine ⟨t.toFinset,?_,?_⟩
      · rw [List.toFinset_card_of_nodup ((hnd hd).filter _)]
        exact (filter_count xs q u).ge
      · intro a ha
        obtain ⟨ha',hmod⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
        exact ⟨hmem _ ha', by simpa using hmod⟩
    · rw [Nat.add_mod (k*c) ((xs.map (· % q)).sum), ←modSum, ←Nat.add_mod]
      exact hr
  · rintro ⟨k,rs,hk,hb,hmem,hnd,hr⟩
    obtain ⟨xs,hmap,hm,hn⟩ := lift_residue_word rs hmem hnd
    have hlen : xs.length = rs.length := by rw [←hmap,List.length_map]
    refine ⟨k,xs,hk,by simpa [hlen],hm,hn,?_⟩
    rw [Nat.add_mod (k*c) xs.sum, modSum,hmap,←Nat.add_mod]
    exact hr

theorem restricted_iff_finite_profile {A : Set ℕ} {q c h : ℕ}
    (hq : 0 < q) (hc : c < q) (core : ∀ a, a % q = c → a ∈ A)
    (escape : Escapes (Outside A q c) q h) :
    HasRestrictedOrder A h ↔ ∀ r < q, Profile (Outside A q c) q c h r true := by
  simp only [← payload_iff_profile]
  rw [restricted_iff_list]
  rw [←profile_iff hq hc core escape true]
  unfold Growth.RestrictedAtMost
  constructor <;> rintro ⟨N,hN⟩ <;> refine ⟨N, fun n hn => ?_⟩
  · obtain ⟨xs,hn,hm,hs,hl⟩ := hN n hn
    exact ⟨xs,hl,hm,hs,fun _ => hn⟩
  · obtain ⟨xs,hl,hm,hs,hd⟩ := hN n hn
    exact ⟨xs,hd rfl,hm,hs,hl⟩

theorem ordinary_iff_finite_profile {A : Set ℕ} {q c h : ℕ}
    (hq : 0 < q) (hc : c < q) (core : ∀ a, a % q = c → a ∈ A)
    (escape : Escapes (Outside A q c) q h) :
    HasOrder A h ↔ ∀ r < q, Profile (Outside A q c) q c h r false := by
  simp only [← payload_iff_profile]
  rw [ordinary_iff_list]
  rw [←profile_iff hq hc core escape false]
  unfold Growth.Mixed.OrdinaryAtMost
  constructor <;> rintro ⟨N,hN⟩ <;> refine ⟨N, fun n hn => ?_⟩
  · obtain ⟨xs,hm,hs,hl⟩ := hN n hn
    exact ⟨xs,hl,hm,hs,by simp⟩
  · obtain ⟨xs,hl,hm,hs,_⟩ := hN n hn
    exact ⟨xs,hm,hs,hl⟩


/-- The infimum of a nonempty set of natural budgets gives its least budget. -/
theorem least_budget_iff (p : ℕ → Prop) (h : ℕ) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = (h : ℕ∞) ↔ p h ∧ ∀ k < h, ¬p k := by
  classical
  have minimum {j : ℕ} (hj : p j) (hl : ∀ k < j, ¬p k) :
      (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = (j : ℕ∞) := by
    apply le_antisymm
    · exact iInf_le_of_le j (iInf_le_of_le hj le_rfl)
    · refine le_iInf fun k => le_iInf fun hk => ENat.natCast_le_natCast.mpr ?_
      exact Nat.le_of_not_gt fun hkh => hl k hkh hk
  constructor
  · intro he
    by_cases hp : ∃ n, p n
    · have hl : ∀ k < Nat.find hp, ¬p k :=
        fun k hk hpk => Nat.not_le_of_gt hk (Nat.find_min' hp hpk)
      have e : Nat.find hp = h := by
        simpa using (minimum (Nat.find_spec hp) hl).symm.trans he
      exact e ▸ ⟨Nat.find_spec hp,hl⟩
    · have heq : (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = ⊤ := by
        apply top_unique
        exact le_iInf fun k => le_iInf fun hk => (hp ⟨k,hk⟩).elim
      exact (ENat.natCast_ne_top h (he.symm.trans heq)).elim
  · exact fun ⟨hh,hl⟩ => minimum hh hl

theorem restricted_to_ordinary {A : Set ℕ} {h : ℕ}
    (R : HasRestrictedOrder A h) : HasOrder A h := by
  rw [restricted_iff_list] at R
  rw [ordinary_iff_list]
  obtain ⟨N,hN⟩ := R
  exact ⟨N, fun n hn => by
    obtain ⟨xs,_,hm,hs,hl⟩ := hN n hn
    exact ⟨xs,hm,hs,hl⟩⟩

theorem equal_orders_iff_finite_profile {A : Set ℕ} {q c h : ℕ}
    (base : basisOrder A = (h : ℕ∞))
    (hq : 0 < q) (hc : c < q) (core : ∀ a, a % q = c → a ∈ A)
    (escape : Escapes (Outside A q c) q h) :
    restrictedOrder A = (h : ℕ∞) ↔
      ∀ r < q, Profile (Outside A q c) q c h r true := by
  rw [basisOrder, least_budget_iff] at base
  rw [restrictedOrder, least_budget_iff, restricted_iff_finite_profile hq hc core escape]
  exact and_iff_left (fun k hk hr => base.2 k hk (restricted_to_ordinary hr))

end Erdos338.Structural.ResidueCore
