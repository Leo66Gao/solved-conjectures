import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! Kernel-checked first- and second-bit identities used by the lattice expansion. -/
namespace Erdos23.ModFour

def bit0 (a : ZMod 4) : ZMod 2 := (a.val : ZMod 2)

def bit1 (a : ZMod 4) : ZMod 2 := ((a.val / 2 : ℕ) : ZMod 2)

theorem bit0_add : ∀ a b, bit0 (a+b) = bit0 a + bit0 b := by decide

theorem bit0_mul : ∀ a b, bit0 (a*b) = bit0 a * bit0 b := by decide

theorem bit_neg : ∀ a, bit1 (-a) = bit1 a + bit0 a := by decide

theorem bit_add : ∀ a b, bit1 (a+b) = bit1 a + bit1 b + bit0 a * bit0 b := by decide

theorem bit_mul : ∀ a b, bit1 (a*b) = bit0 b * bit1 a + bit0 a * bit1 b := by decide

theorem bit_shift : ∀ a b : ZMod 4, bit1 (a+2*b) = bit1 a+bit0 b := by decide

theorem bit_zero : bit1 0 = 0 := by decide

theorem bit_two : bit1 2 = 1 := by decide

theorem bit_three : bit1 3 = 1 := by decide

/-- Algebraic expansion of the distance bit after writing a+b-z. -/
theorem bit_halfnorm_sub : ∀ a b z : ZMod 4,
    bit1 (a+b-z) =
      bit1 a + bit1 b + bit1 z + bit0 z + bit0 a * bit0 b +
        (bit0 a + bit0 b)*bit0 z := by decide


/-- Each unordered pair occurs once, at its earlier index. -/
def pairProduct : List (ZMod 4) → ZMod 2
  | [] => 0
  | a::as => bit0 a * (as.map bit0).sum + pairProduct as

theorem bit0_sum (l : List (ZMod 4)) : bit0 l.sum = (l.map bit0).sum := by
  induction l with
  | nil => decide
  | cons a l ih => simp [List.sum_cons, bit0_add, ih]

theorem bit1_sum (l : List (ZMod 4)) :
    bit1 l.sum = (l.map bit1).sum + pairProduct l := by
  induction l with
  | nil => decide
  | cons a l ih =>
    simp only [List.sum_cons, bit_add, ih, bit0_sum, List.map_cons, pairProduct]
    ring

end Erdos23.ModFour
