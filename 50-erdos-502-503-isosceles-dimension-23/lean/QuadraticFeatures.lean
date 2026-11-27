import Rank23

/-! General quadratic feature forms. This constructs the polar form from
products of linear feature coordinates, so polarization is not an assumption. -/
namespace Erdos23
open scoped BigOperators

abbrev Lin (D : ℕ) := Slots D →ₗ[F] F

def Polynomial {D m : ℕ} (a b : Fin m → Lin D) (l : Lin D) (x : Slots D) : F :=
  (∑ j, a j x * b j x) + l x

def productPolar {D : ℕ} (a b : Lin D) : Slots D →ₗ[F] Slots D →ₗ[F] F where
  toFun x := (a x) • b + (b x) • a
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change a (x+y)*b z+b (x+y)*a z = (a x*b z+b x*a z)+(a y*b z+b y*a z)
    simp only [map_add]
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    change a (c • x)*b z+b (c • x)*a z = c*(a x*b z+b x*a z)
    simp only [map_smul,smul_eq_mul]
    ring

def polynomialPolar {D m : ℕ} (a b : Fin m → Lin D) : Slots D →ₗ[F] Slots D →ₗ[F] F :=
  ∑ j, productPolar (a j) (b j)

theorem polynomial_zero {D m : ℕ} (a b : Fin m → Lin D) (l : Lin D) :
    Polynomial a b l 0 = 0 := by
  simp [Polynomial]

theorem polynomial_law {D m : ℕ} (a b : Fin m → Lin D) (l : Lin D) (x y : Slots D) :
    Polynomial a b l (x+y) =
      Polynomial a b l x + Polynomial a b l y + polynomialPolar a b x y := by
  simp only [Polynomial, polynomialPolar, LinearMap.sum_apply, LinearMap.add_apply,
    map_add, productPolar, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    smul_eq_mul]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  have he : (∑ j, a j y * b j x) = ∑ j, b j x * a j y :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  ring

theorem polynomial_self {D m : ℕ} (a b : Fin m → Lin D) (x : Slots D) :
    polynomialPolar a b x x = 0 := by
  simp only [polynomialPolar, LinearMap.sum_apply, productPolar, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (b i x)]
  exact CharTwo.add_self_eq_zero _

/-- Named entry point using only the arithmetic identities still needed
from the lattice evaluation, with the quadratic law already constructed. -/
def certificate_of_polynomial {N D m : ℕ} (a b : Fin m → Lin D) (l first : Lin D)
    (eval : Fin N → Slots D) (beta : Slots D)
    (he : ∀ i, first (eval i) = 1) (hb : first beta = 0)
    (off : ∀ i j, i ≠ j → polynomialPolar a b (eval i) (eval j) = 1)
    (hbpol : ∀ i, polynomialPolar a b (eval i) beta = 1)
    (hq : ∀ i, Polynomial a b l (eval i) = 0)
    (hqb : Polynomial a b l beta = 0) : QuadraticCertificate N D where
  eval := eval
  Q := Polynomial a b l
  polar := polynomialPolar a b
  first := first
  beta := beta
  first_eval := he
  first_beta := hb
  self i := polynomial_self a b (eval i)
  distinct := off
  polar_beta := hbpol
  zero_Q := polynomial_zero a b l
  beta_Q := hqb
  law := polynomial_law a b l
  eval_Q := hq

#print axioms polynomial_law
#print axioms certificate_of_polynomial
end Erdos23
