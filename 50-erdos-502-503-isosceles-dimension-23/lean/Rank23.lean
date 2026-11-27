import BinarySaturation
import ModFour

/-!
# Dimension-23 certificate interface
These theorems check the numerical rank step and the quadratic contradiction.
The input witnesses are the lattice feature vectors, NOT mere pair distances.
-/
namespace Erdos23

abbrev Slots (D : ℕ) := Fin D → F

/-- The data the integer-lattice expansion must supply. -/
structure QuadraticCertificate (N D : ℕ) where
  eval : Fin N → Slots D
  Q : Slots D → F
  polar : Slots D →ₗ[F] Slots D →ₗ[F] F
  first : Slots D →ₗ[F] F
  beta : Slots D
  first_eval : ∀ x, first (eval x) = 1
  first_beta : first beta = 0
  self : ∀ i, polar (eval i) (eval i) = 0
  distinct : ∀ i j, i ≠ j → polar (eval i) (eval j) = 1
  polar_beta : ∀ i, polar (eval i) beta = 1
  zero_Q : Q 0 = 0
  beta_Q : Q beta = 0
  law : ∀ x y, Q (x+y) = Q x + Q y + polar x y
  eval_Q : ∀ i, Q (eval i) = 0

def QuadraticCertificate.restrict {N D m : ℕ} (c : QuadraticCertificate N D)
    (hm : m ≤ N) : QuadraticCertificate m D where
  eval i := c.eval (Fin.castLE hm i)
  Q := c.Q
  polar := c.polar
  first := c.first
  beta := c.beta
  first_eval _ := c.first_eval _
  first_beta := c.first_beta
  self _ := c.self _
  distinct _ _ ne := c.distinct _ _ (fun eq => ne (Fin.castLE_injective hm eq))
  polar_beta _ := c.polar_beta _
  zero_Q := c.zero_Q
  beta_Q := c.beta_Q
  law := c.law
  eval_Q _ := c.eval_Q _

theorem certificate_rank_bound {N D : ℕ} (c : QuadraticCertificate N D) : N ≤ D := by
  have h := binary_rank_bound c.eval c.polar c.first c.first_eval c.self c.distinct
  simpa [Slots,Module.finrank_pi] using h

theorem excludes_278 {D : ℕ} (c : QuadraticCertificate 278 D) (dim : D ≤ 278) : False := by
  have pairs : ((278 : ℕ).choose 2 : F) = 1 := by
    rw [Nat.choose_two_right]
    decide
  apply no_saturation c.eval c.Q c.polar c.first c.beta
    c.first_eval c.first_beta c.self c.distinct c.polar_beta c.zero_Q
    c.beta_Q c.law c.eval_Q pairs
  simpa [Slots,Module.finrank_pi] using dim

/-- Stronger than the raw feature-count bound: at most 277 given the
    dimension-23 quadratic certificate and even binary rank at most 22. -/
theorem dimension23_at_most_277 {N h r : ℕ}
    (c : QuadraticCertificate N (2+h+r+r.choose 2)) (hh : h ≤ 23) (hr : r ≤ 22) :
    N ≤ 277 := by
  by_contra! hn
  exact excludes_278 (c.restrict hn) (dimension23_count_certificate h r hh hr)

#print axioms ModFour.bit_halfnorm_sub
#print axioms no_saturation
#print axioms excludes_278
#print axioms dimension23_at_most_277
end Erdos23
