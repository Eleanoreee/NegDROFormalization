import NegDROFormalization.QuadraticStructure
import NegDROFormalization.YoungVector

/-!
# Deterministic finite-dimensional fixed-witness inequality

This file combines Appendix equations (61)--(63) into the deterministic fixed-witness bound
underlying Lemma 3.2 and Lemma 4.1. The expression below is the algebraic directional form
obtained after substituting the population-risk expansion from Eq. (63). No differentiation,
probability, expectation, or stochastic-gradient API is claimed or used.
-/

set_option autoImplicit false

namespace NegDRO

/-- The finite-dimensional algebraic directional expression from Appendix Eq. (63):

`2 (∑ₑ (wₑ - a_gamma)) dot(v,d) + 2 quad(Q(w),d)`.

It represents `dᵀ ∇_b L(b,w)` only after the paper's population-risk expansion has been
performed; this definition does not formalize the derivative itself. -/
noncomputable def fixedWitnessDirectionalForm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ) (v d : Fin p → ℝ) : ℝ :=
  2 * (∑ e, (w e - negDROGammaCoefficient m gamma)) * vectorDot v d +
    2 * matrixQuad (negDROQ Sigma gamma w) d

/-- The exact identification-error expression used in Lemma 3.2 and Lemma 4.1. -/
noncomputable def fixedWitnessIdentificationError
    {p : ℕ} (m : ℕ) (gamma lam : ℝ) (v : Fin p → ℝ) : ℝ :=
  sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)

/-- The explicit fixed-witness direction inequality underlying Lemma 3.2 and Lemma 4.1:

`directionalForm ≥ lam * sqNorm d - sqNorm v / (lam * (1 + gamma m)²)`.

The coefficient is reduced using simplex membership. Curvature of `Q(w⁰)` is then derived by
`fixedWitness_curvature_transfer`, whose proof uses the actual matrix decomposition Eq. (61)
and quadratic nonnegativity of the scaled average covariance. Finally `vector_young_exact`
controls the cross term with its exact constant. -/
theorem fixedWitness_direction_explicit
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma lam : ℝ) (w₀ : Fin m → ℝ) (v d : Fin p → ℝ)
    (hm : 0 < m)
    (hgamma : 0 ≤ gamma)
    (hlam : 0 < lam)
    (hw₀ : IsSimplex w₀)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w₀) lam) :
    fixedWitnessDirectionalForm Sigma gamma w₀ v d ≥
      lam * sqNorm d -
        sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2) := by
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  have hcoeff := negDRO_coefficient_sum gamma hm hgamma hw₀
  -- This curvature transfer invokes `negDRO_q_decomposition`, the matrix equality Eq. (61).
  have hcurvatureQ :=
    fixedWitness_curvature_transfer Sigma gamma lam w₀ hm hgamma hSigma hcurvature
  have hquad := hcurvatureQ d
  have hyoung :=
    vector_young_exact v d lam (1 + gamma * (m : ℝ)) hlam hdenPos
  have hcross :
      2 * (1 / (1 + gamma * (m : ℝ))) * vectorDot v d =
        2 * vectorDot v d / (1 + gamma * (m : ℝ)) := by
    field_simp [ne_of_gt hdenPos]
  rw [fixedWitnessDirectionalForm, hcoeff]
  rw [hcross]
  nlinarith

/-- The fixed-witness direction theorem with the identification error named explicitly:
`directionalForm ≥ lam * sqNorm d - epsilon_id`. -/
theorem fixedWitness_direction_identificationError
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma lam : ℝ) (w₀ : Fin m → ℝ) (v d : Fin p → ℝ)
    (hm : 0 < m)
    (hgamma : 0 ≤ gamma)
    (hlam : 0 < lam)
    (hw₀ : IsSimplex w₀)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w₀) lam) :
    fixedWitnessDirectionalForm Sigma gamma w₀ v d ≥
      lam * sqNorm d - fixedWitnessIdentificationError m gamma lam v := by
  simpa only [fixedWitnessIdentificationError] using
    fixedWitness_direction_explicit Sigma gamma lam w₀ v d
      hm hgamma hlam hw₀ hSigma hcurvature

/-- The primal directional expression for the objective penalized by `-μ ‖w‖²`. Since that
penalty depends only on `w`, its primal directional expression is definitionally the same as
the unpenalized one. This is an algebraic representation, not a claim about Fréchet derivatives. -/
noncomputable def penalizedFixedWitnessDirectionalForm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ) (v d : Fin p → ℝ) (_μ : ℝ) : ℝ :=
  fixedWitnessDirectionalForm Sigma gamma w v d

/-- Adding the weight-only penalty `-μ ‖w‖²` leaves the primal directional expression
unchanged. The genuine derivative bridge for the actual penalized expanded objective is
`hasDerivAt_expandedPenalizedRadialObjective` in `PopulationExpansion.lean`. -/
theorem penalizedFixedWitnessDirectionalForm_eq
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ) (v d : Fin p → ℝ) (μ : ℝ) :
    penalizedFixedWitnessDirectionalForm Sigma gamma w v d μ =
      fixedWitnessDirectionalForm Sigma gamma w v d := by
  rfl

/-- Penalized fixed-witness direction bound. It has exactly the same identification loss as the
unpenalized bound and contains no `2μ` term; that term arises later from the comparator identity,
not from the primal directional expression at `w⁰`. -/
theorem penalized_fixedWitness_direction_identificationError
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma lam μ : ℝ) (w₀ : Fin m → ℝ) (v d : Fin p → ℝ)
    (hm : 0 < m)
    (hgamma : 0 ≤ gamma)
    (hlam : 0 < lam)
    (hw₀ : IsSimplex w₀)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w₀) lam) :
    penalizedFixedWitnessDirectionalForm Sigma gamma w₀ v d μ ≥
      lam * sqNorm d - fixedWitnessIdentificationError m gamma lam v := by
  rw [penalizedFixedWitnessDirectionalForm_eq]
  exact fixedWitness_direction_identificationError Sigma gamma lam w₀ v d
    hm hgamma hlam hw₀ hSigma hcurvature

end NegDRO
