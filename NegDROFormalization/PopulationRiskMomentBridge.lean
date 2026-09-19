import NegDROFormalization.FreshSamplingConditionalOracles

/-!
# Population squared risk from finite coordinate moments

This module starts from the integral of the actual squared loss and derives its finite quadratic
moment expansion.  It is independent of the additive structural model.  This is the expanded
environmental-risk identity from Appendix Lemma 1 used by the project; official v3 Eq. (13) is
instead the minimax identification formulation.  Any older Eq. (13) label refers only to
project-note numbering.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- Actual population squared-error risk for a fixed finite-coordinate predictor. -/
noncomputable def finitePopulationSquaredRisk
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Fin p → ℝ) : ℝ :=
  ∫ omega, (Y omega - vectorDot (X omega) b) ^ 2 ∂mu

/-- Coordinate second-moment matrix defined by actual integrals. -/
noncomputable def populationSecondMomentMatrix
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ ∫ omega, X omega i * X omega j ∂mu

/-- An actual coordinate second-moment matrix is symmetric, directly from commutativity of
real multiplication.  No structural-model or integrability assumption is needed for this
identity of the two (possibly nonintegrable) Lebesgue integrals. -/
theorem populationSecondMomentMatrix_isSymm
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ) :
    (populationSecondMomentMatrix mu X).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [populationSecondMomentMatrix]
  apply integral_congr_ae
  filter_upwards [] with omega
  ring

/-- Coordinate covariate-outcome cross moment defined by actual integrals. -/
noncomputable def populationCrossMoment
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) :
    Fin p → ℝ :=
  fun i ↦ ∫ omega, X omega i * Y omega ∂mu

/-- Outcome second moment defined by the actual integral. -/
noncomputable def populationOutcomeSecondMoment
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure Omega) (Y : Omega → ℝ) : ℝ :=
  ∫ omega, (Y omega) ^ 2 ∂mu

/-- Exactly the coordinate monomial integrability needed for the quadratic risk expansion. -/
structure HasIntegrablePopulationQuadraticMonomials
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) : Prop where
  ySq : Integrable (fun omega ↦ (Y omega) ^ 2) mu
  xy : ∀ i, Integrable (fun omega ↦ X omega i * Y omega) mu
  xx : ∀ i j, Integrable (fun omega ↦ X omega i * X omega j) mu

/-- The exact formal coordinate derivative of the finite moment polynomial before using
matrix symmetry.  This is an algebraic coefficient, not a claim about a derivative API. -/
noncomputable def finiteMomentRiskCoordinateDerivative
    {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin p → ℝ) : Fin p → ℝ :=
  fun i ↦ -2 * c i + Matrix.mulVec Sigma b i +
    Matrix.mulVec Sigma.transpose b i

/-- Under symmetry and the project-note cross-moment relation, the full coordinate derivative
coefficient is `2 v + 2 Sigma (b - betaStar)`. -/
theorem finiteMomentRiskCoordinateDerivative_eq_expanded
    {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (c v betaStar b : Fin p → ℝ)
    (hCross : ∀ i, c i = Matrix.mulVec Sigma betaStar i - v i)
    (hSymm : Sigma.IsSymm) :
    finiteMomentRiskCoordinateDerivative Sigma c b =
      fun i ↦ 2 * v i + 2 * Matrix.mulVec Sigma
        (primalDisplacement b betaStar) i := by
  funext i
  rw [finiteMomentRiskCoordinateDerivative, hCross i, hSymm.eq]
  simp only [Matrix.mulVec, dotProduct, primalDisplacement]
  rw [show (∑ j, Sigma i j * (b j - betaStar j)) =
      (∑ j, Sigma i j * b j) - ∑ j, Sigma i j * betaStar j by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  ring

/-- Pointwise finite-coordinate expansion of a squared residual. -/
theorem residual_sq_finite_monomial_expansion
    {Omega : Type*} {p : ℕ} (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Fin p → ℝ) (omega : Omega) :
    (Y omega - vectorDot (X omega) b) ^ 2 =
      (Y omega) ^ 2 - 2 * ∑ i, b i * (X omega i * Y omega) +
        ∑ ij : Fin p × Fin p,
          (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2) := by
  have hCross : 2 * ∑ i, b i * (X omega i * Y omega) =
      2 * Y omega * ∑ i, X omega i * b i := by
    calc
      2 * ∑ i, b i * (X omega i * Y omega) =
          ∑ i, 2 * (b i * (X omega i * Y omega)) := Finset.mul_sum _ _ _
      _ = ∑ i, (2 * Y omega) * (X omega i * b i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = 2 * Y omega * ∑ i, X omega i * b i := (Finset.mul_sum _ _ _).symm
  have hQuad : (∑ ij : Fin p × Fin p,
      (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2)) =
      (∑ i, X omega i * b i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro ij _hij
    ring
  rw [vectorDot, hCross, hQuad]
  ring

/-- The actual squared loss is integrable under the coordinate monomial assumptions. -/
theorem integrable_population_squared_loss
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) (b : Fin p → ℝ)
    (hMom : HasIntegrablePopulationQuadraticMonomials mu X Y) :
    Integrable (fun omega ↦ (Y omega - vectorDot (X omega) b) ^ 2) mu := by
  have hXY : Integrable (fun omega ↦ ∑ i, b i * (X omega i * Y omega)) mu :=
    integrable_finsetSum Finset.univ
      (fun i _hi ↦ (hMom.xy i).const_mul (b i))
  have hXX : Integrable (fun omega ↦ ∑ ij : Fin p × Fin p,
      (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2)) mu :=
    integrable_finsetSum Finset.univ
      (fun ij _hij ↦ (hMom.xx ij.1 ij.2).const_mul (b ij.1 * b ij.2))
  have hExpanded : Integrable (fun omega ↦
      (Y omega) ^ 2 - 2 * ∑ i, b i * (X omega i * Y omega) +
        ∑ ij : Fin p × Fin p,
          (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2)) mu :=
    (hMom.ySq.sub (hXY.const_mul 2)).add hXX
  exact hExpanded.congr (ae_of_all mu fun omega ↦
    (residual_sq_finite_monomial_expansion X Y b omega).symm)

/-- The integral of the actual squared loss equals the finite moment quadratic expression. -/
theorem finitePopulationSquaredRisk_eq_momentRisk
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) (b : Fin p → ℝ)
    (hMom : HasIntegrablePopulationQuadraticMonomials mu X Y) :
    finitePopulationSquaredRisk mu X Y b =
      finiteMomentEnvironmentalRisk
        (populationSecondMomentMatrix mu X)
        (populationCrossMoment mu X Y) b
        (populationOutcomeSecondMoment mu Y) := by
  have hXY : ∀ i, Integrable (fun omega ↦ b i * (X omega i * Y omega)) mu :=
    fun i ↦ (hMom.xy i).const_mul (b i)
  have hXX : ∀ ij : Fin p × Fin p, Integrable (fun omega ↦
      (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2)) mu :=
    fun ij ↦ (hMom.xx ij.1 ij.2).const_mul (b ij.1 * b ij.2)
  let xySum : Omega → ℝ := fun omega ↦ ∑ i, b i * (X omega i * Y omega)
  let xxSum : Omega → ℝ := fun omega ↦ ∑ ij : Fin p × Fin p,
    (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2)
  have hXYSum : Integrable xySum mu :=
    integrable_finsetSum Finset.univ (fun i _hi ↦ hXY i)
  have hXXSum : Integrable xxSum mu :=
    integrable_finsetSum Finset.univ (fun ij _hij ↦ hXX ij)
  rw [finitePopulationSquaredRisk]
  apply Eq.trans (integral_congr_ae (ae_of_all mu fun omega ↦
    residual_sq_finite_monomial_expansion X Y b omega))
  change (∫ omega, (Y omega) ^ 2 - 2 * xySum omega + xxSum omega ∂mu) = _
  rw [show (fun omega ↦ (Y omega) ^ 2 - 2 * xySum omega + xxSum omega) =
      ((fun omega ↦ (Y omega) ^ 2) - (fun omega ↦ 2 * xySum omega)) +
        xxSum by rfl]
  have hAddEq : integral mu
      (((fun omega ↦ (Y omega) ^ 2) - (fun omega ↦ 2 * xySum omega)) + xxSum) =
      integral mu ((fun omega ↦ (Y omega) ^ 2) - (fun omega ↦ 2 * xySum omega)) +
        integral mu xxSum := by
    change (∫ omega, ((Y omega) ^ 2 - 2 * xySum omega) + xxSum omega ∂mu) = _
    exact integral_add (hMom.ySq.sub (hXYSum.const_mul 2)) hXXSum
  rw [hAddEq]
  have hSubEq : integral mu
      ((fun omega ↦ (Y omega) ^ 2) - (fun omega ↦ 2 * xySum omega)) =
      (∫ omega, (Y omega) ^ 2 ∂mu) - (∫ omega, 2 * xySum omega ∂mu) := by
    change (∫ omega, (Y omega) ^ 2 - 2 * xySum omega ∂mu) = _
    exact integral_sub hMom.ySq (hXYSum.const_mul 2)
  rw [hSubEq]
  rw [integral_const_mul]
  change (∫ omega, (Y omega) ^ 2 ∂mu) -
      2 * (∫ omega, ∑ i, b i * (X omega i * Y omega) ∂mu) +
      (∫ omega, ∑ ij : Fin p × Fin p,
        (b ij.1 * b ij.2) * (X omega ij.1 * X omega ij.2) ∂mu) = _
  rw [integral_finset_sum Finset.univ (fun i _hi ↦ hXY i)]
  rw [integral_finset_sum Finset.univ (fun ij _hij ↦ hXX ij)]
  simp_rw [integral_const_mul]
  dsimp [finiteMomentEnvironmentalRisk, populationSecondMomentMatrix,
    populationCrossMoment, populationOutcomeSecondMoment, matrixQuad,
    vectorDot, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  ring_nf
  have hCrossSum : (∑ i, b i * ∫ omega, X omega i * Y omega ∂mu) =
      ∑ i, (∫ omega, X omega i * Y omega ∂mu) * b i := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hCrossSum]
  have hQuadSum :
      (∑ i, ∑ j, b i * b j * ∫ omega, X omega i * X omega j ∂mu) =
      ∑ i, b i * ∑ j, (∫ omega, X omega i * X omega j ∂mu) * b j := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hQuadSum]

/-- Moment-level expanded environmental-risk identity, now starting from the integral of the actual squared
loss. The two displayed moment relations are the exact remaining model-specific content. -/
theorem finitePopulationSquaredRisk_eq_expandedEnvironmentalRisk
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (sigmaYSq : ℝ) (v betaStar b : Fin p → ℝ)
    (hMom : HasIntegrablePopulationQuadraticMonomials mu X Y)
    (hCross : ∀ i,
      populationCrossMoment mu X Y i =
        Matrix.mulVec (populationSecondMomentMatrix mu X) betaStar i - v i)
    (hOutcome : populationOutcomeSecondMoment mu Y =
      sigmaYSq + matrixQuad (populationSecondMomentMatrix mu X) betaStar -
        2 * vectorDot v betaStar) :
    finitePopulationSquaredRisk mu X Y b =
      expandedEnvironmentalRisk sigmaYSq v b betaStar
        (populationSecondMomentMatrix mu X) := by
  rw [finitePopulationSquaredRisk_eq_momentRisk X Y b hMom]
  let Sigma : Fin 1 → Matrix (Fin p) (Fin p) ℝ :=
    fun _ ↦ populationSecondMomentMatrix mu X
  let c : Fin 1 → Fin p → ℝ := fun _ ↦ populationCrossMoment mu X Y
  let q : Fin 1 → ℝ := fun _ ↦ populationOutcomeSecondMoment mu Y
  have hCrossFamily : HasNegDROCrossMomentRelation Sigma c v betaStar := by
    intro _e i
    exact hCross i
  have hOutcomeFamily : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar := by
    intro _e
    exact hOutcome
  have hSymmFamily : ∀ e, (Sigma e).IsSymm :=
    fun _e ↦ populationSecondMomentMatrix_isSymm mu X
  exact finiteMomentEnvironmentalRisk_eq_expandedEnvironmentalRisk
    Sigma c q sigmaYSq v betaStar b hCrossFamily hOutcomeFamily hSymmFamily 0

end NegDRO
