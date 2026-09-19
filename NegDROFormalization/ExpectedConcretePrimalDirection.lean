import NegDROFormalization.ExpandedPrimalCoefficient
import NegDROFormalization.ExpectedDualRegret
import NegDROFormalization.ExpectedPrimalRecursion

/-!
# Expected concrete primal-direction lower bounds

This module integrates the deterministic current-weight coefficient bounds. All objective
regrets remain signed comparator-minus-current differences; no regret nonnegativity is used.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- The concrete population primal coefficient evaluated at random primal and dual points. -/
noncomputable def randomExpandedPrimalCoefficient
    {Omega : Type*} {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ) (gamma : ℝ)
    (v betaStar : Fin p → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin nEnv → ℝ) : Omega → Fin p → ℝ :=
  fun omega => expandedPrimalCoefficient Sigma gamma v (b omega) betaStar (w omega)

/-- The penalized concrete population primal coefficient at random points. -/
noncomputable def randomExpandedPenalizedPrimalCoefficient
    {Omega : Type*} {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ) (gamma : ℝ)
    (v betaStar : Fin p → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin nEnv → ℝ) (penalty : ℝ) : Omega → Fin p → ℝ :=
  fun omega =>
    expandedPenalizedPrimalCoefficient Sigma gamma v (b omega) betaStar (w omega) penalty

/-- Expected concrete primal radial pairing. -/
noncomputable def expectedRandomExpandedPrimalDirection
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ) (gamma : ℝ)
    (v betaStar : Fin p → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin nEnv → ℝ) : ℝ :=
  expectedDirection
    (randomExpandedPrimalCoefficient Sigma gamma v betaStar b w)
    (fun omega => primalDisplacement (b omega) betaStar) mu

/-- Expected penalized concrete primal radial pairing. -/
noncomputable def expectedRandomExpandedPenalizedPrimalDirection
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ) (gamma : ℝ)
    (v betaStar : Fin p → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin nEnv → ℝ) (penalty : ℝ) : ℝ :=
  expectedDirection
    (randomExpandedPenalizedPrimalCoefficient
      Sigma gamma v betaStar b w penalty)
    (fun omega => primalDisplacement (b omega) betaStar) mu

/-- A population finite-vector pairing is integrable when its coordinates are a.e. equal to
conditional expectations of integrable oracle coordinates and its predictable multiplier is
coordinatewise bounded. -/
theorem integrable_population_vectorDot_of_condExp_ae_eq
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {q : ℕ} (hmCond : mCond ≤ mOmega)
    (gHat F d : Omega → Fin q → ℝ)
    (_hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hdMeas : ∀ i,
      AEStronglyMeasurable[mCond] (fun omega => d omega i) mu)
    (bound : ℝ) (hdBound : ∀ i, ∀ᵐ omega ∂mu, ‖d omega i‖ ≤ bound)
    (hCondUnbiased : ∀ i,
      (fun omega => F omega i) =ᵐ[mu]
        mu[(fun omega => gHat omega i) | mCond]) :
    Integrable (fun omega => vectorDot (F omega) (d omega)) mu := by
  have hFInt : ∀ i, Integrable (fun omega => F omega i) mu := by
    intro i
    exact integrable_condExp.congr (hCondUnbiased i).symm
  simp only [vectorDot]
  apply integrable_finsetSum Finset.univ
  intro i _hi
  exact (hFInt i).mul_bdd ((hdMeas i).mono hmCond) (hdBound i)

/-- Integrability of actual unpenalized objective regret derived from the exact deterministic
linearization and a conditionally unbiased integrable dual oracle. -/
theorem integrable_randomExpandedUnpenalizedRegret_of_condExp_ae_eq
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {nEnv p : ℕ} (hmCond : mCond ≤ mOmega)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w gHat : Omega → Fin nEnv → ℝ)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => primalDisplacement u (w omega) i) mu)
    (bound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement u (w omega) i‖ ≤ bound)
    (hCondUnbiased : ∀ i,
      (fun omega =>
        expandedDualGradient Sigma sigmaYSq v (b omega) betaStar i) =ᵐ[mu]
      mu[(fun omega => gHat omega i) | mCond]) :
    Integrable
      (randomExpandedUnpenalizedRegret
        Sigma gamma sigmaYSq v betaStar u b w) mu := by
  let F : Omega → Fin nEnv → ℝ :=
    fun omega => expandedDualGradient Sigma sigmaYSq v (b omega) betaStar
  let d : Omega → Fin nEnv → ℝ :=
    fun omega => primalDisplacement u (w omega)
  have hPairInt : Integrable (fun omega => vectorDot (F omega) (d omega)) mu :=
    integrable_population_vectorDot_of_condExp_ae_eq
      hmCond gHat F d hgHatInt hDisplacementMeas bound
      hDisplacementBound (by simpa [F] using hCondUnbiased)
  apply hPairInt.congr
  exact Eventually.of_forall (fun omega => by
    symm
    exact expandedUnpenalizedRegret_eq_linearization
      Sigma gamma sigmaYSq v (b omega) betaStar u (w omega))

/-- Integrability of actual penalized objective regret. Besides the population pairing, the
exact deterministic remainder uses the integrable finite squared displacement. -/
theorem integrable_randomExpandedPenalizedRegret_of_condExp_ae_eq
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] {nEnv p : ℕ} (hmCond : mCond ≤ mOmega)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq penalty : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w gHat : Omega → Fin nEnv → ℝ)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => primalDisplacement u (w omega) i) mu)
    (bound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement u (w omega) i‖ ≤ bound)
    (hCondUnbiased : ∀ i,
      (fun omega =>
        expandedPenalizedDualGradient Sigma sigmaYSq v (b omega) betaStar
          (w omega) penalty i) =ᵐ[mu]
      mu[(fun omega => gHat omega i) | mCond]) :
    Integrable
      (randomExpandedPenalizedRegret
        Sigma gamma sigmaYSq v betaStar u b w penalty) mu := by
  let F : Omega → Fin nEnv → ℝ := fun omega =>
    expandedPenalizedDualGradient Sigma sigmaYSq v (b omega) betaStar
      (w omega) penalty
  let d : Omega → Fin nEnv → ℝ :=
    fun omega => primalDisplacement u (w omega)
  have hPairInt : Integrable (fun omega => vectorDot (F omega) (d omega)) mu :=
    integrable_population_vectorDot_of_condExp_ae_eq
      hmCond gHat F d hgHatInt hDisplacementMeas bound
      hDisplacementBound (by simpa [F] using hCondUnbiased)
  have hdAmbient : ∀ i,
      AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
    fun i => (hDisplacementMeas i).mono hmCond
  have hSqInt : Integrable (fun omega => sqNorm (d omega)) mu :=
    integrable_sqNorm_of_coordinatewise_aestronglyMeasurable_of_bound
      d hdAmbient bound hDisplacementBound
  have hRemainderInt : Integrable (fun omega => penalty * sqNorm (d omega)) mu :=
    hSqInt.const_mul penalty
  apply (hPairInt.sub hRemainderInt).congr
  exact Eventually.of_forall (fun omega => by
    symm
    exact expandedPenalizedObjective_sub_eq_linearization_sub_remainder
      Sigma gamma sigmaYSq v (b omega) betaStar u (w omega) penalty)

/-- Expected unpenalized concrete direction bound. The three displayed integrability premises
ensure that every integral is a genuine expectation; later trajectory/oracle assumptions derive
them via the helpers above and the bounded primal domain. -/
theorem expected_expandedPrimalCoefficient_unpenalized_lower_bound
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v betaStar : Fin p → ℝ)
    (w0 : Fin nEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin nEnv → ℝ)
    (hnEnv : 0 < nEnv) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hw0 : IsSimplex w0) (hw : ∀ omega, IsSimplex (w omega))
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam)
    (hDirectionInt : Integrable (fun omega =>
      vectorDot
        (randomExpandedPrimalCoefficient Sigma gamma v betaStar b w omega)
        (primalDisplacement (b omega) betaStar)) mu)
    (hDistInt : Integrable (fun omega => sqDist (b omega) betaStar) mu)
    (hRegretInt : Integrable
      (randomExpandedUnpenalizedRegret
        Sigma gamma sigmaYSq v betaStar w0 b w) mu) :
    expectedRandomExpandedPrimalDirection
        (mu := mu) Sigma gamma v betaStar b w ≥
      lam * (∫ omega, sqDist (b omega) betaStar ∂mu) -
        sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2) -
        2 * (∫ omega,
          randomExpandedUnpenalizedRegret
            Sigma gamma sigmaYSq v betaStar w0 b w omega ∂mu) := by
  let epsilonId := sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)
  let regret := randomExpandedUnpenalizedRegret
    Sigma gamma sigmaYSq v betaStar w0 b w
  have hRightInt : Integrable (fun omega =>
      lam * sqDist (b omega) betaStar - epsilonId - 2 * regret omega) mu :=
    ((hDistInt.const_mul lam).sub (integrable_const epsilonId)).sub
      (hRegretInt.const_mul 2)
  have hPointwise : ∀ᵐ omega ∂mu,
      lam * sqDist (b omega) betaStar - epsilonId - 2 * regret omega ≤
        vectorDot
          (randomExpandedPrimalCoefficient Sigma gamma v betaStar b w omega)
          (primalDisplacement (b omega) betaStar) :=
    Eventually.of_forall (fun omega => by
      have hDet := expandedPrimalCoefficient_unpenalized_lower_bound
        Sigma gamma sigmaYSq lam v (b omega) betaStar w0 (w omega)
        hnEnv hgamma hlam hw0 (hw omega) hSigma hcurvature
      rw [show sqNorm (primalDisplacement (b omega) betaStar) =
        sqDist (b omega) betaStar by rfl] at hDet
      simpa [randomExpandedPrimalCoefficient, randomExpandedUnpenalizedRegret,
        epsilonId, regret] using hDet)
  have hIntegrated := integral_mono_ae hRightInt hDirectionInt hPointwise
  have hRightIntegral :
      (∫ omega,
        (lam * sqDist (b omega) betaStar - epsilonId - 2 * regret omega) ∂mu) =
      lam * (∫ omega, sqDist (b omega) betaStar ∂mu) - epsilonId -
        2 * (∫ omega, regret omega ∂mu) := by
    calc
      _ = (∫ omega, lam * sqDist (b omega) betaStar - epsilonId ∂mu) -
          ∫ omega, 2 * regret omega ∂mu :=
        integral_sub
          ((hDistInt.const_mul lam).sub (integrable_const epsilonId))
          (hRegretInt.const_mul 2)
      _ = ((∫ omega, lam * sqDist (b omega) betaStar ∂mu) -
          ∫ _omega : Omega, epsilonId ∂mu) -
          ∫ omega, 2 * regret omega ∂mu := by
        rw [integral_sub (hDistInt.const_mul lam) (integrable_const epsilonId)]
      _ = lam * (∫ omega, sqDist (b omega) betaStar ∂mu) - epsilonId -
          2 * (∫ omega, regret omega ∂mu) := by
        rw [integral_const_mul, integral_const_mul]
        simp
  rw [hRightIntegral] at hIntegrated
  simpa [expectedRandomExpandedPrimalDirection, expectedDirection,
    epsilonId, regret] using hIntegrated

/-- Expected penalized concrete direction bound. The structural loss is exactly `-2 * penalty`,
not a cumulative `-2 * penalty * T`. -/
theorem expected_expandedPrimalCoefficient_penalized_lower_bound
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v betaStar : Fin p → ℝ)
    (w0 : Fin nEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin nEnv → ℝ)
    (hnEnv : 0 < nEnv) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hpenalty : 0 ≤ penalty)
    (hw0 : IsSimplex w0) (hw : ∀ omega, IsSimplex (w omega))
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam)
    (hDirectionInt : Integrable (fun omega =>
      vectorDot
        (randomExpandedPenalizedPrimalCoefficient
          Sigma gamma v betaStar b w penalty omega)
        (primalDisplacement (b omega) betaStar)) mu)
    (hDistInt : Integrable (fun omega => sqDist (b omega) betaStar) mu)
    (hRegretInt : Integrable
      (randomExpandedPenalizedRegret
        Sigma gamma sigmaYSq v betaStar w0 b w penalty) mu) :
    expectedRandomExpandedPenalizedPrimalDirection
        (mu := mu) Sigma gamma v betaStar b w penalty ≥
      lam * (∫ omega, sqDist (b omega) betaStar ∂mu) -
        sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2) -
        2 * (∫ omega,
          randomExpandedPenalizedRegret
            Sigma gamma sigmaYSq v betaStar w0 b w penalty omega ∂mu) -
        2 * penalty := by
  let epsilonId := sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)
  let regret := randomExpandedPenalizedRegret
    Sigma gamma sigmaYSq v betaStar w0 b w penalty
  have hRegretLocal : Integrable regret mu := by
    simpa [regret] using hRegretInt
  have hRightInt : Integrable (fun omega =>
      lam * sqDist (b omega) betaStar - epsilonId -
        2 * regret omega - 2 * penalty) mu :=
    (((hDistInt.const_mul lam).sub (integrable_const epsilonId)).sub
      (hRegretLocal.const_mul 2)).sub (integrable_const (2 * penalty))
  have hPointwise : ∀ᵐ omega ∂mu,
      lam * sqDist (b omega) betaStar - epsilonId -
          2 * regret omega - 2 * penalty ≤
        vectorDot
          (randomExpandedPenalizedPrimalCoefficient
            Sigma gamma v betaStar b w penalty omega)
          (primalDisplacement (b omega) betaStar) :=
    Eventually.of_forall (fun omega => by
      have hDet := expandedPrimalCoefficient_penalized_lower_bound
        Sigma gamma sigmaYSq lam penalty v (b omega) betaStar w0 (w omega)
        hnEnv hgamma hlam hpenalty hw0 (hw omega) hSigma hcurvature
      rw [show sqNorm (primalDisplacement (b omega) betaStar) =
        sqDist (b omega) betaStar by rfl] at hDet
      simpa [randomExpandedPenalizedPrimalCoefficient, randomExpandedPenalizedRegret,
        epsilonId, regret] using hDet)
  have hIntegrated := integral_mono_ae hRightInt hDirectionInt hPointwise
  have hRightIntegral :
      (∫ omega,
        (lam * sqDist (b omega) betaStar - epsilonId -
          2 * regret omega - 2 * penalty) ∂mu) =
      lam * (∫ omega, sqDist (b omega) betaStar ∂mu) - epsilonId -
        2 * (∫ omega, regret omega ∂mu) - 2 * penalty := by
    calc
      _ = (∫ omega,
          lam * sqDist (b omega) betaStar - epsilonId - 2 * regret omega ∂mu) -
          ∫ _omega : Omega, 2 * penalty ∂mu :=
        integral_sub
          (((hDistInt.const_mul lam).sub (integrable_const epsilonId)).sub
            (hRegretLocal.const_mul 2))
          (integrable_const (2 * penalty))
      _ = ((∫ omega, lam * sqDist (b omega) betaStar - epsilonId ∂mu) -
          ∫ omega, 2 * regret omega ∂mu) -
          ∫ _omega : Omega, 2 * penalty ∂mu := by
        congr 1
        exact integral_sub
          ((hDistInt.const_mul lam).sub (integrable_const epsilonId))
          (hRegretLocal.const_mul 2)
      _ = (((∫ omega, lam * sqDist (b omega) betaStar ∂mu) -
          ∫ _omega : Omega, epsilonId ∂mu) -
          ∫ omega, 2 * regret omega ∂mu) -
          ∫ _omega : Omega, 2 * penalty ∂mu := by
        rw [integral_sub (hDistInt.const_mul lam) (integrable_const epsilonId)]
      _ = lam * (∫ omega, sqDist (b omega) betaStar ∂mu) - epsilonId -
          2 * (∫ omega, regret omega ∂mu) - 2 * penalty := by
        rw [integral_const_mul, integral_const_mul]
        simp
  rw [hRightIntegral] at hIntegrated
  simpa [expectedRandomExpandedPenalizedPrimalDirection, expectedDirection,
    epsilonId, regret] using hIntegrated

end NegDRO
