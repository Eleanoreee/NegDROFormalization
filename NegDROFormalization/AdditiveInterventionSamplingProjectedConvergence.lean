import NegDROFormalization.AdditiveInterventionSamplingConvergence
import NegDROFormalization.EuclideanProjectionBridge

/-!
# Additive-intervention convergence with the actual Euclidean projection

This module only discharges the three former abstract projection interfaces.  For a nonempty
closed convex coordinate set `C`, every occurrence of the primal update uses
`coordinateEuclideanProjection C hCNonempty hCClosed hCConvex`.  Numerical moment, spectral,
and rate assumptions are unchanged; concrete oracle integrability is derived from the retained
fresh-law, fourth-moment, measurability, and bounded-trajectory assumptions.

The algorithm remains the project's simultaneous fresh-sample projected primal descent plus EG
ascent.  It is not official v3 Algorithm 1, which exactly maximizes empirical risk in `w` before
its primal gradient step.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- The additive fresh-sampling assumptions with the abstract projection fields replaced by
the primitive geometric hypotheses needed to construct nearest-point projection. -/
structure AdditiveInterventionFreshSamplingProjectedAssumptions
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    (mu : Measure Omega) (nu : Measure Noise) {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
  hCNonempty : C.Nonempty
  hCClosed : IsClosed C
  hCConvex : Convex ℝ C
  hInt : ∀ e, HasIntegrableAdditiveInterventionMoments nu etaY etaX (delta e)
  hZero : ∀ e, HasZeroSystematicInterventionCrossMoments nu etaY etaX (delta e)
  hEnvXMeas : ∀ e i, AEStronglyMeasurable
    (fun xi ↦ additiveInterventionEnvironmentX GT BYX etaY etaX delta e xi i) nu
  hEnvYMeas : ∀ e, AEStronglyMeasurable
    (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta e) nu
  hEnvX4Int : ∀ e, Integrable (fun xi ↦
    (sqNorm (additiveInterventionEnvironmentX GT BYX etaY etaX delta e xi)) ^ 2) nu
  hEnvY4Int : ∀ e, Integrable (fun xi ↦
    (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta e xi) ^ 4) nu
  hEnvX4 : ∀ e, (∫ xi,
    (sqNorm (additiveInterventionEnvironmentX GT BYX etaY etaX delta e xi)) ^ 2 ∂nu) ≤ KX
  hEnvY4 : ∀ e, (∫ xi,
    (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta e xi) ^ 4 ∂nu) ≤ KY
  hMono : ∀ t, mCond t ≤ mCond (t + 1)
  hmCond : ∀ t, mCond t ≤ mOmega
  hLaw : ∀ t < T, HasFreshUniformFiniteEnvironmentLaw (mCond := mCond t) mu
    (eHat t) (xHat t) (yHat t) (fun _ ↦ nu)
    (additiveInterventionEnvironmentX GT BYX etaY etaX delta)
    (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta)
  hPrimalMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
    concreteTrajectoryPrimalOracle
      (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex)
      bInit gamma penalty etaB etaW eHat xHat yHat t omega)
  hDualMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
    concreteTrajectoryDualOracle
      (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex)
      bInit gamma penalty etaB etaW eHat xHat yHat t omega)
  hm : 0 < m
  hT : 0 < T
  hetaB : 0 < etaB
  hetaW : 0 < etaW
  hB : 0 ≤ B
  hKX : 0 ≤ KX
  hKY : 0 ≤ KY
  hgamma : 0 ≤ gamma
  hlam : 0 < lam
  hInit : bInit ∈ C
  hbetaStar : betaStar ∈ C
  hCBall : SetContainedInCoordinateSqBall C B
  hw0 : IsSimplex w0
  hEigen : ∀ i, lam ≤
    (Matrix.isHermitian_iff_isSymm.mpr
      (negDROHeterogeneityMatrix_isSymm
        (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta) w0
        (additiveInterventionFamily_sigmaIsSymm nu GT BYX etaY etaX delta))).eigenvalues i

/-- Supply the old bundle using the projection properties proved from closed convex geometry. -/
theorem AdditiveInterventionFreshSamplingProjectedAssumptions.toBase
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat) :
    AdditiveInterventionFreshSamplingAssumptions mu nu mCond C
      (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
      bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T
      eHat xHat yHat where
  hInt := h.hInt
  hZero := h.hZero
  hEnvXMeas := h.hEnvXMeas
  hEnvYMeas := h.hEnvYMeas
  hEnvX4Int := h.hEnvX4Int
  hEnvY4Int := h.hEnvY4Int
  hEnvX4 := h.hEnvX4
  hEnvY4 := h.hEnvY4
  hMono := h.hMono
  hmCond := h.hmCond
  hLaw := h.hLaw
  hPMeas := coordinateEuclideanProjection_measurable C h.hCNonempty h.hCClosed h.hCConvex
  hPrimalMeas := h.hPrimalMeas
  hDualMeas := h.hDualMeas
  hm := h.hm
  hT := h.hT
  hetaB := h.hetaB
  hetaW := h.hetaW
  hB := h.hB
  hKX := h.hKX
  hKY := h.hKY
  hgamma := h.hgamma
  hlam := h.hlam
  hInit := h.hInit
  hbetaStar := h.hbetaStar
  hPFeas := coordinateEuclideanProjection_mapsIntoFeasibleSet
    C h.hCNonempty h.hCClosed h.hCConvex
  hPDist := coordinateEuclideanProjection_hasProjectionDistanceBound
    C h.hCNonempty h.hCClosed h.hCConvex
  hCBall := h.hCBall
  hw0 := h.hw0
  hEigen := h.hEigen

/-- Unpenalized finite-time bound with actual nearest-point projection. -/
theorem stochasticNegDRO_additiveSampling_projected_unpenalized_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu)
          (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
          bInit etaB
          (concreteTrajectoryPrimalOracle
            (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
            bInit gamma 0 etaB etaW eHat xHat yHat) betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_additiveSampling_unpenalized_convergence mCond C
    (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
    bInit betaStar GT BYX etaY etaX delta gamma lam w0 etaB etaW B KX KY T
    eHat xHat yHat
    (h.toBase mCond C bInit betaStar GT BYX etaY etaX delta gamma lam 0 w0
      etaB etaW B KX KY T eHat xHat yHat)

/-- Unpenalized averaged-iterate bound with actual nearest-point projection. -/
theorem stochasticNegDRO_additiveSampling_projected_unpenalized_averaged_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory
        (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
        bInit etaB
        (concreteTrajectoryPrimalOracle
          (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
          bInit gamma 0 etaB etaW eHat xHat yHat) t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_additiveSampling_unpenalized_averaged_convergence mCond C
    (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
    bInit betaStar GT BYX etaY etaX delta gamma lam w0 etaB etaW B KX KY T
    eHat xHat yHat
    (h.toBase mCond C bInit betaStar GT BYX etaY etaX delta gamma lam 0 w0
      etaB etaW B KX KY T eHat xHat yHat)

/-- Unpenalized inverse-square-root rate with actual nearest-point projection. -/
theorem stochasticNegDRO_additiveSampling_projected_unpenalized_invSqrt_rate
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu)
          (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
          bInit (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle
            (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
            bInit gamma 0 (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
            eHat xHat yHat) betaStar t ≤
      explicitIdentificationBias m gamma lam (semV nu GT BYX etaY etaX) +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  exact stochasticNegDRO_additiveSampling_unpenalized_invSqrt_rate mCond C
    (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
    bInit betaStar GT BYX etaY etaX delta gamma lam w0 B KX KY T eHat xHat yHat
    (h.toBase mCond C bInit betaStar GT BYX etaY etaX delta gamma lam 0 w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)

/-- Penalized finite-time bound with actual nearest-point projection. -/
theorem stochasticNegDRO_additiveSampling_projected_penalized_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu)
          (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
          bInit etaB
          (concreteTrajectoryPrimalOracle
            (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
            bInit gamma penalty etaB etaW eHat xHat yHat) betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_additiveSampling_penalized_convergence mCond C
    (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
    bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T
    eHat xHat yHat
    (h.toBase mCond C bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0
      etaB etaW B KX KY T eHat xHat yHat) hpenalty

/-- Penalized averaged-iterate bound with actual nearest-point projection. -/
theorem stochasticNegDRO_additiveSampling_projected_penalized_averaged_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory
        (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
        bInit etaB
        (concreteTrajectoryPrimalOracle
          (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
          bInit gamma penalty etaB etaW eHat xHat yHat) t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_additiveSampling_penalized_averaged_convergence mCond C
    (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
    bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T
    eHat xHat yHat
    (h.toBase mCond C bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0
      etaB etaW B KX KY T eHat xHat yHat) hpenalty

/-- Penalized inverse-square-root rate with actual nearest-point projection. -/
theorem stochasticNegDRO_additiveSampling_projected_penalized_invSqrt_rate
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (bInit betaStar : Fin p → ℝ)
    (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingProjectedAssumptions mu nu mCond C bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu)
          (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
          bInit (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle
            (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
            bInit gamma penalty (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
            eHat xHat yHat) betaStar t ≤
      explicitIdentificationBias m gamma lam (semV nu GT BYX etaY etaX) +
        2 * penalty / lam +
        explicitPenalizedRateConstant m penalty bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  exact stochasticNegDRO_additiveSampling_penalized_invSqrt_rate mCond C
    (coordinateEuclideanProjection C h.hCNonempty h.hCClosed h.hCConvex)
    bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0 B KX KY T eHat xHat yHat
    (h.toBase mCond C bInit betaStar GT BYX etaY etaX delta gamma lam penalty w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)
    hpenalty

end NegDRO
