import NegDROFormalization.AdditiveInterventionSamplingBridge
import NegDROFormalization.OracleIntegrabilityBridge
import NegDROFormalization.SpectralWitnessInterface

/-!
# Corrected realized additive reduced-form plus fresh-sampling convergence assembly

This module contains no new stochastic argument.  It constructs the existing fresh-sampling
assumption bundles from (A) an additive SEM, (B) a universal fresh conditional law, and
(C) optimization/projection plus a genuine spectral lower bound, then invokes the established
finite-time, averaged, and rate theorems.

The entry point receives `GT` and the realized additive maps directly.  It does not reconstruct
them from `BXX`, acyclicity, or the original block structural equation.  The algorithm proved
here is simultaneous fresh-sample projected primal descent plus EG ascent.  Official v3
Algorithm 1 instead exactly maximizes the empirical risk over `w` and then takes a primal
gradient step; no theorem in this module claims to verify that literal algorithm.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- Top-level assumptions before any selected moments, oracle conditional means, matrix PSD,
symmetry, or quadratic curvature have been derived.

Fields `hInt`--`hEnvY4` are model/environment assumptions (A); `hMono`, `hmCond`, `hLaw`, and
the oracle measurability fields are sampling assumptions (B); the remaining fields are
optimization assumptions (C), including the actual projection interfaces and eigenvalue lower
bound.  Concrete oracle integrability is derived from these fields.
-/
structure AdditiveInterventionFreshSamplingAssumptions
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    (mu : Measure Omega) (nu : Measure Noise) {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
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
  hPMeas : Measurable P
  hPrimalMeas : ∀ t, Measurable[mCond (t + 1)]
    (fun omega ↦ concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega)
  hDualMeas : ∀ t, Measurable[mCond (t + 1)]
    (fun omega ↦ concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega)
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
  hPFeas : MapsIntoFeasibleSet C P
  hPDist : HasProjectionDistanceBound C P
  hCBall : SetContainedInCoordinateSqBall C B
  hw0 : IsSimplex w0
  hEigen : ∀ i, lam ≤
    (Matrix.isHermitian_iff_isSymm.mpr
      (negDROHeterogeneityMatrix_isSymm
        (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta) w0
        (additiveInterventionFamily_sigmaIsSymm nu GT BYX etaY etaX delta))).eigenvalues i

/-- Derive the common old convergence bundle.  In particular `hFresh`, PSD, and curvature are
constructed rather than accepted as fields. -/
theorem AdditiveInterventionFreshSamplingAssumptions.toFreshCommon
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    FreshConcreteCommonAssumptions mu mCond C P bInit betaStar
      (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
      gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat := by
  have hFresh : ∀ t < T, HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
      (eHat t) (xHat t) (yHat t) KX KY := by
    intro t ht
    exact freshLaw_toFreshRawMoments KX KY h.hKX h.hKY (h.hLaw t ht)
      (fun e i ↦ h.hEnvXMeas e i) h.hEnvYMeas h.hEnvX4Int h.hEnvY4Int
      h.hEnvX4 h.hEnvY4
  refine
    { hMono := h.hMono
      hmCond := h.hmCond
      hPMeas := h.hPMeas
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
      hPFeas := h.hPFeas
      hPDist := h.hPDist
      hCBall := h.hCBall
      hw0 := h.hw0
      hSigma := additiveInterventionFamily_sigmaQuadNonneg GT BYX etaY etaX delta h.hInt
      hcurvature := ?_
      hPrimalHatInt := fun t ht i ↦
        integrable_concreteTrajectoryPrimalOracle_coordinate_of_fresh
          mCond C P bInit gamma penalty etaB etaW B KX KY eHat xHat yHat
          h.hMono h.hmCond h.hPMeas h.hPrimalMeas h.hDualMeas h.hm h.hB
          h.hInit h.hPFeas h.hCBall t (hFresh t ht) i
      hPrimalSqInt := fun t ht ↦
        integrable_concreteTrajectoryPrimalOracle_sqNorm_of_fresh
          mCond C P bInit gamma penalty etaB etaW B KX KY eHat xHat yHat
          h.hMono h.hmCond h.hPMeas h.hPrimalMeas h.hDualMeas h.hm h.hB
          h.hInit h.hPFeas h.hCBall t (hFresh t ht)
      hDualHatInt := fun t ht i ↦
        integrable_concreteTrajectoryDualOracle_coordinate_of_fresh
          mCond C P bInit gamma penalty etaB etaW B KX KY eHat xHat yHat
          h.hMono h.hmCond h.hPMeas h.hPrimalMeas h.hDualMeas h.hm h.hB hpenalty
          h.hInit h.hPFeas h.hCBall t (hFresh t ht) i
      hDualSizeSqInt := fun t ht ↦
        integrable_concreteTrajectoryDualSize_sq_of_fresh
          mCond C P bInit gamma penalty etaB etaW B KX KY eHat xHat yHat
          h.hMono h.hmCond h.hPMeas h.hPrimalMeas h.hDualMeas h.hm h.hB
          h.hInit h.hPFeas h.hCBall t (hFresh t ht)
      hFresh := hFresh }
  · exact (additiveInterventionFamily_spectralWitnessAtLeast nu GT BYX etaY etaX delta
      w0 lam h.hEigen).curvatureAtLeast

/-- Construct the complete old unpenalized sampling bundle; all population relations and
conditional moment structures are derived. -/
theorem AdditiveInterventionFreshSamplingAssumptions.toFreshSamplingUnpenalized
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat) :
    FreshSamplingConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar
      (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
      (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
      (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
      gamma (∫ xi, etaY xi * etaY xi ∂nu) lam (semV nu GT BYX etaY etaX) w0
      etaB etaW B KX KY T eHat xHat yHat := by
  exact
    { common := h.toFreshCommon mCond C P bInit betaStar GT BYX etaY etaX delta
        gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat (by norm_num)
      population := fun t ht ↦
        additiveInterventionFreshLaw_toFreshPopulationMoments GT BYX betaStar etaY etaX
          delta (h.hLaw t ht) h.hInt
      crossRelation := additiveInterventionFamily_hasCrossMomentRelation GT BYX betaStar
        etaY etaX delta h.hInt h.hZero
      outcomeRelation := additiveInterventionFamily_hasOutcomeMomentRelation GT BYX betaStar
        etaY etaX delta h.hInt h.hZero
      sigmaSymm := additiveInterventionFamily_sigmaIsSymm nu GT BYX etaY etaX delta }

/-- Penalized version of the bundle constructor; nonnegativity of the actual penalty remains an
optimization assumption. -/
theorem AdditiveInterventionFreshSamplingAssumptions.toFreshSamplingPenalized
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    FreshSamplingConcretePenalizedAssumptions mu mCond C P bInit betaStar
      (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
      (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
      (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
      gamma (∫ xi, etaY xi * etaY xi ∂nu) lam penalty
      (semV nu GT BYX etaY etaX) w0 etaB etaW B KX KY T eHat xHat yHat := by
  exact
    { common := h.toFreshCommon mCond C P bInit betaStar GT BYX etaY etaX delta
        gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat hpenalty
      hpenalty := hpenalty
      population := fun t ht ↦
        additiveInterventionFreshLaw_toFreshPopulationMoments GT BYX betaStar etaY etaX
          delta (h.hLaw t ht) h.hInt
      crossRelation := additiveInterventionFamily_hasCrossMomentRelation GT BYX betaStar
        etaY etaX delta h.hInt h.hZero
      outcomeRelation := additiveInterventionFamily_hasOutcomeMomentRelation GT BYX betaStar
        etaY etaX delta h.hInt h.hZero
      sigmaSymm := additiveInterventionFamily_sigmaIsSymm nu GT BYX etaY etaX delta }

/-- Unpenalized finite-time trajectory bound assembled from model, law, spectral, and projection
interfaces. -/
theorem stochasticNegDRO_additiveSampling_unpenalized_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_sampling_unpenalized_convergence mCond C P bInit betaStar
    (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
    (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
    (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
    gamma (∫ xi, etaY xi * etaY xi ∂nu) lam (semV nu GT BYX etaY etaX) w0
    etaB etaW B KX KY T eHat xHat yHat
    (h.toFreshSamplingUnpenalized mCond C P bInit betaStar GT BYX etaY etaX delta
      gamma lam w0 etaB etaW B KX KY T eHat xHat yHat)

/-- Unpenalized bound for the actual averaged primal iterate. -/
theorem stochasticNegDRO_additiveSampling_unpenalized_averaged_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_sampling_unpenalized_averaged_convergence mCond C P bInit betaStar
    (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
    (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
    (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
    gamma (∫ xi, etaY xi * etaY xi ∂nu) lam (semV nu GT BYX etaY etaX) w0
    etaB etaW B KX KY T eHat xHat yHat
    (h.toFreshSamplingUnpenalized mCond C P bInit betaStar GT BYX etaY etaX delta
      gamma lam w0 etaB etaW B KX KY T eHat xHat yHat)

/-- Unpenalized inverse-square-root step-size trajectory rate. -/
theorem stochasticNegDRO_additiveSampling_unpenalized_invSqrt_rate
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) (gamma lam : ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam 0 w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma 0
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam (semV nu GT BYX etaY etaX) +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  exact stochasticNegDRO_sampling_unpenalized_invSqrt_rate mCond C P bInit betaStar
    (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
    (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
    (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
    gamma (∫ xi, etaY xi * etaY xi ∂nu) lam (semV nu GT BYX etaY etaX) w0
    B KX KY T eHat xHat yHat
    (h.toFreshSamplingUnpenalized mCond C P bInit betaStar GT BYX etaY etaX delta
      gamma lam w0 (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat)

/-- Penalized finite-time trajectory bound; the structural bias is exactly `2 * penalty / lam`. -/
theorem stochasticNegDRO_additiveSampling_penalized_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_sampling_penalized_convergence mCond C P bInit betaStar
    (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
    (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
    (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
    gamma (∫ xi, etaY xi * etaY xi ∂nu) lam penalty (semV nu GT BYX etaY etaX) w0
    etaB etaW B KX KY T eHat xHat yHat
    (h.toFreshSamplingPenalized mCond C P bInit betaStar GT BYX etaY etaX delta
      gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat hpenalty)

/-- Penalized bound for the actual averaged primal iterate. -/
theorem stochasticNegDRO_additiveSampling_penalized_averaged_convergence
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm (semV nu GT BYX etaY etaX) /
        (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  exact stochasticNegDRO_sampling_penalized_averaged_convergence mCond C P bInit betaStar
    (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
    (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
    (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
    gamma (∫ xi, etaY xi * etaY xi ∂nu) lam penalty (semV nu GT BYX etaY etaX) w0
    etaB etaW B KX KY T eHat xHat yHat
    (h.toFreshSamplingPenalized mCond C P bInit betaStar GT BYX etaY etaX delta
      gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat hpenalty)

/-- Penalized inverse-square-root step-size trajectory rate. -/
theorem stochasticNegDRO_additiveSampling_penalized_invSqrt_rate
    {Omega Noise : Type*}
    {mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {nu : Measure Noise} {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : AdditiveInterventionFreshSamplingAssumptions mu nu mCond C P bInit betaStar
      GT BYX etaY etaX delta gamma lam penalty w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)
    (hpenalty : 0 ≤ penalty) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma penalty
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam (semV nu GT BYX etaY etaX) +
        2 * penalty / lam +
        explicitPenalizedRateConstant m penalty bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  exact stochasticNegDRO_sampling_penalized_invSqrt_rate mCond C P bInit betaStar
    (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
    (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
    (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta)
    gamma (∫ xi, etaY xi * etaY xi ∂nu) lam penalty (semV nu GT BYX etaY etaX) w0
    B KX KY T eHat xHat yHat
    (h.toFreshSamplingPenalized mCond C P bInit betaStar GT BYX etaY etaX delta
      gamma lam penalty w0 (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat hpenalty)

end NegDRO
