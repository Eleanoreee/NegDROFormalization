import NegDROFormalization.StochasticNegDROConvergence
import NegDROFormalization.TrajectoryPredictability

/-!
# Stochastic NegDRO convergence from oracle adaptedness

These corollaries remove the explicit trajectory-predictability premises from the existing
finite-time convergence theorems. Predictability is derived by induction from measurable
updates, increasing pre-round information, and next-round measurable stochastic oracles.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Unpenalized finite-time convergence with trajectory predictability derived internally. -/
theorem stochasticNegDRO_unpenalized_convergence_of_oracleAdapted
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin nEnv → ℝ)
    (gHatB : ℕ → Omega → Fin p → ℝ)
    (gHatW : ℕ → Omega → Fin nEnv → ℝ)
    (dualSize : ℕ → Omega → ℝ)
    (etaB etaW B primalGradSqBound dualGradSqBound : ℝ) (T : ℕ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (hPMeas : Measurable P)
    (hGHatBMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatB t omega))
    (hGHatWMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatW t omega))
    (hnEnv : 0 < nEnv) (hT : 0 < T)
    (hetaB : 0 < etaB) (hetaW : 0 < etaW)
    (hB : 0 ≤ B) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hPDist : HasProjectionDistanceBound C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hw0 : IsSimplex w0)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam)
    (hPrimalHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatB t omega i) mu)
    (hPrimalSqInt : ∀ t < T,
      Integrable (fun omega => sqNorm (gHatB t omega)) mu)
    (hPrimalCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => stochasticExpandedPrimalCoefficient
        Sigma gamma v betaStar P bInit etaB gHatB gHatW etaW t omega i) =ᵐ[mu]
        mu[(fun omega => gHatB t omega i) | mCond t])
    (hPrimalCondMoment : ∀ t < T,
      mu[(fun omega => sqNorm (gHatB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ => primalGradSqBound)
    (hDualSizeNonneg : ∀ t < T, ∀ omega, 0 ≤ dualSize t omega)
    (hDualCoordinateBound : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHatW t omega) (dualSize t omega))
    (hDualHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatW t omega i) mu)
    (hDualSizeSqInt : ∀ t < T,
      Integrable (fun omega => (dualSize t omega) ^ 2) mu)
    (hDualCondMoment : ∀ t < T,
      mu[(fun omega => (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound)
    (hDualCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => expandedDualGradient Sigma sigmaYSq v
        (randomPrimalTrajectory P bInit etaB gHatB t omega) betaStar i) =ᵐ[mu]
        mu[(fun omega => gHatW t omega i) | mCond t]) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq
          (mu := mu) P bInit etaB gHatB betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)) / lam +
      2 * Real.log (nEnv : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * dualGradSqBound +
      etaB * primalGradSqBound / (2 * lam) := by
  have hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu :=
    randomPrimalTrajectory_coordinate_aestronglyMeasurable
      mCond P bInit etaB gHatB hMono hPMeas hGHatBMeas
  have hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu := by
    intro t _ht i
    exact randomEGTrajectory_coordinate_aestronglyMeasurable
      mCond gHatW etaW hMono hGHatWMeas t i
  exact stochasticNegDRO_unpenalized_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hInit hbetaStar hPFeas hPDist hCBall hw0
    hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased

/-- Penalized finite-time convergence with trajectory predictability derived internally. -/
theorem stochasticNegDRO_penalized_convergence_of_oracleAdapted
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ)
    (w0 : Fin nEnv → ℝ)
    (gHatB : ℕ → Omega → Fin p → ℝ)
    (gHatW : ℕ → Omega → Fin nEnv → ℝ)
    (dualSize : ℕ → Omega → ℝ)
    (etaB etaW B primalGradSqBound dualGradSqBound : ℝ) (T : ℕ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (hPMeas : Measurable P)
    (hGHatBMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatB t omega))
    (hGHatWMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatW t omega))
    (hnEnv : 0 < nEnv) (hT : 0 < T)
    (hetaB : 0 < etaB) (hetaW : 0 < etaW)
    (hB : 0 ≤ B) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hpenalty : 0 ≤ penalty)
    (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hPDist : HasProjectionDistanceBound C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hw0 : IsSimplex w0)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam)
    (hPrimalHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatB t omega i) mu)
    (hPrimalSqInt : ∀ t < T,
      Integrable (fun omega => sqNorm (gHatB t omega)) mu)
    (hPrimalCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => stochasticExpandedPenalizedPrimalCoefficient
        Sigma gamma v betaStar P bInit etaB gHatB gHatW etaW penalty
          t omega i) =ᵐ[mu]
        mu[(fun omega => gHatB t omega i) | mCond t])
    (hPrimalCondMoment : ∀ t < T,
      mu[(fun omega => sqNorm (gHatB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ => primalGradSqBound)
    (hDualSizeNonneg : ∀ t < T, ∀ omega, 0 ≤ dualSize t omega)
    (hDualCoordinateBound : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHatW t omega) (dualSize t omega))
    (hDualHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatW t omega i) mu)
    (hDualSizeSqInt : ∀ t < T,
      Integrable (fun omega => (dualSize t omega) ^ 2) mu)
    (hDualCondMoment : ∀ t < T,
      mu[(fun omega => (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound)
    (hDualCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => expandedPenalizedDualGradient Sigma sigmaYSq v
        (randomPrimalTrajectory P bInit etaB gHatB t omega) betaStar
        (randomEGTrajectory gHatW etaW t omega) penalty i) =ᵐ[mu]
        mu[(fun omega => gHatW t omega i) | mCond t]) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq
          (mu := mu) P bInit etaB gHatB betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (nEnv : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * dualGradSqBound +
      etaB * primalGradSqBound / (2 * lam) := by
  have hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu :=
    randomPrimalTrajectory_coordinate_aestronglyMeasurable
      mCond P bInit etaB gHatB hMono hPMeas hGHatBMeas
  have hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu := by
    intro t _ht i
    exact randomEGTrajectory_coordinate_aestronglyMeasurable
      mCond gHatW etaW hMono hGHatWMeas t i
  exact stochasticNegDRO_penalized_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hpenalty hInit hbetaStar hPFeas hPDist hCBall
    hw0 hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased

/-- Unpenalized averaged-iterate convergence with both trajectory predictability premises
derived internally from oracle adaptedness. -/
theorem stochasticNegDRO_unpenalized_averaged_convergence_of_oracleAdapted
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin nEnv → ℝ)
    (gHatB : ℕ → Omega → Fin p → ℝ)
    (gHatW : ℕ → Omega → Fin nEnv → ℝ)
    (dualSize : ℕ → Omega → ℝ)
    (etaB etaW B primalGradSqBound dualGradSqBound : ℝ) (T : ℕ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (hPMeas : Measurable P)
    (hGHatBMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatB t omega))
    (hGHatWMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatW t omega))
    (hnEnv : 0 < nEnv) (hT : 0 < T)
    (hetaB : 0 < etaB) (hetaW : 0 < etaW)
    (hB : 0 ≤ B) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hPDist : HasProjectionDistanceBound C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hw0 : IsSimplex w0)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam)
    (hPrimalHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatB t omega i) mu)
    (hPrimalSqInt : ∀ t < T,
      Integrable (fun omega => sqNorm (gHatB t omega)) mu)
    (hPrimalCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => stochasticExpandedPrimalCoefficient
        Sigma gamma v betaStar P bInit etaB gHatB gHatW etaW t omega i) =ᵐ[mu]
        mu[(fun omega => gHatB t omega i) | mCond t])
    (hPrimalCondMoment : ∀ t < T,
      mu[(fun omega => sqNorm (gHatB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ => primalGradSqBound)
    (hDualSizeNonneg : ∀ t < T, ∀ omega, 0 ≤ dualSize t omega)
    (hDualCoordinateBound : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHatW t omega) (dualSize t omega))
    (hDualHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatW t omega i) mu)
    (hDualSizeSqInt : ∀ t < T,
      Integrable (fun omega => (dualSize t omega) ^ 2) mu)
    (hDualCondMoment : ∀ t < T,
      mu[(fun omega => (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound)
    (hDualCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => expandedDualGradient Sigma sigmaYSq v
        (randomPrimalTrajectory P bInit etaB gHatB t omega) betaStar i) =ᵐ[mu]
        mu[(fun omega => gHatW t omega i) | mCond t]) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega =>
        randomPrimalTrajectory P bInit etaB gHatB t omega) omega)
      betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)) / lam +
      2 * Real.log (nEnv : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * dualGradSqBound +
      etaB * primalGradSqBound / (2 * lam) := by
  have hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu :=
    randomPrimalTrajectory_coordinate_aestronglyMeasurable
      mCond P bInit etaB gHatB hMono hPMeas hGHatBMeas
  have hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu := by
    intro t _ht i
    exact randomEGTrajectory_coordinate_aestronglyMeasurable
      mCond gHatW etaW hMono hGHatWMeas t i
  exact stochasticNegDRO_unpenalized_averaged_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hInit hbetaStar hPFeas hPDist hCBall hw0
    hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased

/-- Penalized averaged-iterate convergence with both trajectory predictability premises derived
internally. The structural penalty term remains exactly `2 * penalty / lam`. -/
theorem stochasticNegDRO_penalized_averaged_convergence_of_oracleAdapted
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ)
    (w0 : Fin nEnv → ℝ)
    (gHatB : ℕ → Omega → Fin p → ℝ)
    (gHatW : ℕ → Omega → Fin nEnv → ℝ)
    (dualSize : ℕ → Omega → ℝ)
    (etaB etaW B primalGradSqBound dualGradSqBound : ℝ) (T : ℕ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (hPMeas : Measurable P)
    (hGHatBMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatB t omega))
    (hGHatWMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHatW t omega))
    (hnEnv : 0 < nEnv) (hT : 0 < T)
    (hetaB : 0 < etaB) (hetaW : 0 < etaW)
    (hB : 0 ≤ B) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hpenalty : 0 ≤ penalty)
    (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hPDist : HasProjectionDistanceBound C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hw0 : IsSimplex w0)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam)
    (hPrimalHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatB t omega i) mu)
    (hPrimalSqInt : ∀ t < T,
      Integrable (fun omega => sqNorm (gHatB t omega)) mu)
    (hPrimalCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => stochasticExpandedPenalizedPrimalCoefficient
        Sigma gamma v betaStar P bInit etaB gHatB gHatW etaW penalty
          t omega i) =ᵐ[mu]
        mu[(fun omega => gHatB t omega i) | mCond t])
    (hPrimalCondMoment : ∀ t < T,
      mu[(fun omega => sqNorm (gHatB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ => primalGradSqBound)
    (hDualSizeNonneg : ∀ t < T, ∀ omega, 0 ≤ dualSize t omega)
    (hDualCoordinateBound : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHatW t omega) (dualSize t omega))
    (hDualHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHatW t omega i) mu)
    (hDualSizeSqInt : ∀ t < T,
      Integrable (fun omega => (dualSize t omega) ^ 2) mu)
    (hDualCondMoment : ∀ t < T,
      mu[(fun omega => (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound)
    (hDualCondUnbiased : ∀ t < T, ∀ i,
      (fun omega => expandedPenalizedDualGradient Sigma sigmaYSq v
        (randomPrimalTrajectory P bInit etaB gHatB t omega) betaStar
        (randomEGTrajectory gHatW etaW t omega) penalty i) =ᵐ[mu]
        mu[(fun omega => gHatW t omega i) | mCond t]) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega =>
        randomPrimalTrajectory P bInit etaB gHatB t omega) omega)
      betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (nEnv : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * dualGradSqBound +
      etaB * primalGradSqBound / (2 * lam) := by
  have hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu :=
    randomPrimalTrajectory_coordinate_aestronglyMeasurable
      mCond P bInit etaB gHatB hMono hPMeas hGHatBMeas
  have hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu := by
    intro t _ht i
    exact randomEGTrajectory_coordinate_aestronglyMeasurable
      mCond gHatW etaW hMono hGHatWMeas t i
  exact stochasticNegDRO_penalized_averaged_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hpenalty hInit hbetaStar hPFeas hPDist hCBall
    hw0 hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased

end NegDRO
