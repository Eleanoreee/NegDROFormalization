import NegDROFormalization.StochasticPrimalTrajectory
import NegDROFormalization.StochasticDualRegret
import NegDROFormalization.ExpectedConcretePrimalDirection
import NegDROFormalization.AveragedPrimalIterate
import NegDROFormalization.RegretToConvergence

/-!
# Stochastic NegDRO convergence assembly

This module instantiates the scalar convergence theorem on the actual random projected-primal
and exponentiated-gradient trajectories. Both oracle sequences use the same sample `omega`;
no independence assumption is made. Predictability, projection properties, and oracle moment
interfaces remain explicit hypotheses.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- The concrete unpenalized population coefficient along the actual coupled trajectories. -/
noncomputable def stochasticExpandedPrimalCoefficient
    {Omega : Type*} {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ) (gamma : ℝ)
    (v betaStar : Fin p → ℝ)
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ) (etaB : ℝ)
    (gHatB : ℕ → Omega → Fin p → ℝ)
    (gHatW : ℕ → Omega → Fin nEnv → ℝ) (etaW : ℝ) :
    ℕ → Omega → Fin p → ℝ :=
  fun t omega => expandedPrimalCoefficient Sigma gamma v
    (randomPrimalTrajectory P bInit etaB gHatB t omega) betaStar
    (randomEGTrajectory gHatW etaW t omega)

/-- The penalized population coefficient along the same coupled trajectories. The penalty is
dual-only, but this named interface records the penalized model used in the comparator bound. -/
noncomputable def stochasticExpandedPenalizedPrimalCoefficient
    {Omega : Type*} {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ) (gamma : ℝ)
    (v betaStar : Fin p → ℝ)
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ) (etaB : ℝ)
    (gHatB : ℕ → Omega → Fin p → ℝ)
    (gHatW : ℕ → Omega → Fin nEnv → ℝ) (etaW penalty : ℝ) :
    ℕ → Omega → Fin p → ℝ :=
  fun t omega => expandedPenalizedPrimalCoefficient Sigma gamma v
    (randomPrimalTrajectory P bInit etaB gHatB t omega) betaStar
    (randomEGTrajectory gHatW etaW t omega) penalty

/-- The expected initial squared distance is the deterministic initial squared distance. -/
theorem expectedPrimalTrajectoryDistSq_zero_eq
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit betaStar : Fin p → ℝ)
    (etaB : ℝ) (gHatB : ℕ → Omega → Fin p → ℝ) :
    expectedPrimalTrajectoryDistSq
        (mu := mu) P bInit etaB gHatB betaStar 0 =
      sqDist bInit betaStar := by
  simp [expectedPrimalTrajectoryDistSq]

/-- Expected squared distance is nonnegative, directly from coordinate squares. -/
theorem expectedPrimalTrajectoryDistSq_nonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit betaStar : Fin p → ℝ)
    (etaB : ℝ) (gHatB : ℕ → Omega → Fin p → ℝ) (t : ℕ) :
    0 ≤ expectedPrimalTrajectoryDistSq
      (mu := mu) P bInit etaB gHatB betaStar t := by
  apply integral_nonneg_of_ae
  exact Eventually.of_forall (fun _omega => sqNorm_nonneg _)

/-- Natural scalar-theorem form of unpenalized stochastic convergence. The quantities
`primalGradSqBound` and `dualGradSqBound` are already squared bounds. -/
theorem stochasticNegDRO_unpenalized_convergence_unsimplified
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
    (hmCond : ∀ t, mCond t ≤ mOmega)
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
    (hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu)
    (hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu)
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
      2 * (Real.log (nEnv : ℝ) / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound) / (lam * (T : ℝ)) +
      etaB * primalGradSqBound / (2 * lam) := by
  let b : ℕ → Omega → Fin p → ℝ :=
    fun t omega => randomPrimalTrajectory P bInit etaB gHatB t omega
  let w : ℕ → Omega → Fin nEnv → ℝ :=
    fun t omega => randomEGTrajectory gHatW etaW t omega
  let F : ℕ → Omega → Fin p → ℝ :=
    stochasticExpandedPrimalCoefficient
      Sigma gamma v betaStar P bInit etaB gHatB gHatW etaW
  let distSq : ℕ → ℝ := fun t =>
    expectedPrimalTrajectoryDistSq
      (mu := mu) P bInit etaB gHatB betaStar t
  let direction : ℕ → ℝ := fun t =>
    expectedPrimalTrajectoryDirection
      (mu := mu) P bInit etaB gHatB F betaStar t
  let regret : ℕ → ℝ := fun t =>
    expectedExpandedUnpenalizedRegretAt
      (mu := mu) Sigma gamma sigmaYSq v betaStar w0 b gHatW etaW t
  have hrec : ∀ t < T,
      distSq (t + 1) ≤ distSq t - 2 * etaB * direction t +
        etaB ^ 2 * primalGradSqBound := by
    intro t ht
    exact stochasticPrimalTrajectory_expected_recursion
      mCond hmCond C P bInit betaStar etaB B primalGradSqBound gHatB F t
      hB hInit hbetaStar hPFeas hPDist hCBall hPrimalTrajectoryMeas
      (hPrimalHatInt t ht) (hPrimalSqInt t ht)
      (by simpa [F] using hPrimalCondUnbiased t ht)
      (hPrimalCondMoment t ht)
  have hdirection : ∀ t < T,
      direction t ≥ lam * distSq t -
        sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2) -
        2 * regret t := by
    intro t ht
    have hPrimalDisplacementMeas : ∀ i,
        AEStronglyMeasurable[mCond t]
          (fun omega => primalDisplacement (b t omega) betaStar i) mu := by
      simpa [b] using
        randomPrimalTrajectory_displacement_aestronglyMeasurable
          (mCond := mCond t) (mOmega := mOmega) (mu := mu)
          P bInit betaStar etaB gHatB t (hPrimalTrajectoryMeas t)
    have hPrimalDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
        ‖primalDisplacement (b t omega) betaStar i‖ ≤ 2 * B := by
      intro i
      exact Eventually.of_forall (fun omega => by
        simpa [b, Real.norm_eq_abs] using
          abs_randomPrimalTrajectory_displacement_le_two_mul
            C P bInit betaStar etaB B gHatB hB hInit hbetaStar
            hPFeas hCBall t omega i)
    have hDirectionInt : Integrable (fun omega =>
        vectorDot (F t omega)
          (primalDisplacement (b t omega) betaStar)) mu :=
      integrable_population_vectorDot_of_condExp_ae_eq
        (hmCond t) (gHatB t) (F t)
        (fun omega => primalDisplacement (b t omega) betaStar)
        (hPrimalHatInt t ht) hPrimalDisplacementMeas (2 * B)
        hPrimalDisplacementBound
        (by simpa [F] using hPrimalCondUnbiased t ht)
    have hDistInt : Integrable
        (fun omega => sqDist (b t omega) betaStar) mu := by
      simpa [b] using integrable_randomPrimalTrajectory_sqDist
        (hmCond t) C P bInit betaStar etaB B gHatB hInit hbetaStar
        hPFeas hCBall t (hPrimalTrajectoryMeas t)
    have hDualDisplacementMeas : ∀ i,
        AEStronglyMeasurable[mCond t]
          (fun omega => primalDisplacement w0 (w t omega) i) mu := by
      simpa [w] using randomEGTrajectory_displacement_aestronglyMeasurable
        (mCond := mCond t) (mOmega := mOmega) (mu := mu)
        gHatW etaW w0 t (hDualTrajectoryMeas t ht)
    have hDualDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
        ‖primalDisplacement w0 (w t omega) i‖ ≤ 1 := by
      intro i
      exact Eventually.of_forall (fun omega => by
        simpa [w] using randomEGTrajectory_displacement_norm_le_one
          gHatW etaW w0 hnEnv hw0 t omega i)
    have hRegretInt : Integrable
        (randomExpandedUnpenalizedRegret Sigma gamma sigmaYSq v betaStar
          w0 (b t) (w t)) mu :=
      integrable_randomExpandedUnpenalizedRegret_of_condExp_ae_eq
        (hmCond t) Sigma gamma sigmaYSq v betaStar w0 (b t) (w t)
        (gHatW t) (hDualHatInt t ht) hDualDisplacementMeas 1
        hDualDisplacementBound (hDualCondUnbiased t ht)
    have hBound := expected_expandedPrimalCoefficient_unpenalized_lower_bound
      Sigma gamma sigmaYSq lam v betaStar w0 (b t) (w t)
      hnEnv hgamma hlam hw0
      (fun omega => by simpa [w] using
        randomEGTrajectory_isSimplex gHatW etaW hnEnv t omega)
      hSigma hcurvature
      (by simpa [F, stochasticExpandedPrimalCoefficient,
          randomExpandedPrimalCoefficient,
          expectedPrimalTrajectoryDirection, expectedDirection, b, w] using hDirectionInt)
      hDistInt hRegretInt
    simpa [direction, distSq, regret, F, b, w,
      stochasticExpandedPrimalCoefficient, randomExpandedPrimalCoefficient,
      expectedPrimalTrajectoryDirection, expectedRandomExpandedPrimalDirection,
      expectedPrimalTrajectoryDistSq, expectedDirection,
      expectedExpandedUnpenalizedRegretAt] using hBound
  have hterminal : 0 ≤ distSq T := by
    exact expectedPrimalTrajectoryDistSq_nonneg
      P bInit betaStar etaB gHatB T
  have hregret : ∑ t ∈ Finset.range T, regret t ≤
      Real.log (nEnv : ℝ) / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound := by
    exact stochasticEG_cumulative_unpenalized_objectiveRegret
      mCond hmCond Sigma gamma sigmaYSq v betaStar w0 b gHatW dualSize
      etaW dualGradSqBound T hnEnv hetaW hw0 hDualSizeNonneg
      hDualCoordinateBound hDualHatInt hDualTrajectoryMeas hDualSizeSqInt
      hDualCondMoment hDualCondUnbiased
  have hScalar := scalar_theorem_4_3_unpenalized
    T distSq direction regret etaB lam
    (sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2))
    primalGradSqBound
    (Real.log (nEnv : ℝ) / etaW +
      etaW * (T : ℝ) / 2 * dualGradSqBound)
    hT hrec hdirection hterminal hregret hetaB hlam
  rw [show distSq 0 = sqDist bInit betaStar by
    simpa [distSq] using expectedPrimalTrajectoryDistSq_zero_eq
      (mu := mu) P bInit betaStar etaB gHatB] at hScalar
  simpa [distSq] using hScalar

/-- Algebraic simplification of the cumulative EG contribution. -/
theorem simplify_stochastic_dual_regret_term
    (T : ℕ) (n etaW lam dualGradSqBound : ℝ)
    (hT : 0 < T) (hetaW : 0 < etaW) (hlam : 0 < lam) :
    2 * (Real.log n / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound) / (lam * (T : ℝ)) =
      2 * Real.log n / (lam * etaW * (T : ℝ)) +
        etaW / lam * dualGradSqBound := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  field_simp [ne_of_gt hetaW, ne_of_gt hlam, hTne]

/-- Simplified unpenalized stochastic convergence bound. -/
theorem stochasticNegDRO_unpenalized_convergence
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
    (hmCond : ∀ t, mCond t ≤ mOmega)
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
    (hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu)
    (hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu)
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
  have h := stochasticNegDRO_unpenalized_convergence_unsimplified
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hInit hbetaStar hPFeas hPDist hCBall hw0
    hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased
  rw [simplify_stochastic_dual_regret_term
    T (nEnv : ℝ) etaW lam dualGradSqBound hT hetaW hlam] at h
  convert h using 1
  ring

/-- Simplified penalized stochastic convergence bound. The unique structural penalty loss is
`2 * penalty / lam`; the dual regret theorem contributes no additional penalty term. -/
theorem stochasticNegDRO_penalized_convergence
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
    (hmCond : ∀ t, mCond t ≤ mOmega)
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
    (hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu)
    (hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu)
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
  let b : ℕ → Omega → Fin p → ℝ :=
    fun t omega => randomPrimalTrajectory P bInit etaB gHatB t omega
  let w : ℕ → Omega → Fin nEnv → ℝ :=
    fun t omega => randomEGTrajectory gHatW etaW t omega
  let F : ℕ → Omega → Fin p → ℝ :=
    stochasticExpandedPenalizedPrimalCoefficient
      Sigma gamma v betaStar P bInit etaB gHatB gHatW etaW penalty
  let distSq : ℕ → ℝ := fun t =>
    expectedPrimalTrajectoryDistSq
      (mu := mu) P bInit etaB gHatB betaStar t
  let direction : ℕ → ℝ := fun t =>
    expectedPrimalTrajectoryDirection
      (mu := mu) P bInit etaB gHatB F betaStar t
  let regret : ℕ → ℝ := fun t =>
    expectedExpandedPenalizedRegretAt
      (mu := mu) Sigma gamma sigmaYSq v betaStar w0 b gHatW etaW penalty t
  have hrec : ∀ t < T,
      distSq (t + 1) ≤ distSq t - 2 * etaB * direction t +
        etaB ^ 2 * primalGradSqBound := by
    intro t ht
    exact stochasticPrimalTrajectory_expected_recursion
      mCond hmCond C P bInit betaStar etaB B primalGradSqBound gHatB F t
      hB hInit hbetaStar hPFeas hPDist hCBall hPrimalTrajectoryMeas
      (hPrimalHatInt t ht) (hPrimalSqInt t ht)
      (by simpa [F] using hPrimalCondUnbiased t ht)
      (hPrimalCondMoment t ht)
  have hdirection : ∀ t < T,
      direction t ≥ lam * distSq t -
        sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2) -
        2 * penalty - 2 * regret t := by
    intro t ht
    have hPrimalDisplacementMeas : ∀ i,
        AEStronglyMeasurable[mCond t]
          (fun omega => primalDisplacement (b t omega) betaStar i) mu := by
      simpa [b] using
        randomPrimalTrajectory_displacement_aestronglyMeasurable
          (mCond := mCond t) (mOmega := mOmega) (mu := mu)
          P bInit betaStar etaB gHatB t (hPrimalTrajectoryMeas t)
    have hPrimalDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
        ‖primalDisplacement (b t omega) betaStar i‖ ≤ 2 * B := by
      intro i
      exact Eventually.of_forall (fun omega => by
        simpa [b, Real.norm_eq_abs] using
          abs_randomPrimalTrajectory_displacement_le_two_mul
            C P bInit betaStar etaB B gHatB hB hInit hbetaStar
            hPFeas hCBall t omega i)
    have hDirectionInt : Integrable (fun omega =>
        vectorDot (F t omega)
          (primalDisplacement (b t omega) betaStar)) mu :=
      integrable_population_vectorDot_of_condExp_ae_eq
        (hmCond t) (gHatB t) (F t)
        (fun omega => primalDisplacement (b t omega) betaStar)
        (hPrimalHatInt t ht) hPrimalDisplacementMeas (2 * B)
        hPrimalDisplacementBound
        (by simpa [F] using hPrimalCondUnbiased t ht)
    have hDistInt : Integrable
        (fun omega => sqDist (b t omega) betaStar) mu := by
      simpa [b] using integrable_randomPrimalTrajectory_sqDist
        (hmCond t) C P bInit betaStar etaB B gHatB hInit hbetaStar
        hPFeas hCBall t (hPrimalTrajectoryMeas t)
    have hDualDisplacementMeas : ∀ i,
        AEStronglyMeasurable[mCond t]
          (fun omega => primalDisplacement w0 (w t omega) i) mu := by
      simpa [w] using randomEGTrajectory_displacement_aestronglyMeasurable
        (mCond := mCond t) (mOmega := mOmega) (mu := mu)
        gHatW etaW w0 t (hDualTrajectoryMeas t ht)
    have hDualDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
        ‖primalDisplacement w0 (w t omega) i‖ ≤ 1 := by
      intro i
      exact Eventually.of_forall (fun omega => by
        simpa [w] using randomEGTrajectory_displacement_norm_le_one
          gHatW etaW w0 hnEnv hw0 t omega i)
    have hRegretInt : Integrable
        (randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar
          w0 (b t) (w t) penalty) mu :=
      integrable_randomExpandedPenalizedRegret_of_condExp_ae_eq
        (hmCond t) Sigma gamma sigmaYSq penalty v betaStar w0 (b t) (w t)
        (gHatW t) (hDualHatInt t ht) hDualDisplacementMeas 1
        hDualDisplacementBound (hDualCondUnbiased t ht)
    have hBound := expected_expandedPrimalCoefficient_penalized_lower_bound
      Sigma gamma sigmaYSq lam penalty v betaStar w0 (b t) (w t)
      hnEnv hgamma hlam hpenalty hw0
      (fun omega => by simpa [w] using
        randomEGTrajectory_isSimplex gHatW etaW hnEnv t omega)
      hSigma hcurvature
      (by simpa [F, stochasticExpandedPenalizedPrimalCoefficient,
          randomExpandedPenalizedPrimalCoefficient,
          expectedPrimalTrajectoryDirection, expectedDirection, b, w] using hDirectionInt)
      hDistInt hRegretInt
    have hBound' : direction t ≥ lam * distSq t -
        sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2) -
        2 * regret t - 2 * penalty := by
      simpa [direction, distSq, regret, F, b, w,
        stochasticExpandedPenalizedPrimalCoefficient,
        randomExpandedPenalizedPrimalCoefficient,
        expectedPrimalTrajectoryDirection,
        expectedRandomExpandedPenalizedPrimalDirection,
        expectedPrimalTrajectoryDistSq, expectedDirection,
        expectedExpandedPenalizedRegretAt] using hBound
    linarith
  have hterminal : 0 ≤ distSq T := by
    exact expectedPrimalTrajectoryDistSq_nonneg
      P bInit betaStar etaB gHatB T
  have hregret : ∑ t ∈ Finset.range T, regret t ≤
      Real.log (nEnv : ℝ) / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound := by
    exact stochasticEG_cumulative_penalized_objectiveRegret
      mCond hmCond Sigma gamma sigmaYSq penalty v betaStar w0 b gHatW
      dualSize etaW dualGradSqBound T hnEnv hetaW hw0 hpenalty
      hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualTrajectoryMeas
      hDualSizeSqInt hDualCondMoment hDualCondUnbiased
  have hScalar := scalar_theorem_3_4_penalized
    T distSq direction regret etaB lam
    (sqNorm v / (lam * (1 + gamma * (nEnv : ℝ)) ^ 2)) penalty
    primalGradSqBound
    (Real.log (nEnv : ℝ) / etaW +
      etaW * (T : ℝ) / 2 * dualGradSqBound)
    hT hrec hdirection hterminal hregret hetaB hlam hpenalty
  rw [show distSq 0 = sqDist bInit betaStar by
    simpa [distSq] using expectedPrimalTrajectoryDistSq_zero_eq
      (mu := mu) P bInit betaStar etaB gHatB] at hScalar
  rw [simplify_stochastic_dual_regret_term
    T (nEnv : ℝ) etaW lam dualGradSqBound hT hetaW hlam] at hScalar
  simpa [distSq, add_assoc] using hScalar

/-- Expected squared-distance bound for the arithmetic average of the actual unpenalized
random primal iterates. No square root or asymptotic notation is taken here. -/
theorem stochasticNegDRO_unpenalized_averaged_convergence
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
    (hmCond : ∀ t, mCond t ≤ mOmega)
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
    (hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu)
    (hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu)
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
  let b : ℕ → Omega → Fin p → ℝ :=
    fun t omega => randomPrimalTrajectory P bInit etaB gHatB t omega
  have hMem : ∀ t < T, ∀ omega, b t omega ∈ C := by
    intro t _ht omega
    exact randomPrimalTrajectory_mem
      C P bInit etaB gHatB hInit hPFeas t omega
  have hMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable (fun omega => b t omega i) mu := by
    intro t _ht i
    exact (hPrimalTrajectoryMeas t i).mono (hmCond t)
  have hJensen := integral_sqDist_randomPrimalAverage_le_average_integral_sqDist
    T hT C B betaStar b hCBall hbetaStar hMem hMeas
  have hConvergence := stochasticNegDRO_unpenalized_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hInit hbetaStar hPFeas hPDist hCBall hw0
    hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased
  apply le_trans hJensen
  simpa [b, expectedPrimalTrajectoryDistSq] using hConvergence

/-- Expected squared-distance bound for the arithmetic average of the actual penalized random
primal iterates, with exactly one `2 * penalty / lam` term. -/
theorem stochasticNegDRO_penalized_averaged_convergence
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
    (hmCond : ∀ t, mCond t ≤ mOmega)
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
    (hPrimalTrajectoryMeas : ∀ t i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomPrimalTrajectory P bInit etaB gHatB t omega i) mu)
    (hDualTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHatW etaW t omega i) mu)
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
  let b : ℕ → Omega → Fin p → ℝ :=
    fun t omega => randomPrimalTrajectory P bInit etaB gHatB t omega
  have hMem : ∀ t < T, ∀ omega, b t omega ∈ C := by
    intro t _ht omega
    exact randomPrimalTrajectory_mem
      C P bInit etaB gHatB hInit hPFeas t omega
  have hMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable (fun omega => b t omega i) mu := by
    intro t _ht i
    exact (hPrimalTrajectoryMeas t i).mono (hmCond t)
  have hJensen := integral_sqDist_randomPrimalAverage_le_average_integral_sqDist
    T hT C B betaStar b hCBall hbetaStar hMem hMeas
  have hConvergence := stochasticNegDRO_penalized_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 gHatB gHatW
    dualSize etaB etaW B primalGradSqBound dualGradSqBound T hmCond hnEnv hT
    hetaB hetaW hB hgamma hlam hpenalty hInit hbetaStar hPFeas hPDist hCBall
    hw0 hSigma hcurvature hPrimalTrajectoryMeas hDualTrajectoryMeas
    hPrimalHatInt hPrimalSqInt hPrimalCondUnbiased hPrimalCondMoment
    hDualSizeNonneg hDualCoordinateBound hDualHatInt hDualSizeSqInt
    hDualCondMoment hDualCondUnbiased
  apply le_trans hJensen
  simpa [b, expectedPrimalTrajectoryDistSq] using hConvergence

end NegDRO
