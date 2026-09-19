import NegDROFormalization.ExpectedDualRegret
import NegDROFormalization.ExpectedEGTrajectoryRegret

/-!
# Cumulative stochastic dual objective regret

This assembly module combines the one-round expected objective-regret bridges with the expected
regret theorem for the random exponentiated-gradient trajectory. The same sampled gradient
sequence drives both the EG updates and the sampled pairings.

The indexing is zero-based: Lean's `w_0` is the PDF's uniform `w_1`, while Lean rounds
`t = 0, ..., T - 1` correspond to PDF rounds `1, ..., T`.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Expected actual unpenalized comparator-minus-current objective regret at round `t` along
the random EG trajectory. The existing objective-regret definition is reused verbatim. -/
noncomputable def expectedExpandedUnpenalizedRegretAt
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : ℕ → Omega → Fin p → ℝ)
    (gHat : ℕ → Omega → Fin nEnv → ℝ) (etaW : ℝ) (t : ℕ) : ℝ :=
  ∫ omega,
    randomExpandedUnpenalizedRegret Sigma gamma sigmaYSq v betaStar u
      (b t) (randomEGTrajectory gHat etaW t) omega ∂mu

/-- Expected actual penalized comparator-minus-current objective regret at round `t` along
the random EG trajectory. -/
noncomputable def expectedExpandedPenalizedRegretAt
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {nEnv p : ℕ}
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : ℕ → Omega → Fin p → ℝ)
    (gHat : ℕ → Omega → Fin nEnv → ℝ) (etaW penalty : ℝ)
    (t : ℕ) : ℝ :=
  ∫ omega,
    randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar u
      (b t) (randomEGTrajectory gHat etaW t) penalty omega ∂mu

/-- Scalar finite-sum assembly: pointwise domination followed by an upper bound for the
dominating finite sum. -/
theorem finsetRange_sum_le_of_pointwise_le_of_sum_le
    (r ell : ℕ → ℝ) (T : ℕ) (R : ℝ)
    (hPointwise : ∀ t < T, r t ≤ ell t)
    (hSum : ∑ t ∈ Finset.range T, ell t ≤ R) :
    ∑ t ∈ Finset.range T, r t ≤ R := by
  apply le_trans (Finset.sum_le_sum (fun t ht =>
    hPointwise t (Finset.mem_range.mp ht))) hSum

/-- At one round, expected unpenalized objective regret equals expected sampled linearized
regret. Conditional unbiasedness is coordinatewise and a.e.; trajectory predictability remains
an explicit assumption. -/
theorem expectedExpandedUnpenalizedRegretAt_eq_sampledLinearizedRegret
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (hmCond : mCond ≤ mOmega)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : ℕ → Omega → Fin p → ℝ)
    (gHat : ℕ → Omega → Fin nEnv → ℝ) (etaW : ℝ)
    (t : ℕ) (hnEnv : 0 < nEnv) (hu : IsSimplex u)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => randomEGTrajectory gHat etaW t omega i) mu)
    (hCondUnbiased : ∀ i,
      (fun omega =>
        expandedDualGradient Sigma sigmaYSq v (b t omega) betaStar i) =ᵐ[mu]
      mu[(fun omega => gHat t omega i) | mCond]) :
    expectedExpandedUnpenalizedRegretAt
        (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW t =
      ∫ omega, randomEGLinearizedRegret gHat etaW u t omega ∂mu := by
  have hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega =>
          primalDisplacement u (randomEGTrajectory gHat etaW t omega) i) mu :=
    randomEGTrajectory_displacement_aestronglyMeasurable
      (mCond := mCond) (mOmega := mOmega) (mu := mu)
      gHat etaW u t hTrajectoryMeas
  have hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement u (randomEGTrajectory gHat etaW t omega) i‖ ≤ 1 := by
    intro i
    exact Eventually.of_forall (fun omega =>
      randomEGTrajectory_displacement_norm_le_one
        gHat etaW u hnEnv hu t omega i)
  have hBridge :=
    integral_randomExpandedUnpenalizedRegret_eq_sampled_pairing
      hmCond Sigma gamma sigmaYSq v betaStar u (b t)
      (randomEGTrajectory gHat etaW t) (fun omega => gHat t omega)
      hgHatInt hDisplacementMeas 1 hDisplacementBound hCondUnbiased
  simpa [expectedExpandedUnpenalizedRegretAt,
    randomEGLinearizedRegret] using hBridge

/-- At one round, expected penalized objective regret is bounded by the expected sampled
linearized regret. The penalized population coefficient is evaluated at the current random
iterate, not at comparator `u`. -/
theorem expectedExpandedPenalizedRegretAt_le_sampledLinearizedRegret
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (hmCond : mCond ≤ mOmega)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq penalty : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : ℕ → Omega → Fin p → ℝ)
    (gHat : ℕ → Omega → Fin nEnv → ℝ) (etaW : ℝ)
    (t : ℕ) (hnEnv : 0 < nEnv) (hu : IsSimplex u)
    (hPenalty : 0 ≤ penalty)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => randomEGTrajectory gHat etaW t omega i) mu)
    (hCondUnbiased : ∀ i,
      (fun omega =>
        expandedPenalizedDualGradient Sigma sigmaYSq v (b t omega) betaStar
          (randomEGTrajectory gHat etaW t omega) penalty i) =ᵐ[mu]
      mu[(fun omega => gHat t omega i) | mCond]) :
    expectedExpandedPenalizedRegretAt
        (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW penalty t ≤
      ∫ omega, randomEGLinearizedRegret gHat etaW u t omega ∂mu := by
  have hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega =>
          primalDisplacement u (randomEGTrajectory gHat etaW t omega) i) mu :=
    randomEGTrajectory_displacement_aestronglyMeasurable
      (mCond := mCond) (mOmega := mOmega) (mu := mu)
      gHat etaW u t hTrajectoryMeas
  have hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement u (randomEGTrajectory gHat etaW t omega) i‖ ≤ 1 := by
    intro i
    exact Eventually.of_forall (fun omega =>
      randomEGTrajectory_displacement_norm_le_one
        gHat etaW u hnEnv hu t omega i)
  have hBridge :=
    integral_randomExpandedPenalizedRegret_le_sampled_pairing
      hmCond Sigma gamma sigmaYSq penalty v betaStar u (b t)
      (randomEGTrajectory gHat etaW t) (fun omega => gHat t omega)
      hPenalty hgHatInt hDisplacementMeas 1 hDisplacementBound hCondUnbiased
  simpa [expectedExpandedPenalizedRegretAt,
    randomEGLinearizedRegret] using hBridge

/-- Cumulative expected unpenalized objective regret of the actual random EG trajectory.
The same `gHat` drives the trajectory and the sampled-gradient pairing. -/
theorem stochasticEG_cumulative_unpenalized_objectiveRegret
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : ℕ → Omega → Fin p → ℝ)
    (gHat : ℕ → Omega → Fin nEnv → ℝ)
    (G : ℕ → Omega → ℝ) (etaW dualGradSqBound : ℝ) (T : ℕ)
    (hnEnv : 0 < nEnv) (hetaW : 0 < etaW) (hu : IsSimplex u)
    (hG : ∀ t < T, ∀ omega, 0 ≤ G t omega)
    (hg : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHat t omega) (G t omega))
    (hgHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHat etaW t omega i) mu)
    (hGSqInt : ∀ t < T, Integrable (fun omega => (G t omega) ^ 2) mu)
    (hCondMoment : ∀ t < T,
      mu[(fun omega => (G t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound)
    (hCondUnbiased : ∀ t < T, ∀ i,
      (fun omega =>
        expandedDualGradient Sigma sigmaYSq v (b t omega) betaStar i) =ᵐ[mu]
      mu[(fun omega => gHat t omega i) | mCond t]) :
    ∑ t ∈ Finset.range T,
        expectedExpandedUnpenalizedRegretAt
          (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW t ≤
      Real.log (nEnv : ℝ) / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound := by
  have hRound : ∀ t < T,
      expectedExpandedUnpenalizedRegretAt
          (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW t =
        ∫ omega, randomEGLinearizedRegret gHat etaW u t omega ∂mu := by
    intro t ht
    exact expectedExpandedUnpenalizedRegretAt_eq_sampledLinearizedRegret
      (hmCond t) Sigma gamma sigmaYSq v betaStar u b gHat etaW t
      hnEnv hu (hgHatInt t ht) (hTrajectoryMeas t ht) (hCondUnbiased t ht)
  calc
    ∑ t ∈ Finset.range T,
        expectedExpandedUnpenalizedRegretAt
          (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW t =
      ∑ t ∈ Finset.range T,
        ∫ omega, randomEGLinearizedRegret gHat etaW u t omega ∂mu := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hRound t (Finset.mem_range.mp ht)
    _ ≤ Real.log (nEnv : ℝ) / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound :=
      expected_randomEGTrajectory_cumulative_linearizedRegret_of_condMoment_le
        mCond hmCond gHat G etaW dualGradSqBound u T
        hnEnv hetaW hu hG hg hgHatInt hTrajectoryMeas hGSqInt hCondMoment

/-- Cumulative expected penalized objective regret of the actual random EG trajectory. There
is no additional `2 * penalty * T` term: that term belongs to a later primal comparator
reduction, not to dual EG regret telescoping. -/
theorem stochasticEG_cumulative_penalized_objectiveRegret
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {nEnv p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (Sigma : Fin nEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq penalty : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin nEnv → ℝ) (b : ℕ → Omega → Fin p → ℝ)
    (gHat : ℕ → Omega → Fin nEnv → ℝ)
    (G : ℕ → Omega → ℝ) (etaW dualGradSqBound : ℝ) (T : ℕ)
    (hnEnv : 0 < nEnv) (hetaW : 0 < etaW) (hu : IsSimplex u)
    (hPenalty : 0 ≤ penalty)
    (hG : ∀ t < T, ∀ omega, 0 ≤ G t omega)
    (hg : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHat t omega) (G t omega))
    (hgHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHat etaW t omega i) mu)
    (hGSqInt : ∀ t < T, Integrable (fun omega => (G t omega) ^ 2) mu)
    (hCondMoment : ∀ t < T,
      mu[(fun omega => (G t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound)
    (hCondUnbiased : ∀ t < T, ∀ i,
      (fun omega =>
        expandedPenalizedDualGradient Sigma sigmaYSq v (b t omega) betaStar
          (randomEGTrajectory gHat etaW t omega) penalty i) =ᵐ[mu]
      mu[(fun omega => gHat t omega i) | mCond t]) :
    ∑ t ∈ Finset.range T,
        expectedExpandedPenalizedRegretAt
          (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW penalty t ≤
      Real.log (nEnv : ℝ) / etaW +
        etaW * (T : ℝ) / 2 * dualGradSqBound := by
  have hRound : ∀ t < T,
      expectedExpandedPenalizedRegretAt
          (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW penalty t ≤
        ∫ omega, randomEGLinearizedRegret gHat etaW u t omega ∂mu := by
    intro t ht
    exact expectedExpandedPenalizedRegretAt_le_sampledLinearizedRegret
      (hmCond t) Sigma gamma sigmaYSq penalty v betaStar u b gHat etaW t
      hnEnv hu hPenalty (hgHatInt t ht) (hTrajectoryMeas t ht)
      (hCondUnbiased t ht)
  exact finsetRange_sum_le_of_pointwise_le_of_sum_le
    (fun t => expectedExpandedPenalizedRegretAt
      (mu := mu) Sigma gamma sigmaYSq v betaStar u b gHat etaW penalty t)
    (fun t => ∫ omega, randomEGLinearizedRegret gHat etaW u t omega ∂mu)
    T (Real.log (nEnv : ℝ) / etaW +
      etaW * (T : ℝ) / 2 * dualGradSqBound)
    hRound
    (expected_randomEGTrajectory_cumulative_linearizedRegret_of_condMoment_le
      mCond hmCond gHat G etaW dualGradSqBound u T
      hnEnv hetaW hu hG hg hgHatInt hTrajectoryMeas hGSqInt hCondMoment)

end NegDRO
