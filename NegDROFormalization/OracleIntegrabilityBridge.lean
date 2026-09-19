import NegDROFormalization.FreshFiniteEnvironmentMoments

/-!
# Integrability of the concrete stochastic-oracle trajectory

This module closes the integrability side conditions for the project's concrete fresh-sample
projected-SGD/EG trajectory.  The proofs use the selected-environment mixed and fourth moments
derived from the universal fresh conditional law, together with predictability, feasibility of
the primal trajectory, and simplex invariance of the EG trajectory.  No conditional expectation
bound on an oracle is used to prove that oracle's integrability.

All vector sizes are the project's explicit finite-coordinate `sqNorm`.  In particular, no
default norm on a raw function type is used.
-/

set_option autoImplicit false

open MeasureTheory
open scoped MeasureTheory

namespace NegDRO

/-- Fresh selected-environment moments yield the existing raw conditional-moment interface along
the actual coupled trajectory.  This helper contains no oracle-integrability premise. -/
theorem concreteTrajectory_rawMoments_of_fresh
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit : Fin p → ℝ) (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega) (hPMeas : Measurable P)
    (hPrimalMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hDualMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hm : 0 < m) (hB : 0 ≤ B) (hInit : bInit ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P) (hCBall : SetContainedInCoordinateSqBall C B)
    (t : ℕ)
    (hFresh : HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
      (eHat t) (xHat t) (yHat t) KX KY) :
    HasRawConcreteConditionalMoments (mCond := mCond t) mu gamma B KX KY
      (eHat t) (xHat t) (yHat t)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).1)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).2) := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let b : Omega → Fin p → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1
  let w : Omega → Fin m → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2
  have hbMeasCond : ∀ i, AEStronglyMeasurable[mCond t]
      (fun omega ↦ b omega i) mu := by
    intro i
    have hTrajectory := randomPrimalTrajectory_coordinate_aestronglyMeasurable
      (mu := mu) mCond P bInit etaB gB hMono hPMeas hPrimalMeas t i
    refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
    dsimp [b, gB]
    rw [concreteNegDROState_primal_eq_randomPrimalTrajectory]
  have hbMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ b omega i) mu :=
    fun i ↦ (hbMeasCond i).mono (hmCond t)
  have hwMeas : ∀ e, AEStronglyMeasurable[mCond t]
      (fun omega ↦ w omega e) mu := by
    intro e
    have hTrajectory := randomEGTrajectory_coordinate_aestronglyMeasurable
      (mu := mu) mCond gW etaW hMono hDualMeas t e
    refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
    dsimp [w, gW]
    rw [concreteNegDROState_dual_eq_randomEGTrajectory]
  have hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2 := fun omega ↦ hCBall _
    (concreteNegDROState_primal_mem C P bInit gamma penalty etaB etaW
      eHat xHat yHat hInit hPFeas t omega)
  have hw : ∀ omega, IsSimplex (w omega) := fun omega ↦
    concreteNegDROState_dual_isSimplex P bInit gamma penalty etaB etaW
      eHat xHat yHat hm t omega
  exact HasFreshFiniteEnvironmentRawMoments.toHasRawConcreteConditionalMoments
    (eHat t) (xHat t) (yHat t) b w gamma B KX KY hm hB
    (hmCond t) hbMeas hwMeas hb hw hFresh

/-- The concrete primal oracle's explicit coordinate `sqNorm` is integrable.  The proof uses the
pointwise residual-square estimate and the fresh selected mixed/X-fourth moments. -/
theorem integrable_concreteTrajectoryPrimalOracle_sqNorm_of_fresh
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit : Fin p → ℝ) (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega) (hPMeas : Measurable P)
    (hPrimalMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hDualMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hm : 0 < m) (hB : 0 ≤ B) (hInit : bInit ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P) (hCBall : SetContainedInCoordinateSqBall C B)
    (t : ℕ)
    (hFresh : HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
      (eHat t) (xHat t) (yHat t) KX KY) :
    Integrable (fun omega ↦ sqNorm
      (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega)) mu := by
  let b : Omega → Fin p → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1
  let w : Omega → Fin m → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2
  have hRaw := concreteTrajectory_rawMoments_of_fresh mCond C P bInit
    gamma penalty etaB etaW B KX KY eHat xHat yHat hMono hmCond hPMeas
    hPrimalMeas hDualMeas hm hB hInit hPFeas hCBall t hFresh
  rcases hRaw with ⟨hMixedInt, hXFourthInt, _hMixed, _hXFourth,
    _hResidualInt, _hYFourthInt, _hDataXFourthInt, _hYFourth, _hDataXFourth⟩
  let c : ℝ := 8 * (m : ℝ) ^ 2
  let d : ℝ := 8 * (m : ℝ) ^ 2 * B ^ 2
  have hUpperInt : Integrable (fun omega ↦
      c * rawShiftedMixedMagnitude gamma (eHat t) (xHat t) (yHat t) w omega +
        d * rawShiftedXFourthMagnitude gamma (eHat t) (xHat t) w omega) mu :=
    (hMixedInt.const_mul c).add (hXFourthInt.const_mul d)
  have hOracleMeasAmbient : Measurable[mOmega] (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega) :=
    (hPrimalMeas t).mono (hmCond (t + 1)) le_rfl
  have hOracleCoordMeas : ∀ i, AEStronglyMeasurable (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega i) mu := fun i ↦
    (measurable_coordinate_of_finVector hOracleMeasAmbient i).aestronglyMeasurable
  have hOracleSqMeas : AEStronglyMeasurable (fun omega ↦ sqNorm
      (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega)) mu :=
    aestronglyMeasurable_sqNorm_of_coordinatewise _ hOracleCoordMeas
  refine hUpperInt.mono_nonneg hOracleSqMeas
    (ae_of_all mu (fun omega ↦ sqNorm_nonneg _)) ?_
  refine ae_of_all mu (fun omega ↦ ?_)
  have hb : sqNorm (b omega) ≤ B ^ 2 := hCBall _
    (concreteNegDROState_primal_mem C P bInit gamma penalty etaB etaW
      eHat xHat yHat hInit hPFeas t omega)
  have hPoint := samplePrimalOracle_sqNorm_le gamma (eHat t omega)
    (xHat t omega) (yHat t omega) B (b omega) (w omega) hB hb
  dsimp [concreteTrajectoryPrimalOracle, b, w]
  dsimp [c, d, rawShiftedMixedMagnitude, rawShiftedXFourthMagnitude]
  nlinarith

/-- Every coordinate of the concrete primal oracle is integrable.  This is the finite
probability-space `L² -> L¹` consequence of the preceding explicit-`sqNorm` result. -/
theorem integrable_concreteTrajectoryPrimalOracle_coordinate_of_fresh
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit : Fin p → ℝ) (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega) (hPMeas : Measurable P)
    (hPrimalMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hDualMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hm : 0 < m) (hB : 0 ≤ B) (hInit : bInit ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P) (hCBall : SetContainedInCoordinateSqBall C B)
    (t : ℕ)
    (hFresh : HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
      (eHat t) (xHat t) (yHat t) KX KY) (i : Fin p) :
    Integrable (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega i) mu := by
  let g : Omega → Fin p → ℝ := fun omega ↦
    concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega
  have hSqNormInt : Integrable (fun omega ↦ sqNorm (g omega)) mu :=
    integrable_concreteTrajectoryPrimalOracle_sqNorm_of_fresh mCond C P bInit
      gamma penalty etaB etaW B KX KY eHat xHat yHat hMono hmCond hPMeas
      hPrimalMeas hDualMeas hm hB hInit hPFeas hCBall t hFresh
  have hGMeasAmbient : Measurable[mOmega] g :=
    (hPrimalMeas t).mono (hmCond (t + 1)) le_rfl
  have hCoordMeas : AEStronglyMeasurable (fun omega ↦ g omega i) mu :=
    (measurable_coordinate_of_finVector hGMeasAmbient i).aestronglyMeasurable
  have hCoordSqInt : Integrable (fun omega ↦ (g omega i) ^ 2) mu := by
    refine hSqNormInt.mono_nonneg (hCoordMeas.pow 2)
      (ae_of_all mu (fun omega ↦ sq_nonneg _)) ?_
    exact ae_of_all mu (fun omega ↦ coordinate_sq_le_sqNorm (g omega) i)
  have hMem : MemLp (fun omega ↦ g omega i) 2 mu :=
    (memLp_two_iff_integrable_sq hCoordMeas).2 hCoordSqInt
  exact hMem.integrable one_le_two

/-- The square of the concrete dual coordinate-bound process is integrable.  The unpenalized
part is a constant multiple of the fourth residual; the penalty is added using the same
two-square inequality as the existing explicit penalized moment bound. -/
theorem integrable_concreteTrajectoryDualSize_sq_of_fresh
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit : Fin p → ℝ) (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega) (hPMeas : Measurable P)
    (hPrimalMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hDualMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hm : 0 < m) (hB : 0 ≤ B) (hInit : bInit ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P) (hCBall : SetContainedInCoordinateSqBall C B)
    (t : ℕ)
    (hFresh : HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
      (eHat t) (xHat t) (yHat t) KX KY) :
    Integrable (fun omega ↦
      (concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega) ^ 2) mu := by
  let b : Omega → Fin p → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1
  have hRaw := concreteTrajectory_rawMoments_of_fresh mCond C P bInit
    gamma penalty etaB etaW B KX KY eHat xHat yHat hMono hmCond hPMeas
    hPrimalMeas hDualMeas hm hB hInit hPFeas hCBall t hFresh
  rcases hRaw with ⟨_hMixedInt, _hXFourthInt, _hMixed, _hXFourth,
    hResidualInt, _hYFourthInt, _hDataXFourthInt, _hYFourth, _hDataXFourth⟩
  let unpen : Omega → ℝ := fun omega ↦
    sampleDualCoordinateBound m (xHat t omega) (yHat t omega) (b omega)
  have hUnpenSqInt : Integrable (fun omega ↦ (unpen omega) ^ 2) mu := by
    simpa only [unpen, sampleDualCoordinateBound_sq] using
      hResidualInt.const_mul ((m : ℝ) ^ 2)
  have hUpperInt : Integrable (fun omega ↦
      2 * (unpen omega) ^ 2 + 8 * penalty ^ 2) mu :=
    (hUnpenSqInt.const_mul 2).add (integrable_const (8 * penalty ^ 2))
  have hbMeasCond : ∀ i, AEStronglyMeasurable[mCond t]
      (fun omega ↦ b omega i) mu := by
    intro i
    let gB := concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat
    have hTrajectory := randomPrimalTrajectory_coordinate_aestronglyMeasurable
      (mu := mu) mCond P bInit etaB gB hMono hPMeas hPrimalMeas t i
    refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
    dsimp [b, gB]
    rw [concreteNegDROState_primal_eq_randomPrimalTrajectory]
  have hbMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ b omega i) mu :=
    fun i ↦ (hbMeasCond i).mono (hmCond t)
  have hDotMeas : AEStronglyMeasurable
      (fun omega ↦ vectorDot (xHat t omega) (b omega)) mu := by
    change AEStronglyMeasurable
      (fun omega ↦ ∑ i, xHat t omega i * b omega i) mu
    refine (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _hi ↦ (hFresh.xCoordinateMeasurable i).mul (hbMeas i))).congr ?_
    exact ae_of_all mu (fun omega ↦ by simp)
  have hUnpenMeas : AEStronglyMeasurable unpen mu := by
    exact aestronglyMeasurable_const.mul
      ((hFresh.yMeasurable.sub hDotMeas).pow 2)
  have hSizeSqMeas : AEStronglyMeasurable (fun omega ↦
      (concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega) ^ 2) mu := by
    change AEStronglyMeasurable
      (fun omega ↦ (unpen omega + 2 * penalty) ^ 2) mu
    exact (hUnpenMeas.add aestronglyMeasurable_const).pow 2
  refine hUpperInt.mono_nonneg hSizeSqMeas
    (ae_of_all mu (fun omega ↦ sq_nonneg _)) ?_
  refine ae_of_all mu (fun omega ↦ ?_)
  change (samplePenalizedDualCoordinateBound m penalty
      (xHat t omega) (yHat t omega) (b omega)) ^ 2 ≤
    2 * (unpen omega) ^ 2 + 8 * penalty ^ 2
  exact samplePenalizedDualCoordinateBound_sq_le m penalty
    (xHat t omega) (yHat t omega) (b omega)

/-- Every coordinate of the concrete dual oracle is integrable.  Its square is dominated by the
square of the explicit coordinate-bound process, and finite-measure `L² -> L¹` finishes. -/
theorem integrable_concreteTrajectoryDualOracle_coordinate_of_fresh
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit : Fin p → ℝ) (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega) (hPMeas : Measurable P)
    (hPrimalMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hDualMeas : ∀ t, Measurable[mCond (t + 1)] (fun omega ↦
      concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega))
    (hm : 0 < m) (hB : 0 ≤ B) (hpenalty : 0 ≤ penalty)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B) (t : ℕ)
    (hFresh : HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
      (eHat t) (xHat t) (yHat t) KX KY) (i : Fin m) :
    Integrable (fun omega ↦
      concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega i) mu := by
  let g : Omega → Fin m → ℝ := fun omega ↦
    concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega
  let size : Omega → ℝ := fun omega ↦
    concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega
  have hSizeSqInt : Integrable (fun omega ↦ (size omega) ^ 2) mu :=
    integrable_concreteTrajectoryDualSize_sq_of_fresh mCond C P bInit
      gamma penalty etaB etaW B KX KY eHat xHat yHat hMono hmCond hPMeas
      hPrimalMeas hDualMeas hm hB hInit hPFeas hCBall t hFresh
  have hGMeasAmbient : Measurable[mOmega] g :=
    (hDualMeas t).mono (hmCond (t + 1)) le_rfl
  have hCoordMeas : AEStronglyMeasurable (fun omega ↦ g omega i) mu :=
    (measurable_coordinate_of_finVector hGMeasAmbient i).aestronglyMeasurable
  have hCoordSqInt : Integrable (fun omega ↦ (g omega i) ^ 2) mu := by
    refine hSizeSqInt.mono_nonneg (hCoordMeas.pow 2)
      (ae_of_all mu (fun omega ↦ sq_nonneg _)) ?_
    refine ae_of_all mu (fun omega ↦ ?_)
    rw [← sq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (concreteTrajectoryDualSize_nonneg
      P bInit gamma penalty etaB etaW eHat xHat yHat hpenalty t omega)).2
    exact concreteTrajectoryDualOracle_hasCoordinateAbsBound P bInit gamma penalty
      etaB etaW eHat xHat yHat hm hpenalty t omega i
  have hMem : MemLp (fun omega ↦ g omega i) 2 mu :=
    (memLp_two_iff_integrable_sq hCoordMeas).2 hCoordSqInt
  exact hMem.integrable one_le_two

end NegDRO
