import NegDROFormalization.StochasticNegDRORates

/-!
# Fresh finite-environment conditional moments

This module removes adaptive weights from the primitive conditional-moment interface.  Its raw
assumptions concern only the selected environment indicator and the current data `X,Y`.  The
weight-dependent bounds used by `HasRawConcreteConditionalMoments` are derived by finite
indicator decomposition and conditional-expectation pull-out for predictable weights.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Scalar indicator that the selected environment is `e`. -/
def selectedEnvironmentIndicator
    {Omega : Type*} {m : ℕ} (E : Omega → Fin m) (e : Fin m) : Omega → ℝ :=
  fun omega ↦ finCoordinateIndicator (E omega) e

/-- Exactly one finite-environment indicator is active. -/
theorem sum_selectedEnvironmentIndicator_eq_one
    {Omega : Type*} {m : ℕ} (E : Omega → Fin m) (omega : Omega) :
    ∑ e, selectedEnvironmentIndicator E e omega = 1 := by
  classical
  simp only [selectedEnvironmentIndicator, finCoordinateIndicator]
  rw [Finset.sum_eq_single (E omega)]
  · simp
  · intro e _he hne
    simp [hne]
  · simp

/-- Indicator decomposition of evaluation at the selected environment. -/
theorem selectedEnvironmentIndicator_sum_apply
    {Omega : Type*} {m : ℕ} (E : Omega → Fin m)
    (f : Fin m → ℝ) (omega : Omega) :
    f (E omega) = ∑ e, selectedEnvironmentIndicator E e omega * f e := by
  classical
  simp only [selectedEnvironmentIndicator, finCoordinateIndicator]
  rw [Finset.sum_eq_single (E omega)]
  · simp
  · intro e _he hne
    simp [hne]
  · simp

/-- Weighted selected-environment identity used before conditional expectation. -/
theorem weighted_selectedEnvironmentIndicator_identity
    {Omega : Type*} {m : ℕ} (E : Omega → Fin m)
    (w : Omega → Fin m → ℝ) (a : ℝ) (Z : Omega → ℝ) (omega : Omega) :
    (w omega (E omega) - a) ^ 2 * Z omega =
      ∑ e, (w omega e - a) ^ 2 *
        (selectedEnvironmentIndicator E e omega * Z omega) := by
  calc
    _ = (∑ e, selectedEnvironmentIndicator E e omega *
          (w omega e - a) ^ 2) * Z omega := by
      rw [← selectedEnvironmentIndicator_sum_apply E
        (fun e ↦ (w omega e - a) ^ 2) omega]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      ring

/-- Selected scalar term `1_{E=e} Z`. -/
def selectedEnvironmentTerm
    {Omega : Type*} {m : ℕ} (E : Omega → Fin m)
    (e : Fin m) (Z : Omega → ℝ) : Omega → ℝ :=
  fun omega ↦ selectedEnvironmentIndicator E e omega * Z omega

/-- Every scalar random variable is the finite sum of its selected-environment pieces. -/
theorem sum_selectedEnvironmentTerm
    {Omega : Type*} {m : ℕ} (E : Omega → Fin m)
    (Z : Omega → ℝ) (omega : Omega) :
    ∑ e, selectedEnvironmentTerm E e Z omega = Z omega := by
  simp only [selectedEnvironmentTerm, ← Finset.sum_mul]
  rw [sum_selectedEnvironmentIndicator_eq_one]
  simp

/-- A simplex coordinate shifted by a deterministic scalar is uniformly bounded. -/
theorem norm_sq_shifted_simplex_coordinate_le
    {m : ℕ} (w : Fin m → ℝ) (a : ℝ) (hw : IsSimplex w) (e : Fin m) :
    ‖(w e - a) ^ 2‖ ≤ (1 + |a|) ^ 2 := by
  have hwe := simplex_coordinate_bounds hw e
  have habswe : |w e| ≤ 1 := by
    rw [abs_of_nonneg hwe.1]
    exact hwe.2
  have hsub : |w e - a| ≤ 1 + |a| := by
    calc
      |w e - a| ≤ |w e| + |a| := abs_sub _ _
      _ ≤ 1 + |a| := add_le_add habswe (le_refl _)
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hsub 2

/-- Generic conditional pull-out and summation theorem.  It derives the adaptive weighted bound
from coordinatewise selected-environment bounds that do not mention `w`. -/
theorem condExp_weighted_selected_le
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m : ℕ} (E : Omega → Fin m) (Z : Omega → ℝ)
    (w : Omega → Fin m → ℝ) (a C : ℝ)
    (hmCond : mCond ≤ mOmega)
    (hwMeas : ∀ e, AEStronglyMeasurable[mCond] (fun omega ↦ w omega e) mu)
    (hwSimplex : ∀ omega, IsSimplex (w omega))
    (hSelectedInt : ∀ e, Integrable (selectedEnvironmentTerm E e Z) mu)
    (hSelectedCond : ∀ e,
      mu[selectedEnvironmentTerm E e Z | mCond] ≤ᵐ[mu] fun _ ↦ C) :
    Integrable (fun omega ↦ (w omega (E omega) - a) ^ 2 * Z omega) mu ∧
    mu[(fun omega ↦ (w omega (E omega) - a) ^ 2 * Z omega) | mCond] ≤ᵐ[mu]
      fun omega ↦ C * ∑ e, (w omega e - a) ^ 2 := by
  classical
  let coeff : Fin m → Omega → ℝ := fun e omega ↦ (w omega e - a) ^ 2
  let selected : Fin m → Omega → ℝ := fun e ↦ selectedEnvironmentTerm E e Z
  have hCoeffMeas : ∀ e, AEStronglyMeasurable[mCond] (coeff e) mu := by
    intro e
    exact ((hwMeas e).sub aestronglyMeasurable_const).pow 2
  have hCoeffMeasAmbient : ∀ e, AEStronglyMeasurable (coeff e) mu := by
    intro e
    exact (hCoeffMeas e).mono hmCond
  have hCoeffBound : ∀ e, ∀ᵐ omega ∂mu,
      ‖coeff e omega‖ ≤ (1 + |a|) ^ 2 := by
    intro e
    exact ae_of_all mu (fun omega ↦
      norm_sq_shifted_simplex_coordinate_le (w omega) a (hwSimplex omega) e)
  have hProductInt : ∀ e, Integrable (fun omega ↦ coeff e omega * selected e omega) mu := by
    intro e
    exact (hSelectedInt e).bdd_mul (hCoeffMeasAmbient e) (hCoeffBound e)
  have hWeightedEq :
      (fun omega ↦ (w omega (E omega) - a) ^ 2 * Z omega) =
        (fun omega ↦ ∑ e, coeff e omega * selected e omega) := by
    funext omega
    exact weighted_selectedEnvironmentIndicator_identity E w a Z omega
  have hWeightedInt : Integrable
      (fun omega ↦ (w omega (E omega) - a) ^ 2 * Z omega) mu := by
    rw [hWeightedEq]
    exact integrable_finsetSum Finset.univ (fun e _he ↦ hProductInt e)
  refine ⟨hWeightedInt, ?_⟩
  rw [hWeightedEq]
  have hCondSum := condExp_finsetSum
    (s := Finset.univ) (fun e _he ↦ hProductInt e) mCond
  have hInputEq :
      (∑ e, (fun omega ↦ coeff e omega * selected e omega)) =
        (fun omega ↦ ∑ e, coeff e omega * selected e omega) := by
    funext omega
    simp
  have hOutputEq :
      (∑ e, mu[(fun omega ↦ coeff e omega * selected e omega) | mCond]) =
        (fun omega ↦ ∑ e,
          (mu[(fun omega ↦ coeff e omega * selected e omega) | mCond]) omega) := by
    funext omega
    simp
  have hCondSum' :
      mu[(fun omega ↦ ∑ e, coeff e omega * selected e omega) | mCond] =ᵐ[mu]
        (fun omega ↦ ∑ e,
          (mu[(fun omega ↦ coeff e omega * selected e omega) | mCond]) omega) := by
    rw [← hInputEq, ← hOutputEq]
    exact hCondSum
  have hPull : ∀ e,
      mu[(fun omega ↦ coeff e omega * selected e omega) | mCond] =ᵐ[mu]
        fun omega ↦ coeff e omega * (mu[selected e | mCond]) omega := by
    intro e
    change mu[coeff e * selected e | mCond] =ᵐ[mu]
      coeff e * mu[selected e | mCond]
    exact condExp_mul_of_aestronglyMeasurable_left
      (hCoeffMeas e) (hProductInt e) (hSelectedInt e)
  filter_upwards [hCondSum', ae_all_iff.2 hPull, ae_all_iff.2 hSelectedCond]
    with omega hsum hpull hbound
  rw [hsum]
  calc
    (∑ e, (mu[fun omega ↦ coeff e omega * selected e omega | mCond]) omega) =
        ∑ e, coeff e omega * (mu[selected e | mCond]) omega := by
      apply Finset.sum_congr rfl
      intro e _he
      exact hpull e
    _ ≤ ∑ e, coeff e omega * C := by
      apply Finset.sum_le_sum
      intro e _he
      exact mul_le_mul_of_nonneg_left (hbound e) (sq_nonneg _)
    _ = C * ∑ e, (w omega e - a) ^ 2 := by
      dsimp [coeff]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring

/-- Summing per-environment selected bounds recovers the unselected conditional bound, including
the exact cancellation of the `1/m` normalization. -/
theorem condExp_unselected_le_of_selected
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m : ℕ} (E : Omega → Fin m) (Z : Omega → ℝ) (K : ℝ)
    (hm : 0 < m)
    (hSelectedInt : ∀ e, Integrable (selectedEnvironmentTerm E e Z) mu)
    (hSelectedCond : ∀ e,
      mu[selectedEnvironmentTerm E e Z | mCond] ≤ᵐ[mu]
        fun _ ↦ (1 / (m : ℝ)) * K) :
    Integrable Z mu ∧ mu[Z | mCond] ≤ᵐ[mu] fun _ ↦ K := by
  classical
  have hSumInt : Integrable (fun omega ↦ ∑ e, selectedEnvironmentTerm E e Z omega) mu :=
    integrable_finsetSum Finset.univ (fun e _he ↦ hSelectedInt e)
  have hFunctionEq : (fun omega ↦ ∑ e, selectedEnvironmentTerm E e Z omega) = Z := by
    funext omega
    exact sum_selectedEnvironmentTerm E Z omega
  have hZInt : Integrable Z mu := by simpa only [hFunctionEq] using hSumInt
  refine ⟨hZInt, ?_⟩
  rw [← hFunctionEq]
  have hCondSum := condExp_finsetSum
    (s := Finset.univ) (fun e _he ↦ hSelectedInt e) mCond
  have hInputEq :
      (∑ e, selectedEnvironmentTerm E e Z) =
        (fun omega ↦ ∑ e, selectedEnvironmentTerm E e Z omega) := by
    funext omega
    simp
  have hOutputEq :
      (∑ e, mu[selectedEnvironmentTerm E e Z | mCond]) =
        (fun omega ↦ ∑ e, (mu[selectedEnvironmentTerm E e Z | mCond]) omega) := by
    funext omega
    simp
  have hCondSum' :
      mu[(fun omega ↦ ∑ e, selectedEnvironmentTerm E e Z omega) | mCond] =ᵐ[mu]
        (fun omega ↦ ∑ e, (mu[selectedEnvironmentTerm E e Z | mCond]) omega) := by
    rw [← hInputEq, ← hOutputEq]
    exact hCondSum
  filter_upwards [hCondSum', ae_all_iff.2 hSelectedCond] with omega hsum hbound
  rw [hsum]
  calc
    (∑ e, (mu[selectedEnvironmentTerm E e Z | mCond]) omega) ≤
        ∑ _e : Fin m, (1 / (m : ℝ)) * K := by
      exact Finset.sum_le_sum (fun e _he ↦ hbound e)
    _ = K := by
      have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Weight-independent selected-environment raw data interface.  No field mentions a current
iterate, shifted weight, oracle, or final gradient-moment constant. -/
structure HasFreshFiniteEnvironmentRawMoments
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (KX KY : ℝ) : Prop where
  xCoordinateMeasurable : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu
  yMeasurable : AEStronglyMeasurable Y mu
  selectedMixedIntegrable : ∀ e, Integrable
    (selectedEnvironmentTerm E e (fun omega ↦ sqNorm (X omega) * (Y omega) ^ 2)) mu
  selectedXFourthIntegrable : ∀ e, Integrable
    (selectedEnvironmentTerm E e (fun omega ↦ (sqNorm (X omega)) ^ 2)) mu
  selectedYFourthIntegrable : ∀ e, Integrable
    (selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 4)) mu
  selectedMixedCond : ∀ e,
    mu[selectedEnvironmentTerm E e (fun omega ↦ sqNorm (X omega) * (Y omega) ^ 2) |
      mCond] ≤ᵐ[mu] fun _ ↦ (1 / (m : ℝ)) * Real.sqrt (KY * KX)
  selectedXFourthCond : ∀ e,
    mu[selectedEnvironmentTerm E e (fun omega ↦ (sqNorm (X omega)) ^ 2) |
      mCond] ≤ᵐ[mu] fun _ ↦ (1 / (m : ℝ)) * KX
  selectedYFourthCond : ∀ e,
    mu[selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 4) |
      mCond] ≤ᵐ[mu] fun _ ↦ (1 / (m : ℝ)) * KY

/-- The fresh selected-environment interface implies every conjunct of the older raw conditional
moment interface once `b,w` are predictable/bounded. -/
theorem HasFreshFiniteEnvironmentRawMoments.toHasRawConcreteConditionalMoments
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ)
    (gamma B KX KY : ℝ) (hm : 0 < m) (hB : 0 ≤ B)
    (hmCond : mCond ≤ mOmega)
    (hbMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ b omega i) mu)
    (hwMeas : ∀ e, AEStronglyMeasurable[mCond] (fun omega ↦ w omega e) mu)
    (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hw : ∀ omega, IsSimplex (w omega))
    (hFresh : HasFreshFiniteEnvironmentRawMoments (mCond := mCond) mu E X Y KX KY) :
    HasRawConcreteConditionalMoments (mCond := mCond) mu gamma B KX KY E X Y b w := by
  let mixed : Omega → ℝ := fun omega ↦ sqNorm (X omega) * (Y omega) ^ 2
  let xFourth : Omega → ℝ := fun omega ↦ (sqNorm (X omega)) ^ 2
  let yFourth : Omega → ℝ := fun omega ↦ (Y omega) ^ 4
  have hWeightedMixed := condExp_weighted_selected_le E mixed w
    (negDROGammaCoefficient m gamma) ((1 / (m : ℝ)) * Real.sqrt (KY * KX))
    hmCond hwMeas hw hFresh.selectedMixedIntegrable hFresh.selectedMixedCond
  have hWeightedX := condExp_weighted_selected_le E xFourth w
    (negDROGammaCoefficient m gamma) ((1 / (m : ℝ)) * KX)
    hmCond hwMeas hw hFresh.selectedXFourthIntegrable hFresh.selectedXFourthCond
  have hX := condExp_unselected_le_of_selected E xFourth KX hm
    hFresh.selectedXFourthIntegrable hFresh.selectedXFourthCond
  have hY := condExp_unselected_le_of_selected E yFourth KY hm
    hFresh.selectedYFourthIntegrable hFresh.selectedYFourthCond
  have hDotMeas : AEStronglyMeasurable
      (fun omega ↦ vectorDot (X omega) (b omega)) mu := by
    change AEStronglyMeasurable (fun omega ↦ ∑ i, X omega i * b omega i) mu
    refine (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _hi ↦ (hFresh.xCoordinateMeasurable i).mul (hbMeas i))).congr ?_
    exact ae_of_all mu (fun omega ↦ by simp)
  have hResidualMeas : AEStronglyMeasurable
      (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) mu :=
    (hFresh.yMeasurable.sub hDotMeas).pow 4
  have hUpperInt : Integrable (fun omega ↦
      8 * (Y omega) ^ 4 + 8 * B ^ 4 * (sqNorm (X omega)) ^ 2) mu :=
    (hY.1.const_mul 8).add (hX.1.const_mul (8 * B ^ 4))
  have hResidualInt : Integrable
      (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) mu := by
    refine hUpperInt.mono_nonneg hResidualMeas
      (ae_of_all mu (fun omega ↦ by positivity)) ?_
    exact ae_of_all mu (fun omega ↦
      residual_fourth_le_of_sqNorm_le (X omega) (b omega) (Y omega) B hB (hb omega))
  refine ⟨?_, ?_, ?_, ?_, hResidualInt, hY.1, hX.1, hY.2, hX.2⟩
  · refine hWeightedMixed.1.congr (ae_of_all mu (fun omega ↦ ?_))
    dsimp [rawShiftedMixedMagnitude, mixed]
    ring
  · refine hWeightedX.1.congr (ae_of_all mu (fun omega ↦ ?_))
    rfl
  · rw [show rawShiftedMixedMagnitude gamma E X Y w =
        (fun omega ↦ (w omega (E omega) - negDROGammaCoefficient m gamma) ^ 2 *
          mixed omega) by
      funext omega
      dsimp [rawShiftedMixedMagnitude, mixed]
      ring]
    simpa only [mul_assoc] using hWeightedMixed.2
  · rw [show rawShiftedXFourthMagnitude gamma E X w =
        (fun omega ↦ (w omega (E omega) - negDROGammaCoefficient m gamma) ^ 2 *
          xFourth omega) by rfl]
    exact hWeightedX.2

/-- Assumptions common to the fresh-moment unpenalized and penalized wrappers.  The only moment
field is `hFresh`, which is independent of both current iterates. -/
structure FreshConcreteCommonAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma lam penalty : ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
  hMono : ∀ t, mCond t ≤ mCond (t + 1)
  hmCond : ∀ t, mCond t ≤ mOmega
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
  hSigma : ∀ e, QuadNonneg (Sigma e)
  hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam
  hPrimalHatInt : ∀ t < T, ∀ i, Integrable (fun omega ↦
    concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega i) mu
  hPrimalSqInt : ∀ t < T, Integrable (fun omega ↦ sqNorm
    (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega)) mu
  hDualHatInt : ∀ t < T, ∀ i, Integrable (fun omega ↦
    concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega i) mu
  hDualSizeSqInt : ∀ t < T, Integrable (fun omega ↦
    (concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega) ^ 2) mu
  hFresh : ∀ t < T, HasFreshFiniteEnvironmentRawMoments (mCond := mCond t) mu
    (eHat t) (xHat t) (yHat t) KX KY

/-- Fresh-moment unpenalized assumptions. Conditional unbiasedness remains explicit in Stage 1. -/
structure FreshConcreteUnpenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
  common : FreshConcreteCommonAssumptions mu mCond C P bInit betaStar Sigma
    gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat
  hPrimalCondUnbiased : ∀ t < T, ∀ i,
    (fun omega ↦ stochasticExpandedPrimalCoefficient Sigma gamma v betaStar P bInit etaB
      (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
      (concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
      etaW t omega i) =ᵐ[mu]
    mu[(fun omega ↦ concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW
      eHat xHat yHat t omega i) | mCond t]
  hDualCondUnbiased : ∀ t < T, ∀ i,
    (fun omega ↦ expandedDualGradient Sigma sigmaYSq v
      (randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
        t omega) betaStar i) =ᵐ[mu]
    mu[(fun omega ↦ concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW
      eHat xHat yHat t omega i) | mCond t]

/-- Predictability and fresh selected moments construct the old unpenalized assumptions without
requesting their adaptive `hRaw` field. -/
theorem FreshConcreteUnpenalizedAssumptions.toConcreteUnpenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    ConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW eHat xHat yHat
  have hRaw : ∀ t < T, HasRawConcreteConditionalMoments (mCond := mCond t) mu
      gamma B KX KY (eHat t) (xHat t) (yHat t)
      (fun omega ↦ (concreteNegDROState P bInit gamma 0 etaB etaW
        eHat xHat yHat t omega).1)
      (fun omega ↦ (concreteNegDROState P bInit gamma 0 etaB etaW
        eHat xHat yHat t omega).2) := by
    intro t ht
    let b : Omega → Fin p → ℝ := fun omega ↦
      (concreteNegDROState P bInit gamma 0 etaB etaW eHat xHat yHat t omega).1
    let w : Omega → Fin m → ℝ := fun omega ↦
      (concreteNegDROState P bInit gamma 0 etaB etaW eHat xHat yHat t omega).2
    have hbMeasCond : ∀ i, AEStronglyMeasurable[mCond t]
        (fun omega ↦ b omega i) mu := by
      intro i
      have hTrajectory := randomPrimalTrajectory_coordinate_aestronglyMeasurable
        (mu := mu) mCond P bInit etaB gB h.common.hMono h.common.hPMeas
        h.common.hPrimalMeas t i
      refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
      dsimp [b, gB]
      rw [concreteNegDROState_primal_eq_randomPrimalTrajectory]
    have hbMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ b omega i) mu :=
      fun i ↦ (hbMeasCond i).mono (h.common.hmCond t)
    have hwMeas : ∀ e, AEStronglyMeasurable[mCond t]
        (fun omega ↦ w omega e) mu := by
      intro e
      have hTrajectory := randomEGTrajectory_coordinate_aestronglyMeasurable
        (mu := mu) mCond gW etaW h.common.hMono h.common.hDualMeas t e
      refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
      dsimp [w, gW]
      rw [concreteNegDROState_dual_eq_randomEGTrajectory]
    have hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2 := fun omega ↦ h.common.hCBall _
      (concreteNegDROState_primal_mem C P bInit gamma 0 etaB etaW eHat xHat yHat
        h.common.hInit h.common.hPFeas t omega)
    have hw : ∀ omega, IsSimplex (w omega) := fun omega ↦
      concreteNegDROState_dual_isSimplex P bInit gamma 0 etaB etaW eHat xHat yHat
        h.common.hm t omega
    exact HasFreshFiniteEnvironmentRawMoments.toHasRawConcreteConditionalMoments
      (eHat t) (xHat t) (yHat t) b w gamma B KX KY h.common.hm h.common.hB
      (h.common.hmCond t) hbMeas hwMeas hb hw (h.common.hFresh t ht)
  exact {
    hMono := h.common.hMono
    hmCond := h.common.hmCond
    hPMeas := h.common.hPMeas
    hPrimalMeas := h.common.hPrimalMeas
    hDualMeas := h.common.hDualMeas
    hm := h.common.hm
    hT := h.common.hT
    hetaB := h.common.hetaB
    hetaW := h.common.hetaW
    hB := h.common.hB
    hKX := h.common.hKX
    hKY := h.common.hKY
    hgamma := h.common.hgamma
    hlam := h.common.hlam
    hInit := h.common.hInit
    hbetaStar := h.common.hbetaStar
    hPFeas := h.common.hPFeas
    hPDist := h.common.hPDist
    hCBall := h.common.hCBall
    hw0 := h.common.hw0
    hSigma := h.common.hSigma
    hcurvature := h.common.hcurvature
    hPrimalHatInt := h.common.hPrimalHatInt
    hPrimalSqInt := h.common.hPrimalSqInt
    hDualHatInt := h.common.hDualHatInt
    hDualSizeSqInt := h.common.hDualSizeSqInt
    hRaw := hRaw
    hPrimalCondUnbiased := h.hPrimalCondUnbiased
    hDualCondUnbiased := h.hDualCondUnbiased }

/-- Unpenalized finite-time convergence from weight-independent selected-environment moments. -/
theorem stochasticNegDRO_fresh_unpenalized_convergence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) :=
  stochasticNegDRO_concrete_unpenalized_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 etaB etaW B KX KY T
    eHat xHat yHat (h.toConcreteUnpenalizedAssumptions
      mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 etaB etaW B KX KY T
      eHat xHat yHat)

/-- Unpenalized inverse-square-root rate from weight-independent selected moments. -/
theorem stochasticNegDRO_fresh_unpenalized_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma 0
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam v +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) :=
  stochasticNegDRO_concrete_unpenalized_invSqrt_rate
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 B KX KY T eHat xHat yHat
    (h.toConcreteUnpenalizedAssumptions mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat)

/-- Fresh-moment penalized assumptions. Conditional unbiasedness remains explicit in Stage 1. -/
structure FreshConcretePenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
  common : FreshConcreteCommonAssumptions mu mCond C P bInit betaStar Sigma
    gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat
  hpenalty : 0 ≤ penalty
  hPrimalCondUnbiased : ∀ t < T, ∀ i,
    (fun omega ↦ stochasticExpandedPenalizedPrimalCoefficient Sigma gamma v betaStar
      P bInit etaB
      (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
      (concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
      etaW penalty t omega i) =ᵐ[mu]
    mu[(fun omega ↦ concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega i) | mCond t]
  hDualCondUnbiased : ∀ t < T, ∀ i,
    (fun omega ↦ expandedPenalizedDualGradient Sigma sigmaYSq v
      (randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        t omega) betaStar
      (randomEGTrajectory
        (concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        etaW t omega) penalty i) =ᵐ[mu]
    mu[(fun omega ↦ concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega i) | mCond t]

/-- Predictability and fresh selected moments construct the old penalized assumptions without
requesting their adaptive `hRaw` field. -/
theorem FreshConcretePenalizedAssumptions.toConcretePenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat) :
    ConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  have hRaw : ∀ t < T, HasRawConcreteConditionalMoments (mCond := mCond t) mu
      gamma B KX KY (eHat t) (xHat t) (yHat t)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).1)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).2) := by
    intro t ht
    let b : Omega → Fin p → ℝ := fun omega ↦
      (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1
    let w : Omega → Fin m → ℝ := fun omega ↦
      (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2
    have hbMeasCond : ∀ i, AEStronglyMeasurable[mCond t]
        (fun omega ↦ b omega i) mu := by
      intro i
      have hTrajectory := randomPrimalTrajectory_coordinate_aestronglyMeasurable
        (mu := mu) mCond P bInit etaB gB h.common.hMono h.common.hPMeas
        h.common.hPrimalMeas t i
      refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
      dsimp [b, gB]
      rw [concreteNegDROState_primal_eq_randomPrimalTrajectory]
    have hbMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ b omega i) mu :=
      fun i ↦ (hbMeasCond i).mono (h.common.hmCond t)
    have hwMeas : ∀ e, AEStronglyMeasurable[mCond t]
        (fun omega ↦ w omega e) mu := by
      intro e
      have hTrajectory := randomEGTrajectory_coordinate_aestronglyMeasurable
        (mu := mu) mCond gW etaW h.common.hMono h.common.hDualMeas t e
      refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
      dsimp [w, gW]
      rw [concreteNegDROState_dual_eq_randomEGTrajectory]
    have hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2 := fun omega ↦ h.common.hCBall _
      (concreteNegDROState_primal_mem C P bInit gamma penalty etaB etaW eHat xHat yHat
        h.common.hInit h.common.hPFeas t omega)
    have hw : ∀ omega, IsSimplex (w omega) := fun omega ↦
      concreteNegDROState_dual_isSimplex P bInit gamma penalty etaB etaW eHat xHat yHat
        h.common.hm t omega
    exact HasFreshFiniteEnvironmentRawMoments.toHasRawConcreteConditionalMoments
      (eHat t) (xHat t) (yHat t) b w gamma B KX KY h.common.hm h.common.hB
      (h.common.hmCond t) hbMeas hwMeas hb hw (h.common.hFresh t ht)
  exact {
    hMono := h.common.hMono
    hmCond := h.common.hmCond
    hPMeas := h.common.hPMeas
    hPrimalMeas := h.common.hPrimalMeas
    hDualMeas := h.common.hDualMeas
    hm := h.common.hm
    hT := h.common.hT
    hetaB := h.common.hetaB
    hetaW := h.common.hetaW
    hB := h.common.hB
    hKX := h.common.hKX
    hKY := h.common.hKY
    hgamma := h.common.hgamma
    hlam := h.common.hlam
    hpenalty := h.hpenalty
    hInit := h.common.hInit
    hbetaStar := h.common.hbetaStar
    hPFeas := h.common.hPFeas
    hPDist := h.common.hPDist
    hCBall := h.common.hCBall
    hw0 := h.common.hw0
    hSigma := h.common.hSigma
    hcurvature := h.common.hcurvature
    hPrimalHatInt := h.common.hPrimalHatInt
    hPrimalSqInt := h.common.hPrimalSqInt
    hDualHatInt := h.common.hDualHatInt
    hDualSizeSqInt := h.common.hDualSizeSqInt
    hRaw := hRaw
    hPrimalCondUnbiased := h.hPrimalCondUnbiased
    hDualCondUnbiased := h.hDualCondUnbiased }

/-- Penalized finite-time convergence from weight-independent selected-environment moments. -/
theorem stochasticNegDRO_fresh_penalized_convergence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) :=
  stochasticNegDRO_concrete_penalized_convergence
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
    eHat xHat yHat (h.toConcretePenalizedAssumptions
      mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
      eHat xHat yHat)

/-- Penalized inverse-square-root rate from weight-independent selected moments. -/
theorem stochasticNegDRO_fresh_penalized_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma penalty
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
        explicitPenalizedRateConstant m penalty bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) :=
  stochasticNegDRO_concrete_penalized_invSqrt_rate
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 B KX KY T
    eHat xHat yHat
    (h.toConcretePenalizedAssumptions mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)

end NegDRO
