import NegDROFormalization.ConcreteOracleMomentBounds
import NegDROFormalization.StochasticNegDROConvergencePredictable

/-!
# Concrete stochastic NegDRO trajectories and conditional moment realization

The existing convergence API treats oracle sequences as external inputs.  Here the concrete
sample oracles depend on the current primal and dual iterates, so we first define their joint
recursive state and then prove that its two components are exactly the existing random projected
and exponentiated-gradient trajectories driven by the resulting oracle sequences.

The conditional-moment interface below is stated in terms of raw selected-environment data
moments.  It never assumes a conditional bound on the final oracle norm under another name.
Conditional unbiasedness remains a separate input: this module does not yet derive the population
gradients from a kernel-level sampling law, and it assumes no independence between the primal and
dual oracle values.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Joint concrete primal/dual state.  The dual state starts at the project uniform weight, in
accordance with `randomEGTrajectory`; `penalty = 0` is the unpenalized algorithm. -/
noncomputable def concreteNegDROState
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) :
    ℕ → Omega → (Fin p → ℝ) × (Fin m → ℝ)
  | 0 => fun _ ↦ (bInit, uniformWeight m)
  | t + 1 => fun omega ↦
      let state := concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega
      let gB := samplePrimalOracle gamma (eHat t omega) (xHat t omega) (yHat t omega)
        state.1 state.2
      let gW := samplePenalizedDualOracle penalty (eHat t omega) (xHat t omega) (yHat t omega)
        state.1 state.2
      (projectedGradientStep P state.1 etaB gB, egUpdate state.2 gW etaW)

/-- Concrete primal sample-oracle process evaluated at the recursively generated current state. -/
noncomputable def concreteTrajectoryPrimalOracle
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : ℕ → Omega → Fin p → ℝ :=
  fun t omega ↦
    let state := concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega
    samplePrimalOracle gamma (eHat t omega) (xHat t omega) (yHat t omega) state.1 state.2

/-- Concrete penalized dual sample-oracle process evaluated at the recursively generated current
state.  At `penalty = 0` this reduces to the unpenalized one-hot oracle. -/
noncomputable def concreteTrajectoryDualOracle
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : ℕ → Omega → Fin m → ℝ :=
  fun t omega ↦
    let state := concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega
    samplePenalizedDualOracle penalty (eHat t omega) (xHat t omega) (yHat t omega)
      state.1 state.2

/-- Random coordinate-size process for the concrete penalized dual oracle. -/
noncomputable def concreteTrajectoryDualSize
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : ℕ → Omega → ℝ :=
  fun t omega ↦
    samplePenalizedDualCoordinateBound m penalty (xHat t omega) (yHat t omega)
      (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1

/-- The recursive concrete state is exactly the pair of existing random trajectories driven by
the concrete oracle processes. -/
theorem concreteNegDROState_eq_randomTrajectories
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) (t : ℕ) (omega : Omega) :
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1 =
        randomPrimalTrajectory P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
          t omega ∧
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2 =
        randomEGTrajectory
          (concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
          etaW t omega := by
  induction t with
  | zero =>
      simp [concreteNegDROState]
  | succ t ih =>
      constructor
      · rw [randomPrimalTrajectory_succ]
        simp only [concreteNegDROState]
        rw [← ih.1]
        rfl
      · rw [randomEGTrajectory_succ]
        simp only [concreteNegDROState]
        rw [← ih.2]
        rfl

/-- Primal component of the concrete-state/trajectory identification. -/
theorem concreteNegDROState_primal_eq_randomPrimalTrajectory
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) (t : ℕ) (omega : Omega) :
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1 =
      randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        t omega :=
  (concreteNegDROState_eq_randomTrajectories
    P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1

/-- Dual component of the concrete-state/trajectory identification. -/
theorem concreteNegDROState_dual_eq_randomEGTrajectory
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) (t : ℕ) (omega : Omega) :
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2 =
      randomEGTrajectory
        (concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        etaW t omega :=
  (concreteNegDROState_eq_randomTrajectories
    P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2

/-- Conditional expectation preserves a nonnegative two-term scalar linear combination of two
a.e. bounds.  This is a small API bridge used for the raw-moment calculations below. -/
theorem condExp_two_term_ae_le
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (f g A B : Omega → ℝ) (c d : ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfBound : mu[f | mCond] ≤ᵐ[mu] A)
    (hgBound : mu[g | mCond] ≤ᵐ[mu] B) :
    mu[(fun omega ↦ c * f omega + d * g omega) | mCond] ≤ᵐ[mu]
      fun omega ↦ c * A omega + d * B omega := by
  have hcf : Integrable (fun omega ↦ c * f omega) mu := hf.const_mul c
  have hdg : Integrable (fun omega ↦ d * g omega) mu := hg.const_mul d
  have hAdd := condExp_add hcf hdg mCond
  have hScaleF :
      mu[(fun omega ↦ c * f omega) | mCond] =ᵐ[mu]
        fun omega ↦ c * (mu[f | mCond]) omega := by
    have hcMeas : AEStronglyMeasurable[mCond] (fun _ : Omega ↦ c) mu :=
      aestronglyMeasurable_const
    change mu[((fun _ : Omega ↦ c) * f) | mCond] =ᵐ[mu]
      (fun _ : Omega ↦ c) * mu[f | mCond]
    exact condExp_mul_of_aestronglyMeasurable_left hcMeas hcf hf
  have hScaleG :
      mu[(fun omega ↦ d * g omega) | mCond] =ᵐ[mu]
        fun omega ↦ d * (mu[g | mCond]) omega := by
    have hdMeas : AEStronglyMeasurable[mCond] (fun _ : Omega ↦ d) mu :=
      aestronglyMeasurable_const
    change mu[((fun _ : Omega ↦ d) * g) | mCond] =ᵐ[mu]
      (fun _ : Omega ↦ d) * mu[g | mCond]
    exact condExp_mul_of_aestronglyMeasurable_left hdMeas hdg hg
  have hLinear :
      mu[(fun omega ↦ c * f omega + d * g omega) | mCond] =ᵐ[mu]
        fun omega ↦ c * (mu[f | mCond]) omega + d * (mu[g | mCond]) omega := by
    exact hAdd.trans (hScaleF.add hScaleG)
  filter_upwards [hLinear, hfBound, hgBound] with omega hlin hfomega hgomega
  rw [hlin]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hfomega hc)
    (mul_le_mul_of_nonneg_left hgomega hd)

/-- Raw selected-environment mixed magnitude used in the primal conditional-moment interface. -/
noncomputable def rawShiftedMixedMagnitude
    {Omega : Type*} {m p : ℕ} (gamma : ℝ)
    (e : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (w : Omega → Fin m → ℝ) : Omega → ℝ :=
  fun omega ↦
    (w omega (e omega) - negDROGammaCoefficient m gamma) ^ 2 *
      sqNorm (X omega) * (Y omega) ^ 2

/-- Raw selected-environment fourth-`X` magnitude used in the primal conditional-moment
interface. -/
noncomputable def rawShiftedXFourthMagnitude
    {Omega : Type*} {m p : ℕ} (gamma : ℝ)
    (e : Omega → Fin m) (X : Omega → Fin p → ℝ)
    (w : Omega → Fin m → ℝ) : Omega → ℝ :=
  fun omega ↦
    (w omega (e omega) - negDROGammaCoefficient m gamma) ^ 2 *
      (sqNorm (X omega)) ^ 2

/-- Conditional second-moment realization for the actual primal sample formula from two raw
selected-environment moment assumptions.  The raw bounds retain the shifted coefficient and the
explicit uniform factor `1/m`; neither hypothesis mentions the oracle norm. -/
theorem condExp_samplePrimalOracle_sqNorm_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (gamma B KX KY : ℝ)
    (e : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hB : 0 ≤ B)
    (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hw : ∀ omega, IsSimplex (w omega))
    (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hOracleInt : Integrable (fun omega ↦
      sqNorm (samplePrimalOracle gamma (e omega) (X omega) (Y omega) (b omega) (w omega))) mu)
    (hMixedInt : Integrable (rawShiftedMixedMagnitude gamma e X Y w) mu)
    (hXFourthInt : Integrable (rawShiftedXFourthMagnitude gamma e X w) mu)
    (hRawMixed :
      mu[rawShiftedMixedMagnitude gamma e X Y w | mCond] ≤ᵐ[mu]
        fun omega ↦ (1 / (m : ℝ)) * Real.sqrt (KY * KX) *
          ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2)
    (hRawXFourth :
      mu[rawShiftedXFourthMagnitude gamma e X w | mCond] ≤ᵐ[mu]
        fun omega ↦ (1 / (m : ℝ)) * KX *
          ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2) :
    mu[(fun omega ↦
      sqNorm (samplePrimalOracle gamma (e omega) (X omega) (Y omega) (b omega) (w omega))) |
        mCond] ≤ᵐ[mu]
      fun _ ↦ explicitPrimalGradSqBound m B KX KY := by
  let c : ℝ := 8 * (m : ℝ) ^ 2
  let d : ℝ := 8 * (m : ℝ) ^ 2 * B ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hUpperInt : Integrable (fun omega ↦
      c * rawShiftedMixedMagnitude gamma e X Y w omega +
        d * rawShiftedXFourthMagnitude gamma e X w omega) mu :=
    (hMixedInt.const_mul c).add (hXFourthInt.const_mul d)
  have hPointwise : ∀ omega,
      sqNorm (samplePrimalOracle gamma (e omega) (X omega) (Y omega) (b omega) (w omega)) ≤
        c * rawShiftedMixedMagnitude gamma e X Y w omega +
          d * rawShiftedXFourthMagnitude gamma e X w omega := by
    intro omega
    have horacle := samplePrimalOracle_sqNorm_le gamma (e omega) (X omega) (Y omega) B
      (b omega) (w omega) hB (hb omega)
    dsimp [c, d, rawShiftedMixedMagnitude, rawShiftedXFourthMagnitude]
    nlinarith
  have hMono := condExp_mono (m := mCond) hOracleInt hUpperInt
    (ae_of_all mu hPointwise)
  have hRawCombined := condExp_two_term_ae_le
    (rawShiftedMixedMagnitude gamma e X Y w)
    (rawShiftedXFourthMagnitude gamma e X w)
    (fun omega ↦ (1 / (m : ℝ)) * Real.sqrt (KY * KX) *
      ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2)
    (fun omega ↦ (1 / (m : ℝ)) * KX *
      ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2)
    c d hMixedInt hXFourthInt hc hd hRawMixed hRawXFourth
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  filter_upwards [hMono, hRawCombined] with omega hmono hraw
  calc
    (mu[(fun omega ↦
      sqNorm (samplePrimalOracle gamma (e omega) (X omega) (Y omega) (b omega) (w omega))) |
        mCond]) omega ≤
        (mu[(fun omega ↦
          c * rawShiftedMixedMagnitude gamma e X Y w omega +
            d * rawShiftedXFourthMagnitude gamma e X w omega) | mCond]) omega := hmono
    _ ≤ c * ((1 / (m : ℝ)) * Real.sqrt (KY * KX) *
          ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2) +
        d * ((1 / (m : ℝ)) * KX *
          ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2) := hraw
    _ ≤ explicitPrimalGradSqBound m B KX KY := by
      have hShift := shiftedCoefficient_sq_sum_le_one gamma (w omega) hm hgamma (hw omega)
      have hCommon : 0 ≤
          4 * (m : ℝ) * (2 * Real.sqrt (KY * KX) + 2 * B ^ 2 * KX) := by
        positivity
      have hScaled := mul_le_mul_of_nonneg_left hShift hCommon
      dsimp [c, d, explicitPrimalGradSqBound]
      field_simp
      nlinarith

/-- A raw conditional fourth-moment realization of the residual bound.  Both assumptions concern
the sampled data themselves; in particular, neither is an oracle-gradient moment assumption. -/
theorem condExp_residual_fourth_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (B KX KY : ℝ)
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ)
    (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hResidualInt : Integrable
      (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) mu)
    (hYFourthInt : Integrable (fun omega ↦ (Y omega) ^ 4) mu)
    (hXFourthInt : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hYFourth : mu[(fun omega ↦ (Y omega) ^ 4) | mCond] ≤ᵐ[mu] fun _ ↦ KY)
    (hXFourth : mu[(fun omega ↦ (sqNorm (X omega)) ^ 2) | mCond] ≤ᵐ[mu]
      fun _ ↦ KX) :
    mu[(fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) | mCond] ≤ᵐ[mu]
      fun _ ↦ 8 * KY + 8 * B ^ 4 * KX := by
  have hUpperInt : Integrable (fun omega ↦
      8 * (Y omega) ^ 4 + (8 * B ^ 4) * (sqNorm (X omega)) ^ 2) mu :=
    (hYFourthInt.const_mul 8).add (hXFourthInt.const_mul (8 * B ^ 4))
  have hMono := condExp_mono (m := mCond) hResidualInt hUpperInt
    (ae_of_all mu (fun omega ↦ by
      simpa only using
        residual_fourth_le_of_sqNorm_le (X omega) (b omega) (Y omega) B hB (hb omega)))
  have hRaw := condExp_two_term_ae_le
    (fun omega ↦ (Y omega) ^ 4)
    (fun omega ↦ (sqNorm (X omega)) ^ 2)
    (fun _ ↦ KY) (fun _ ↦ KX)
    8 (8 * B ^ 4) hYFourthInt hXFourthInt (by norm_num) (by positivity)
    hYFourth hXFourth
  exact hMono.trans hRaw

/-- Scaling a conditional upper bound by a nonnegative deterministic scalar. -/
theorem condExp_const_mul_ae_le
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (f A : Omega → ℝ) (c : ℝ)
    (hf : Integrable f mu) (hc : 0 ≤ c)
    (hBound : mu[f | mCond] ≤ᵐ[mu] A) :
    mu[(fun omega ↦ c * f omega) | mCond] ≤ᵐ[mu] fun omega ↦ c * A omega := by
  have hcf : Integrable (fun omega ↦ c * f omega) mu := hf.const_mul c
  have hcMeas : AEStronglyMeasurable[mCond] (fun _ : Omega ↦ c) mu :=
    aestronglyMeasurable_const
  have hScale :
      mu[(fun omega ↦ c * f omega) | mCond] =ᵐ[mu]
        fun omega ↦ c * (mu[f | mCond]) omega := by
    change mu[((fun _ : Omega ↦ c) * f) | mCond] =ᵐ[mu]
      (fun _ : Omega ↦ c) * mu[f | mCond]
    exact condExp_mul_of_aestronglyMeasurable_left hcMeas hcf hf
  filter_upwards [hScale, hBound] with omega hscale hbound
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hbound hc

/-- Conditional second moment of the unpenalized dual coordinate-bound scalar, derived from the
raw residual fourth-moment bound. -/
theorem condExp_sampleDualCoordinateBound_sq_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (B KX KY : ℝ)
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ)
    (hResidualInt : Integrable
      (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) mu)
    (hResidual :
      mu[(fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) | mCond] ≤ᵐ[mu]
        fun _ ↦ 8 * KY + 8 * B ^ 4 * KX) :
    mu[(fun omega ↦ (sampleDualCoordinateBound m (X omega) (Y omega) (b omega)) ^ 2) |
        mCond] ≤ᵐ[mu]
      fun _ ↦ explicitUnpenalizedDualGradSqBound m B KX KY := by
  have hScaled := condExp_const_mul_ae_le
    (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4)
    (fun _ ↦ 8 * KY + 8 * B ^ 4 * KX) ((m : ℝ) ^ 2)
    hResidualInt (by positivity) hResidual
  simpa only [sampleDualCoordinateBound_sq,
    explicitUnpenalizedDualGradSqBound] using hScaled

/-- Conditional second moment of the penalized coordinate-bound scalar.  The additive
`8 * penalty^2` comes from a genuine constant conditional expectation under a probability
measure, rather than from a hidden oracle-moment premise. -/
theorem condExp_samplePenalizedDualCoordinateBound_sq_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ} (penalty B KX KY : ℝ)
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ)
    (hmCond : mCond ≤ mOmega)
    (hUnpenInt : Integrable
      (fun omega ↦ (sampleDualCoordinateBound m (X omega) (Y omega) (b omega)) ^ 2) mu)
    (hPenInt : Integrable (fun omega ↦
      (samplePenalizedDualCoordinateBound m penalty (X omega) (Y omega) (b omega)) ^ 2) mu)
    (hUnpen :
      mu[(fun omega ↦ (sampleDualCoordinateBound m (X omega) (Y omega) (b omega)) ^ 2) |
          mCond] ≤ᵐ[mu]
        fun _ ↦ explicitUnpenalizedDualGradSqBound m B KX KY) :
    mu[(fun omega ↦
      (samplePenalizedDualCoordinateBound m penalty (X omega) (Y omega) (b omega)) ^ 2) |
        mCond] ≤ᵐ[mu]
      fun _ ↦ explicitPenalizedDualGradSqBound m penalty B KX KY := by
  have hUpperInt : Integrable (fun omega ↦
      2 * (sampleDualCoordinateBound m (X omega) (Y omega) (b omega)) ^ 2 +
        8 * penalty ^ 2) mu :=
    (hUnpenInt.const_mul 2).add (integrable_const (8 * penalty ^ 2))
  have hMono := condExp_mono (m := mCond) hPenInt hUpperInt
    (ae_of_all mu (fun omega ↦
      samplePenalizedDualCoordinateBound_sq_le m penalty (X omega) (Y omega) (b omega)))
  have hConst :
      mu[(fun _ : Omega ↦ (1 : ℝ)) | mCond] ≤ᵐ[mu] fun _ ↦ (1 : ℝ) := by
    exact ae_of_all mu (fun omega ↦ by
      rw [condExp_const (μ := mu) hmCond (1 : ℝ)])
  have hRaw := condExp_two_term_ae_le
    (fun omega ↦ (sampleDualCoordinateBound m (X omega) (Y omega) (b omega)) ^ 2)
    (fun _ : Omega ↦ (1 : ℝ))
    (fun _ ↦ explicitUnpenalizedDualGradSqBound m B KX KY)
    (fun _ ↦ (1 : ℝ))
    2 (8 * penalty ^ 2) hUnpenInt (integrable_const 1)
    (by norm_num) (by positivity) hUnpen hConst
  have hRaw' :
      mu[(fun omega ↦
        2 * (sampleDualCoordinateBound m (X omega) (Y omega) (b omega)) ^ 2 +
          8 * penalty ^ 2) | mCond] ≤ᵐ[mu]
        fun _ ↦ explicitPenalizedDualGradSqBound m penalty B KX KY := by
    have hRawS := hRaw
    simp only [mul_one] at hRawS
    filter_upwards [hRawS] with omega homega
    dsimp [explicitPenalizedDualGradSqBound,
      explicitUnpenalizedDualGradSqBound] at homega ⊢
    linarith
  exact hMono.trans hRaw'

/-- Raw per-round conditional data assumptions used by the explicit-constant wrappers.  This
predicate contains only selected-sample mixed/fourth moments and their integrability; it does not
contain either desired oracle-gradient moment bound. -/
def HasRawConcreteConditionalMoments
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (gamma B KX KY : ℝ)
    (e : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ) : Prop :=
  Integrable (rawShiftedMixedMagnitude gamma e X Y w) mu ∧
  Integrable (rawShiftedXFourthMagnitude gamma e X w) mu ∧
  mu[rawShiftedMixedMagnitude gamma e X Y w | mCond] ≤ᵐ[mu]
    (fun omega ↦ (1 / (m : ℝ)) * Real.sqrt (KY * KX) *
      ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2) ∧
  mu[rawShiftedXFourthMagnitude gamma e X w | mCond] ≤ᵐ[mu]
    (fun omega ↦ (1 / (m : ℝ)) * KX *
      ∑ j, (w omega j - negDROGammaCoefficient m gamma) ^ 2) ∧
  Integrable (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 4) mu ∧
  Integrable (fun omega ↦ (Y omega) ^ 4) mu ∧
  Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu ∧
  mu[(fun omega ↦ (Y omega) ^ 4) | mCond] ≤ᵐ[mu] (fun _ ↦ KY) ∧
  mu[(fun omega ↦ (sqNorm (X omega)) ^ 2) | mCond] ≤ᵐ[mu] (fun _ ↦ KX)

/-- The primal component of the concrete joint state remains in the feasible set. -/
theorem concreteNegDROState_primal_mem
    {Omega : Type*} {m p : ℕ}
    (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (t : ℕ) (omega : Omega) :
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1 ∈ C := by
  rw [concreteNegDROState_primal_eq_randomPrimalTrajectory]
  exact randomPrimalTrajectory_mem C P bInit etaB
    (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
    hInit hPFeas t omega

/-- The dual component of the concrete joint state remains in the simplex. -/
theorem concreteNegDROState_dual_isSimplex
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hm : 0 < m) (t : ℕ) (omega : Omega) :
    IsSimplex
      (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2 := by
  rw [concreteNegDROState_dual_eq_randomEGTrajectory]
  exact randomEGTrajectory_isSimplex
    (concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
    etaW hm t omega

/-- Raw per-round data moments imply the explicit primal oracle conditional moment along the
actual jointly recursive trajectory. -/
theorem concreteTrajectoryPrimal_condMoment_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (t : ℕ) (hm : 0 < m) (hgamma : 0 ≤ gamma) (hB : 0 ≤ B)
    (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hOracleInt : Integrable (fun omega ↦ sqNorm
      (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega)) mu)
    (hRaw : HasRawConcreteConditionalMoments (mCond := mCond) mu gamma B KX KY
      (eHat t) (xHat t) (yHat t)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).1)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).2)) :
    mu[(fun omega ↦ sqNorm
      (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega)) | mCond] ≤ᵐ[mu]
      fun _ ↦ explicitPrimalGradSqBound m B KX KY := by
  rcases hRaw with ⟨hMixedInt, hXFourthInt, hMixed, hXFourth,
    _hResidualInt, _hYFourthInt, _hDataXFourthInt, _hYFourth, _hDataXFourth⟩
  apply condExp_samplePrimalOracle_sqNorm_le_explicit gamma B KX KY
    (eHat t) (xHat t) (yHat t)
    (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega).1)
    (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega).2)
    hm hgamma hB hKX hKY
  · exact fun omega ↦ concreteNegDROState_dual_isSimplex
      P bInit gamma penalty etaB etaW eHat xHat yHat hm t omega
  · exact fun omega ↦ hCBall _
      (concreteNegDROState_primal_mem C P bInit gamma penalty etaB etaW
        eHat xHat yHat hInit hPFeas t omega)
  · exact hOracleInt
  · exact hMixedInt
  · exact hXFourthInt
  · exact hMixed
  · exact hXFourth

/-- Raw per-round data moments imply the explicit unpenalized dual-size conditional moment along
the actual trajectory. -/
theorem concreteTrajectoryDualSize_unpenalized_condMoment_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (t : ℕ) (hB : 0 ≤ B)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hRaw : HasRawConcreteConditionalMoments (mCond := mCond) mu gamma B KX KY
      (eHat t) (xHat t) (yHat t)
      (fun omega ↦ (concreteNegDROState P bInit gamma 0 etaB etaW
        eHat xHat yHat t omega).1)
      (fun omega ↦ (concreteNegDROState P bInit gamma 0 etaB etaW
        eHat xHat yHat t omega).2)) :
    mu[(fun omega ↦
      (concreteTrajectoryDualSize P bInit gamma 0 etaB etaW eHat xHat yHat t omega) ^ 2) |
        mCond] ≤ᵐ[mu]
      fun _ ↦ explicitUnpenalizedDualGradSqBound m B KX KY := by
  rcases hRaw with ⟨_hMixedInt, _hShiftedXFourthInt, _hMixed, _hShiftedXFourth,
    hResidualInt, hYFourthInt, hXFourthInt, hYFourth, hXFourth⟩
  let b : Omega → Fin p → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma 0 etaB etaW eHat xHat yHat t omega).1
  have hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2 := fun omega ↦ hCBall _
    (concreteNegDROState_primal_mem C P bInit gamma 0 etaB etaW
      eHat xHat yHat hInit hPFeas t omega)
  have hResidual := condExp_residual_fourth_le_explicit B KX KY
    (xHat t) (yHat t) b hB hb hResidualInt hYFourthInt hXFourthInt
    hYFourth hXFourth
  simpa only [concreteTrajectoryDualSize, samplePenalizedDualCoordinateBound,
    mul_zero, add_zero] using
    (condExp_sampleDualCoordinateBound_sq_le_explicit B KX KY
      (m := m) (xHat t) (yHat t) b hResidualInt hResidual)

/-- Raw per-round data moments imply the explicit penalized dual-size conditional moment along
the actual trajectory. -/
theorem concreteTrajectoryDualSize_penalized_condMoment_le_explicit
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW B KX KY : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (t : ℕ) (hmCond : mCond ≤ mOmega) (hB : 0 ≤ B)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hDualSizeSqInt : Integrable (fun omega ↦
      (concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega) ^ 2) mu)
    (hRaw : HasRawConcreteConditionalMoments (mCond := mCond) mu gamma B KX KY
      (eHat t) (xHat t) (yHat t)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).1)
      (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega).2)) :
    mu[(fun omega ↦
      (concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega) ^ 2) | mCond] ≤ᵐ[mu]
      fun _ ↦ explicitPenalizedDualGradSqBound m penalty B KX KY := by
  rcases hRaw with ⟨_hMixedInt, _hShiftedXFourthInt, _hMixed, _hShiftedXFourth,
    hResidualInt, hYFourthInt, hXFourthInt, hYFourth, hXFourth⟩
  let b : Omega → Fin p → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1
  have hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2 := fun omega ↦ hCBall _
    (concreteNegDROState_primal_mem C P bInit gamma penalty etaB etaW
      eHat xHat yHat hInit hPFeas t omega)
  have hResidual := condExp_residual_fourth_le_explicit B KX KY
    (xHat t) (yHat t) b hB hb hResidualInt hYFourthInt hXFourthInt
    hYFourth hXFourth
  have hUnpen := condExp_sampleDualCoordinateBound_sq_le_explicit B KX KY
    (m := m) (xHat t) (yHat t) b hResidualInt hResidual
  have hUnpenInt : Integrable (fun omega ↦
      (sampleDualCoordinateBound m (xHat t omega) (yHat t omega) (b omega)) ^ 2) mu := by
    simpa only [sampleDualCoordinateBound_sq] using
      hResidualInt.const_mul ((m : ℝ) ^ 2)
  exact condExp_samplePenalizedDualCoordinateBound_sq_le_explicit
    penalty B KX KY (xHat t) (yHat t) b hmCond hUnpenInt hDualSizeSqInt hUnpen

/-- The concrete penalized dual size is nonnegative under the algorithm's sign assumptions. -/
theorem concreteTrajectoryDualSize_nonneg
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hpenalty : 0 ≤ penalty) (t : ℕ) (omega : Omega) :
    0 ≤ concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega := by
  dsimp [concreteTrajectoryDualSize, samplePenalizedDualCoordinateBound,
    sampleDualCoordinateBound]
  positivity

/-- The concrete penalized sample oracle is coordinatewise bounded by its concrete scalar size. -/
theorem concreteTrajectoryDualOracle_hasCoordinateAbsBound
    {Omega : Type*} {m p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (gamma penalty etaB etaW : ℝ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hm : 0 < m) (hpenalty : 0 ≤ penalty) (t : ℕ) (omega : Omega) :
    HasCoordinateAbsBound
      (concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega)
      (concreteTrajectoryDualSize P bInit gamma penalty etaB etaW
        eHat xHat yHat t omega) := by
  exact samplePenalizedDualOracle_hasCoordinateAbsBound_explicit
    penalty (eHat t omega) (xHat t omega) (yHat t omega)
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).1
    (concreteNegDROState P bInit gamma penalty etaB etaW eHat xHat yHat t omega).2
    hpenalty
    (concreteNegDROState_dual_isSimplex P bInit gamma penalty etaB etaW
      eHat xHat yHat hm t omega)

/-- All non-moment and raw-data assumptions for the concrete unpenalized convergence wrappers.
Notably, this structure has no field asserting a conditional bound on an oracle norm or dual
coordinate-size square. -/
structure ConcreteUnpenalizedAssumptions
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
  hMono : ∀ t, mCond t ≤ mCond (t + 1)
  hmCond : ∀ t, mCond t ≤ mOmega
  hPMeas : Measurable P
  hPrimalMeas : ∀ t, Measurable[mCond (t + 1)]
    (fun omega ↦ concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW
      eHat xHat yHat t omega)
  hDualMeas : ∀ t, Measurable[mCond (t + 1)]
    (fun omega ↦ concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW
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
    concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat t omega i) mu
  hPrimalSqInt : ∀ t < T, Integrable (fun omega ↦ sqNorm
    (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat t omega)) mu
  hDualHatInt : ∀ t < T, ∀ i, Integrable (fun omega ↦
    concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW eHat xHat yHat t omega i) mu
  hDualSizeSqInt : ∀ t < T, Integrable (fun omega ↦
    (concreteTrajectoryDualSize P bInit gamma 0 etaB etaW eHat xHat yHat t omega) ^ 2) mu
  hRaw : ∀ t < T, HasRawConcreteConditionalMoments (mCond := mCond t) mu gamma B KX KY
    (eHat t) (xHat t) (yHat t)
    (fun omega ↦ (concreteNegDROState P bInit gamma 0 etaB etaW
      eHat xHat yHat t omega).1)
    (fun omega ↦ (concreteNegDROState P bInit gamma 0 etaB etaW
      eHat xHat yHat t omega).2)
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

/-- Actual-oracle unpenalized finite-time convergence with the explicit PDF moment constants. -/
theorem stochasticNegDRO_concrete_unpenalized_convergence
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
    (h : ConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW eHat xHat yHat
  let dualSize := concreteTrajectoryDualSize P bInit gamma 0 etaB etaW eHat xHat yHat
  have hPrimalMoment : ∀ t < T,
      mu[(fun omega ↦ sqNorm (gB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitPrimalGradSqBound m B KX KY := by
    intro t ht
    exact concreteTrajectoryPrimal_condMoment_le_explicit C P bInit gamma 0 etaB etaW
      B KX KY eHat xHat yHat t h.hm h.hgamma h.hB h.hKX h.hKY h.hInit
      h.hPFeas h.hCBall (h.hPrimalSqInt t ht) (h.hRaw t ht)
  have hDualMoment : ∀ t < T,
      mu[(fun omega ↦ (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitUnpenalizedDualGradSqBound m B KX KY := by
    intro t ht
    exact concreteTrajectoryDualSize_unpenalized_condMoment_le_explicit
      C P bInit gamma etaB etaW B KX KY eHat xHat yHat t h.hB h.hInit
      h.hPFeas h.hCBall (h.hRaw t ht)
  exact stochasticNegDRO_unpenalized_convergence_of_oracleAdapted
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 gB gW dualSize
    etaB etaW B (explicitPrimalGradSqBound m B KX KY)
    (explicitUnpenalizedDualGradSqBound m B KX KY) T h.hMono h.hmCond h.hPMeas
    h.hPrimalMeas h.hDualMeas h.hm h.hT h.hetaB h.hetaW h.hB h.hgamma h.hlam
    h.hInit h.hbetaStar h.hPFeas h.hPDist h.hCBall h.hw0 h.hSigma h.hcurvature
    h.hPrimalHatInt h.hPrimalSqInt h.hPrimalCondUnbiased hPrimalMoment
    (fun t _ht omega ↦ concreteTrajectoryDualSize_nonneg P bInit gamma 0 etaB etaW
      eHat xHat yHat (by norm_num) t omega)
    (fun t _ht omega ↦ concreteTrajectoryDualOracle_hasCoordinateAbsBound
      P bInit gamma 0 etaB etaW eHat xHat yHat h.hm (by norm_num) t omega)
    h.hDualHatInt h.hDualSizeSqInt hDualMoment h.hDualCondUnbiased

/-- Actual-oracle unpenalized averaged-iterate convergence with the explicit PDF constants. -/
theorem stochasticNegDRO_concrete_unpenalized_averaged_convergence
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
    (h : ConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma 0 etaB etaW eHat xHat yHat
  let dualSize := concreteTrajectoryDualSize P bInit gamma 0 etaB etaW eHat xHat yHat
  have hPrimalMoment : ∀ t < T,
      mu[(fun omega ↦ sqNorm (gB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitPrimalGradSqBound m B KX KY := by
    intro t ht
    exact concreteTrajectoryPrimal_condMoment_le_explicit C P bInit gamma 0 etaB etaW
      B KX KY eHat xHat yHat t h.hm h.hgamma h.hB h.hKX h.hKY h.hInit
      h.hPFeas h.hCBall (h.hPrimalSqInt t ht) (h.hRaw t ht)
  have hDualMoment : ∀ t < T,
      mu[(fun omega ↦ (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitUnpenalizedDualGradSqBound m B KX KY := by
    intro t ht
    exact concreteTrajectoryDualSize_unpenalized_condMoment_le_explicit
      C P bInit gamma etaB etaW B KX KY eHat xHat yHat t h.hB h.hInit
      h.hPFeas h.hCBall (h.hRaw t ht)
  exact stochasticNegDRO_unpenalized_averaged_convergence_of_oracleAdapted
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 gB gW dualSize
    etaB etaW B (explicitPrimalGradSqBound m B KX KY)
    (explicitUnpenalizedDualGradSqBound m B KX KY) T h.hMono h.hmCond h.hPMeas
    h.hPrimalMeas h.hDualMeas h.hm h.hT h.hetaB h.hetaW h.hB h.hgamma h.hlam
    h.hInit h.hbetaStar h.hPFeas h.hPDist h.hCBall h.hw0 h.hSigma h.hcurvature
    h.hPrimalHatInt h.hPrimalSqInt h.hPrimalCondUnbiased hPrimalMoment
    (fun t _ht omega ↦ concreteTrajectoryDualSize_nonneg P bInit gamma 0 etaB etaW
      eHat xHat yHat (by norm_num) t omega)
    (fun t _ht omega ↦ concreteTrajectoryDualOracle_hasCoordinateAbsBound
      P bInit gamma 0 etaB etaW eHat xHat yHat h.hm (by norm_num) t omega)
    h.hDualHatInt h.hDualSizeSqInt hDualMoment h.hDualCondUnbiased

/-- All non-moment and raw-data assumptions for the concrete penalized convergence wrappers.
The structural comparator penalty and the stochastic penalty contribution remain separate. -/
structure ConcretePenalizedAssumptions
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
  hpenalty : 0 ≤ penalty
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
  hRaw : ∀ t < T, HasRawConcreteConditionalMoments (mCond := mCond t) mu gamma B KX KY
    (eHat t) (xHat t) (yHat t)
    (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega).1)
    (fun omega ↦ (concreteNegDROState P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega).2)
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

/-- Actual-oracle penalized finite-time convergence with explicit PDF moment constants. -/
theorem stochasticNegDRO_concrete_penalized_convergence
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
    (h : ConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
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
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let dualSize := concreteTrajectoryDualSize P bInit gamma penalty etaB etaW eHat xHat yHat
  have hPrimalMoment : ∀ t < T,
      mu[(fun omega ↦ sqNorm (gB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitPrimalGradSqBound m B KX KY := by
    intro t ht
    exact concreteTrajectoryPrimal_condMoment_le_explicit C P bInit gamma penalty etaB etaW
      B KX KY eHat xHat yHat t h.hm h.hgamma h.hB h.hKX h.hKY h.hInit
      h.hPFeas h.hCBall (h.hPrimalSqInt t ht) (h.hRaw t ht)
  have hDualMoment : ∀ t < T,
      mu[(fun omega ↦ (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitPenalizedDualGradSqBound m penalty B KX KY := by
    intro t ht
    exact concreteTrajectoryDualSize_penalized_condMoment_le_explicit
      C P bInit gamma penalty etaB etaW B KX KY eHat xHat yHat t (h.hmCond t)
      h.hB h.hInit h.hPFeas h.hCBall (h.hDualSizeSqInt t ht) (h.hRaw t ht)
  exact stochasticNegDRO_penalized_convergence_of_oracleAdapted
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 gB gW dualSize
    etaB etaW B (explicitPrimalGradSqBound m B KX KY)
    (explicitPenalizedDualGradSqBound m penalty B KX KY) T h.hMono h.hmCond h.hPMeas
    h.hPrimalMeas h.hDualMeas h.hm h.hT h.hetaB h.hetaW h.hB h.hgamma h.hlam
    h.hpenalty h.hInit h.hbetaStar h.hPFeas h.hPDist h.hCBall h.hw0 h.hSigma
    h.hcurvature h.hPrimalHatInt h.hPrimalSqInt h.hPrimalCondUnbiased hPrimalMoment
    (fun t _ht omega ↦ concreteTrajectoryDualSize_nonneg P bInit gamma penalty etaB etaW
      eHat xHat yHat h.hpenalty t omega)
    (fun t _ht omega ↦ concreteTrajectoryDualOracle_hasCoordinateAbsBound
      P bInit gamma penalty etaB etaW eHat xHat yHat h.hm h.hpenalty t omega)
    h.hDualHatInt h.hDualSizeSqInt hDualMoment h.hDualCondUnbiased

/-- Actual-oracle penalized averaged-iterate convergence with explicit PDF constants. -/
theorem stochasticNegDRO_concrete_penalized_averaged_convergence
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
    (h : ConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW eHat xHat yHat
  let dualSize := concreteTrajectoryDualSize P bInit gamma penalty etaB etaW eHat xHat yHat
  have hPrimalMoment : ∀ t < T,
      mu[(fun omega ↦ sqNorm (gB t omega)) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitPrimalGradSqBound m B KX KY := by
    intro t ht
    exact concreteTrajectoryPrimal_condMoment_le_explicit C P bInit gamma penalty etaB etaW
      B KX KY eHat xHat yHat t h.hm h.hgamma h.hB h.hKX h.hKY h.hInit
      h.hPFeas h.hCBall (h.hPrimalSqInt t ht) (h.hRaw t ht)
  have hDualMoment : ∀ t < T,
      mu[(fun omega ↦ (dualSize t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ ↦ explicitPenalizedDualGradSqBound m penalty B KX KY := by
    intro t ht
    exact concreteTrajectoryDualSize_penalized_condMoment_le_explicit
      C P bInit gamma penalty etaB etaW B KX KY eHat xHat yHat t (h.hmCond t)
      h.hB h.hInit h.hPFeas h.hCBall (h.hDualSizeSqInt t ht) (h.hRaw t ht)
  exact stochasticNegDRO_penalized_averaged_convergence_of_oracleAdapted
    mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 gB gW dualSize
    etaB etaW B (explicitPrimalGradSqBound m B KX KY)
    (explicitPenalizedDualGradSqBound m penalty B KX KY) T h.hMono h.hmCond h.hPMeas
    h.hPrimalMeas h.hDualMeas h.hm h.hT h.hetaB h.hetaW h.hB h.hgamma h.hlam
    h.hpenalty h.hInit h.hbetaStar h.hPFeas h.hPDist h.hCBall h.hw0 h.hSigma
    h.hcurvature h.hPrimalHatInt h.hPrimalSqInt h.hPrimalCondUnbiased hPrimalMoment
    (fun t _ht omega ↦ concreteTrajectoryDualSize_nonneg P bInit gamma penalty etaB etaW
      eHat xHat yHat h.hpenalty t omega)
    (fun t _ht omega ↦ concreteTrajectoryDualOracle_hasCoordinateAbsBound
      P bInit gamma penalty etaB etaW eHat xHat yHat h.hm h.hpenalty t omega)
    h.hDualHatInt h.hDualSizeSqInt hDualMoment h.hDualCondUnbiased

end NegDRO
