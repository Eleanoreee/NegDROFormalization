import NegDROFormalization.StochasticNegDROExplicitConstants

/-!
# Explicit `T⁻¹/²` stochastic NegDRO rates

This module specializes both concrete-oracle convergence bounds to the common step size
`1 / sqrt T`.  The resulting constants are transparent formulas.  The final square-root lemma
is explicitly an RMS statement; it does not identify RMS error with expected norm error.
-/

set_option autoImplicit false

open MeasureTheory
open scoped MeasureTheory

namespace NegDRO

/-- The common non-identifiability/bias term in both explicit rates. -/
noncomputable def explicitIdentificationBias
    {p : ℕ} (m : ℕ) (gamma lam : ℝ) (v : Fin p → ℝ) : ℝ :=
  (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam

/-- Transparent coefficient of `1 / sqrt T` in the unpenalized explicit rate. -/
noncomputable def explicitUnpenalizedRateConstant
    {p : ℕ} (m : ℕ) (bInit betaStar : Fin p → ℝ)
    (lam B KX KY : ℝ) : ℝ :=
  sqDist bInit betaStar / (2 * lam) +
  2 * Real.log (m : ℝ) / lam +
  explicitUnpenalizedDualGradSqBound m B KX KY / lam +
  explicitPrimalGradSqBound m B KX KY / (2 * lam)

/-- Transparent coefficient of `1 / sqrt T` in the penalized explicit rate.  Its dual moment
term depends on `penalty^2`, separately from the structural bias `2 * penalty / lam`. -/
noncomputable def explicitPenalizedRateConstant
    {p : ℕ} (m : ℕ) (penalty : ℝ) (bInit betaStar : Fin p → ℝ)
    (lam B KX KY : ℝ) : ℝ :=
  sqDist bInit betaStar / (2 * lam) +
  2 * Real.log (m : ℝ) / lam +
  explicitPenalizedDualGradSqBound m penalty B KX KY / lam +
  explicitPrimalGradSqBound m B KX KY / (2 * lam)

/-- For positive natural `T`, the chosen step size times `T` is exactly `sqrt T`. -/
theorem one_div_sqrt_mul_natCast (T : ℕ) (hT : 0 < T) :
    (1 / Real.sqrt (T : ℝ)) * (T : ℝ) = Real.sqrt (T : ℝ) := by
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTReal
  have hsquare : (Real.sqrt (T : ℝ)) ^ 2 = (T : ℝ) :=
    Real.sq_sqrt hTReal.le
  field_simp
  nlinarith

/-- Pure scalar specialization of two reciprocal-step terms and two linear-step terms. -/
theorem common_inv_sqrt_rate_identity
    (A B W CW CB : ℝ) (T : ℕ) (hT : 0 < T) :
    A / ((1 / Real.sqrt (T : ℝ)) * (T : ℝ)) + B +
        W / ((1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        (1 / Real.sqrt (T : ℝ)) * CW +
        (1 / Real.sqrt (T : ℝ)) * CB =
      B + (A + W + CW + CB) / Real.sqrt (T : ℝ) := by
  rw [one_div_sqrt_mul_natCast T hT]
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrt : Real.sqrt (T : ℝ) ≠ 0 := (Real.sqrt_pos.2 hTReal).ne'
  field_simp
  ring

/-- Exact algebraic normalization of the unpenalized concrete convergence right-hand side. -/
theorem explicit_unpenalized_rhs_eq_rate
    {p : ℕ} (m T : ℕ) (gamma lam B KX KY : ℝ)
    (v bInit betaStar : Fin p → ℝ) (hT : 0 < T) (hlam : 0 < lam) :
    sqDist bInit betaStar /
        (2 * lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
      explicitIdentificationBias m gamma lam v +
      2 * Real.log (m : ℝ) /
        (lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
      (1 / Real.sqrt (T : ℝ)) / lam *
        explicitUnpenalizedDualGradSqBound m B KX KY +
      (1 / Real.sqrt (T : ℝ)) * explicitPrimalGradSqBound m B KX KY /
        (2 * lam) =
      explicitIdentificationBias m gamma lam v +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTReal
  have hsquare : (Real.sqrt (T : ℝ)) ^ 2 = (T : ℝ) :=
    Real.sq_sqrt hTReal.le
  dsimp [explicitUnpenalizedRateConstant]
  rw [← hsquare]
  simp only [Real.sqrt_sq_eq_abs, abs_of_pos hsqrt]
  field_simp
  ring

/-- Exact algebraic normalization of the penalized concrete convergence right-hand side. -/
theorem explicit_penalized_rhs_eq_rate
    {p : ℕ} (m T : ℕ) (gamma lam penalty B KX KY : ℝ)
    (v bInit betaStar : Fin p → ℝ) (hT : 0 < T) (hlam : 0 < lam) :
    sqDist bInit betaStar /
        (2 * lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
      explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
      2 * Real.log (m : ℝ) /
        (lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
      (1 / Real.sqrt (T : ℝ)) / lam *
        explicitPenalizedDualGradSqBound m penalty B KX KY +
      (1 / Real.sqrt (T : ℝ)) * explicitPrimalGradSqBound m B KX KY /
        (2 * lam) =
      explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
        explicitPenalizedRateConstant m penalty bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTReal
  have hsquare : (Real.sqrt (T : ℝ)) ^ 2 = (T : ℝ) :=
    Real.sq_sqrt hTReal.le
  dsimp [explicitPenalizedRateConstant]
  rw [← hsquare]
  simp only [Real.sqrt_sq_eq_abs, abs_of_pos hsqrt]
  field_simp
  ring

/-- Unpenalized finite-time rate for the actual sample oracle at step size `1 / sqrt T`. -/
theorem stochasticNegDRO_concrete_unpenalized_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : ConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma 0
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam v +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  calc
    _ ≤ sqDist bInit betaStar /
          (2 * lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        explicitIdentificationBias m gamma lam v +
        2 * Real.log (m : ℝ) /
          (lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        (1 / Real.sqrt (T : ℝ)) / lam *
          explicitUnpenalizedDualGradSqBound m B KX KY +
        (1 / Real.sqrt (T : ℝ)) * explicitPrimalGradSqBound m B KX KY /
          (2 * lam) :=
      stochasticNegDRO_concrete_unpenalized_convergence
        mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0
        (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T
        eHat xHat yHat h
    _ = _ := explicit_unpenalized_rhs_eq_rate m T gamma lam B KX KY
      v bInit betaStar h.hT h.hlam

/-- Penalized finite-time rate for the actual sample oracle at step size `1 / sqrt T`. -/
theorem stochasticNegDRO_concrete_penalized_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : ConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
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
          Real.sqrt (T : ℝ) := by
  calc
    _ ≤ sqDist bInit betaStar /
          (2 * lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
        2 * Real.log (m : ℝ) /
          (lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        (1 / Real.sqrt (T : ℝ)) / lam *
          explicitPenalizedDualGradSqBound m penalty B KX KY +
        (1 / Real.sqrt (T : ℝ)) * explicitPrimalGradSqBound m B KX KY /
          (2 * lam) :=
      stochasticNegDRO_concrete_penalized_convergence
        mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0
        (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T
        eHat xHat yHat h
    _ = _ := explicit_penalized_rhs_eq_rate m T gamma lam penalty B KX KY
      v bInit betaStar h.hT h.hlam

/-- Unpenalized averaged-iterate rate for the actual sample oracle at step size `1 / sqrt T`. -/
theorem stochasticNegDRO_concrete_unpenalized_averaged_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : ConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit
        (1 / Real.sqrt (T : ℝ))
        (concreteTrajectoryPrimalOracle P bInit gamma 0
          (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      explicitIdentificationBias m gamma lam v +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  calc
    _ ≤ sqDist bInit betaStar /
          (2 * lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        explicitIdentificationBias m gamma lam v +
        2 * Real.log (m : ℝ) /
          (lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        (1 / Real.sqrt (T : ℝ)) / lam *
          explicitUnpenalizedDualGradSqBound m B KX KY +
        (1 / Real.sqrt (T : ℝ)) * explicitPrimalGradSqBound m B KX KY /
          (2 * lam) :=
      stochasticNegDRO_concrete_unpenalized_averaged_convergence
        mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0
        (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T
        eHat xHat yHat h
    _ = _ := explicit_unpenalized_rhs_eq_rate m T gamma lam B KX KY
      v bInit betaStar h.hT h.hlam

/-- Penalized averaged-iterate rate for the actual sample oracle at step size `1 / sqrt T`. -/
theorem stochasticNegDRO_concrete_penalized_averaged_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m)
    (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : ConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0
      (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ))
      B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit
        (1 / Real.sqrt (T : ℝ))
        (concreteTrajectoryPrimalOracle P bInit gamma penalty
          (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
        explicitPenalizedRateConstant m penalty bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) := by
  calc
    _ ≤ sqDist bInit betaStar /
          (2 * lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
        2 * Real.log (m : ℝ) /
          (lam * (1 / Real.sqrt (T : ℝ)) * (T : ℝ)) +
        (1 / Real.sqrt (T : ℝ)) / lam *
          explicitPenalizedDualGradSqBound m penalty B KX KY +
        (1 / Real.sqrt (T : ℝ)) * explicitPrimalGradSqBound m B KX KY /
          (2 * lam) :=
      stochasticNegDRO_concrete_penalized_averaged_convergence
        mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0
        (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) B KX KY T
        eHat xHat yHat h
    _ = _ := explicit_penalized_rhs_eq_rate m T gamma lam penalty B KX KY
      v bInit betaStar h.hT h.hlam

/-- Elementary subadditivity of the real square root on nonnegative inputs. -/
theorem sqrt_add_le_add_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  have hsqxy := Real.sq_sqrt hxy
  have hsqx := Real.sq_sqrt hx
  have hsqy := Real.sq_sqrt hy
  nlinarith [mul_nonneg hsx hsy]

/-- RMS consequence of a squared-error rate.  This is not an expected-norm statement. -/
theorem rms_le_sqrt_bias_add_quarter_rate
    (D bias C : ℝ) (T : ℕ)
    (hT : 0 < T) (hD : 0 ≤ D) (hbias : 0 ≤ bias) (hC : 0 ≤ C)
    (hUpper : D ≤ bias + C / Real.sqrt (T : ℝ)) :
    Real.sqrt D ≤ Real.sqrt bias +
      Real.sqrt C / Real.sqrt (Real.sqrt (T : ℝ)) := by
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrtT : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _
  have hRate : 0 ≤ C / Real.sqrt (T : ℝ) := div_nonneg hC hsqrtT
  calc
    Real.sqrt D ≤ Real.sqrt (bias + C / Real.sqrt (T : ℝ)) :=
      Real.sqrt_le_sqrt hUpper
    _ ≤ Real.sqrt bias + Real.sqrt (C / Real.sqrt (T : ℝ)) :=
      sqrt_add_le_add_sqrt bias (C / Real.sqrt (T : ℝ)) hbias hRate
    _ = Real.sqrt bias + Real.sqrt C / Real.sqrt (Real.sqrt (T : ℝ)) := by
      rw [Real.sqrt_div hC]

end NegDRO
