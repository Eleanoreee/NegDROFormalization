import NegDROFormalization.StochasticPrimalTrajectory
import NegDROFormalization.ExpectedEGTrajectoryRegret
import NegDROFormalization.UpdateMeasurability

/-!
# Predictability of the actual stochastic trajectories

With zero-based indexing, the pre-round information is `mCond t`, the round-`t` oracle is
measurable for `mCond (t + 1)`, and its update produces the next iterate. Thus both actual
iterates at time `t` are measurable for `mCond t` by induction.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- A map measurable for the current information remains measurable for the next, larger
information sigma-algebra. The codomain measurable space is unchanged. -/
theorem measurable_mono_cond_succ
    {Omega X : Type*} [MeasurableSpace X]
    (mCond : ℕ → MeasurableSpace Omega)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    {f : Omega → X} {t : ℕ} (hf : Measurable[mCond t] f) :
    Measurable[mCond (t + 1)] f :=
  hf.mono (hMono t) le_rfl

/-- The actual projected-primal trajectory is predictable. Oracle `gHat t` is required to be
measurable only for the next information sigma-algebra, not the pre-round one. -/
theorem randomPrimalTrajectory_measurable
    {Omega : Type*} {p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hPMeas : Measurable P)
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega)) :
    ∀ t, Measurable[mCond t]
      (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega) := by
  intro t
  induction t with
  | zero =>
      simpa using
        (measurable_const : Measurable[mCond 0]
          (fun _ : Omega => bInit))
  | succ t ih =>
      have hCurrent : Measurable[mCond (t + 1)]
          (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega) :=
        measurable_mono_cond_succ mCond hMono ih
      simpa only [randomPrimalTrajectory_succ] using
        measurable_projectedGradientStep_comp
          P etaB hPMeas hCurrent (hGMeas t)

/-- Coordinatewise a.e. strong predictability required by the stochastic primal modules,
derived rather than assumed. -/
theorem randomPrimalTrajectory_coordinate_aestronglyMeasurable
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hPMeas : Measurable P)
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega)) :
    ∀ t i, AEStronglyMeasurable[mCond t]
      (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega i) mu := by
  intro t i
  exact (measurable_coordinate_of_finVector
    (randomPrimalTrajectory_measurable
      mCond P bInit etaB gHat hMono hPMeas hGMeas t) i).aestronglyMeasurable
        (μ := mu)

/-- Predictability of the primal displacement from a deterministic comparator. -/
theorem randomPrimalTrajectory_displacement_predictable
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit betaStar : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hPMeas : Measurable P)
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega)) :
    ∀ t i, AEStronglyMeasurable[mCond t]
      (fun omega => primalDisplacement
        (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar i) mu := by
  intro t i
  have hCoordinate := measurable_coordinate_of_finVector
    (randomPrimalTrajectory_measurable
      mCond P bInit etaB gHat hMono hPMeas hGMeas t) i
  exact (hCoordinate.sub measurable_const).aestronglyMeasurable

/-- Ambient measurability of a primal iterate follows by enlarging the source sigma-algebra. -/
theorem randomPrimalTrajectory_measurable_ambient
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (hPMeas : Measurable P)
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega))
    (t : ℕ) :
    Measurable[mOmega]
      (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega) :=
  (randomPrimalTrajectory_measurable
    mCond P bInit etaB gHat hMono hPMeas hGMeas t).mono (hmCond t) le_rfl

/-- The actual random EG trajectory is predictable under next-information measurability of its
oracle. No simplex, positivity, step-size, or gradient-bound premise is used. -/
theorem randomEGTrajectory_measurable
    {Omega : Type*} {n : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (gHat : ℕ → Omega → Fin n → ℝ) (etaW : ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega)) :
    ∀ t, Measurable[mCond t]
      (fun omega => randomEGTrajectory gHat etaW t omega) := by
  intro t
  induction t with
  | zero =>
      simpa using
        (measurable_const : Measurable[mCond 0]
          (fun _ : Omega => uniformWeight n))
  | succ t ih =>
      have hCurrent : Measurable[mCond (t + 1)]
          (fun omega => randomEGTrajectory gHat etaW t omega) :=
        measurable_mono_cond_succ mCond hMono ih
      simpa only [randomEGTrajectory_succ] using
        measurable_egUpdate_comp etaW hCurrent (hGMeas t)

/-- Coordinatewise a.e. strong predictability required by the stochastic EG modules,
derived from oracle adaptedness. -/
theorem randomEGTrajectory_coordinate_aestronglyMeasurable
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {n : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (gHat : ℕ → Omega → Fin n → ℝ) (etaW : ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega)) :
    ∀ t i, AEStronglyMeasurable[mCond t]
      (fun omega => randomEGTrajectory gHat etaW t omega i) mu := by
  intro t i
  exact (measurable_coordinate_of_finVector
    (randomEGTrajectory_measurable mCond gHat etaW hMono hGMeas t) i).aestronglyMeasurable
      (μ := mu)

/-- Predictability of displacement from an arbitrary deterministic simplex comparator. The
proof uses only that the comparator is deterministic, so no simplex or positivity assumption is
actually necessary. -/
theorem randomEGTrajectory_displacement_predictable
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {n : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (gHat : ℕ → Omega → Fin n → ℝ) (etaW : ℝ)
    (u : Fin n → ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega)) :
    ∀ t i, AEStronglyMeasurable[mCond t]
      (fun omega => primalDisplacement u
        (randomEGTrajectory gHat etaW t omega) i) mu := by
  intro t i
  have hCoordinate := measurable_coordinate_of_finVector
    (randomEGTrajectory_measurable mCond gHat etaW hMono hGMeas t) i
  exact (measurable_const.sub hCoordinate).aestronglyMeasurable

/-- Ambient measurability of an EG iterate follows by enlarging the source sigma-algebra. -/
theorem randomEGTrajectory_measurable_ambient
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {n : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (gHat : ℕ → Omega → Fin n → ℝ) (etaW : ℝ)
    (hMono : ∀ t, mCond t ≤ mCond (t + 1))
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (hGMeas : ∀ t,
      Measurable[mCond (t + 1)] (fun omega => gHat t omega))
    (t : ℕ) :
    Measurable[mOmega] (fun omega => randomEGTrajectory gHat etaW t omega) :=
  (randomEGTrajectory_measurable mCond gHat etaW hMono hGMeas t).mono
    (hmCond t) le_rfl

end NegDRO
