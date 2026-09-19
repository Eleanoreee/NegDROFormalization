import NegDROFormalization.EGTrajectoryRegret
import NegDROFormalization.ExpectedDualRegret
import NegDROFormalization.ExpectedPrimalRecursion
import NegDROFormalization.PredictableVectorPairing

/-!
# Expected regret of a random EG trajectory

This module applies the deterministic EG trajectory pointwise to a random gradient sequence,
then integrates its pathwise linearized-regret bound. It assumes coordinatewise predictability
of each current iterate; it does not construct a filtration or prove that predictability from
past gradients.

The indexing remains zero-based: Lean's `w_0` is the PDF's uniform `w_1`, and Lean rounds
`t = 0, ..., T - 1` correspond to PDF rounds `1, ..., T`.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- The deterministic EG construction applied separately at each sample point. -/
noncomputable def randomEGTrajectory
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (t : ℕ) (omega : Omega) : Fin m → ℝ :=
  egTrajectory (fun s => gHat s omega) eta t

/-- The sampled online linearized regret against deterministic comparator `u`. -/
noncomputable def randomEGLinearizedRegret
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (t : ℕ) (omega : Omega) : ℝ :=
  vectorDot (gHat t omega)
    (primalDisplacement u (randomEGTrajectory gHat eta t omega))

/-- The random trajectory starts at the deterministic uniform weight, pointwise. -/
@[simp] theorem randomEGTrajectory_zero
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ) (omega : Omega) :
    randomEGTrajectory gHat eta 0 omega = uniformWeight m := by
  simp [randomEGTrajectory]

/-- Pointwise successor recurrence for the random trajectory. -/
@[simp] theorem randomEGTrajectory_succ
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (t : ℕ) (omega : Omega) :
    randomEGTrajectory gHat eta (t + 1) omega =
      egUpdate (randomEGTrajectory gHat eta t omega) (gHat t omega) eta := by
  simp [randomEGTrajectory]

/-- Every sampled trajectory value is a strictly positive simplex vector. -/
theorem randomEGTrajectory_isPositiveSimplex
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (t : ℕ) (omega : Omega) :
    IsSimplex (randomEGTrajectory gHat eta t omega) ∧
      HasStrictlyPositiveCoordinates (randomEGTrajectory gHat eta t omega) := by
  simpa [randomEGTrajectory] using
    egTrajectory_isPositiveSimplex (fun s => gHat s omega) eta hm t

/-- Simplex-membership projection of the pointwise random-trajectory invariant. -/
theorem randomEGTrajectory_isSimplex
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (t : ℕ) (omega : Omega) :
    IsSimplex (randomEGTrajectory gHat eta t omega) :=
  (randomEGTrajectory_isPositiveSimplex gHat eta hm t omega).1

/-- Strict-positivity projection of the pointwise random-trajectory invariant. -/
theorem randomEGTrajectory_pos
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (t : ℕ) (omega : Omega) :
    HasStrictlyPositiveCoordinates (randomEGTrajectory gHat eta t omega) :=
  (randomEGTrajectory_isPositiveSimplex gHat eta hm t omega).2

/-- Predictability of the current iterate coordinates implies predictability of the
comparator displacement coordinates. The comparator is deterministic. -/
theorem randomEGTrajectory_displacement_aestronglyMeasurable
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m : ℕ} (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (t : ℕ)
    (hTrajectoryMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => randomEGTrajectory gHat eta t omega i) mu) :
    ∀ i, AEStronglyMeasurable[mCond]
      (fun omega => primalDisplacement u (randomEGTrajectory gHat eta t omega) i) mu := by
  intro i
  change AEStronglyMeasurable[mCond]
    (fun omega => u i - randomEGTrajectory gHat eta t omega i) mu
  have hConst :
      AEStronglyMeasurable[mCond] (fun _ : Omega => u i) mu :=
    aestronglyMeasurable_const
  refine (hConst.sub (hTrajectoryMeas i)).congr ?_
  exact Eventually.of_forall (fun _omega => rfl)

/-- Simplex membership bounds every sampled comparator displacement coordinate by `1`.
The comparator may be on the boundary of the simplex. -/
theorem randomEGTrajectory_displacement_norm_le_one
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (hm : 0 < m) (hu : IsSimplex u)
    (t : ℕ) (omega : Omega) (i : Fin m) :
    ‖primalDisplacement u (randomEGTrajectory gHat eta t omega) i‖ ≤ 1 := by
  simpa [Real.norm_eq_abs] using
    abs_simplex_displacement_le_one hu
      (randomEGTrajectory_isSimplex gHat eta hm t omega) i

/-- The sampled pairing is integrable at a fixed round. Its integrability is derived from
coordinatewise gradient integrability, assumed iterate predictability, and the simplex
displacement bound `1`. -/
theorem integrable_randomEGLinearizedRegret
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m : ℕ} (hmCond : mCond ≤ mOmega)
    (gHat : ℕ → Omega → Fin m → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (hm : 0 < m) (hu : IsSimplex u) (t : ℕ)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => randomEGTrajectory gHat eta t omega i) mu) :
    Integrable (randomEGLinearizedRegret gHat eta u t) mu := by
  apply integrable_vectorDot_of_coordinatewise_integrable_of_predictableBounded
    hmCond (fun omega => gHat t omega)
      (fun omega => primalDisplacement u (randomEGTrajectory gHat eta t omega))
      hgHatInt
      (randomEGTrajectory_displacement_aestronglyMeasurable
        (mCond := mCond) (mu := mu) gHat eta u t hTrajectoryMeas)
      1
  intro i
  exact Eventually.of_forall (fun omega =>
    randomEGTrajectory_displacement_norm_le_one gHat eta u hm hu t omega i)

/-- The deterministic cumulative EG theorem applied pointwise in the sample `omega`. The
coordinate-size bound `G t omega` is random; no deterministic pathwise replacement is made. -/
theorem randomEGTrajectory_cumulative_linearizedRegret
    {Omega : Type*} {m : ℕ}
    (gHat : ℕ → Omega → Fin m → ℝ)
    (G : ℕ → Omega → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (omega : Omega)
    (hG : ∀ t < T, 0 ≤ G t omega)
    (hg : ∀ t < T, HasCoordinateAbsBound (gHat t omega) (G t omega)) :
    ∑ t ∈ Finset.range T, randomEGLinearizedRegret gHat eta u t omega ≤
      Real.log (m : ℝ) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, (G t omega) ^ 2 := by
  simpa [randomEGLinearizedRegret, randomEGTrajectory, egLinearizedRegret] using
    egTrajectory_cumulative_linearizedRegret
      (fun t => gHat t omega) eta (fun t => G t omega) u T hm heta hu hG hg

/-- Exact expected cumulative sampled-linearized-regret bound. Iterate predictability remains
an explicit assumption; only the deterministic pathwise theorem and finite-sum integration are
used. -/
theorem expected_randomEGTrajectory_cumulative_linearizedRegret
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (gHat : ℕ → Omega → Fin m → ℝ)
    (G : ℕ → Omega → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (hG : ∀ t < T, ∀ omega, 0 ≤ G t omega)
    (hg : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHat t omega) (G t omega))
    (hgHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHat eta t omega i) mu)
    (hGSqInt : ∀ t < T, Integrable (fun omega => (G t omega) ^ 2) mu) :
    ∑ t ∈ Finset.range T,
        ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu ≤
      Real.log (m : ℝ) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, ∫ omega, (G t omega) ^ 2 ∂mu := by
  have hRegretInt : ∀ t < T,
      Integrable (randomEGLinearizedRegret gHat eta u t) mu := by
    intro t ht
    exact integrable_randomEGLinearizedRegret (hmCond t)
      gHat eta u hm hu t (hgHatInt t ht) (hTrajectoryMeas t ht)
  have hRegretSumInt :
      Integrable
        (fun omega => ∑ t ∈ Finset.range T,
          randomEGLinearizedRegret gHat eta u t omega) mu := by
    exact integrable_finsetSum (Finset.range T) (fun t ht =>
      hRegretInt t (Finset.mem_range.mp ht))
  have hGSqSumInt :
      Integrable (fun omega =>
        ∑ t ∈ Finset.range T, (G t omega) ^ 2) mu := by
    exact integrable_finsetSum (Finset.range T) (fun t ht =>
      hGSqInt t (Finset.mem_range.mp ht))
  have hRightInt : Integrable (fun omega =>
      Real.log (m : ℝ) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, (G t omega) ^ 2) mu :=
    (integrable_const (Real.log (m : ℝ) / eta)).add
      (hGSqSumInt.const_mul (eta / 2))
  have hIntegrated :
      (∫ omega, ∑ t ∈ Finset.range T,
          randomEGLinearizedRegret gHat eta u t omega ∂mu) ≤
        ∫ omega, (Real.log (m : ℝ) / eta +
          eta / 2 * ∑ t ∈ Finset.range T, (G t omega) ^ 2) ∂mu :=
    integral_mono_ae hRegretSumInt hRightInt
      (Eventually.of_forall (fun omega =>
        randomEGTrajectory_cumulative_linearizedRegret
          gHat G eta u T hm heta hu omega
          (fun t ht => hG t ht omega) (fun t ht => hg t ht omega)))
  calc
    ∑ t ∈ Finset.range T,
        ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu =
        ∫ omega, ∑ t ∈ Finset.range T,
          randomEGLinearizedRegret gHat eta u t omega ∂mu := by
      symm
      exact integral_finsetSum (Finset.range T) (fun t ht =>
        hRegretInt t (Finset.mem_range.mp ht))
    _ ≤ ∫ omega, (Real.log (m : ℝ) / eta +
          eta / 2 * ∑ t ∈ Finset.range T, (G t omega) ^ 2) ∂mu := hIntegrated
    _ = Real.log (m : ℝ) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, ∫ omega, (G t omega) ^ 2 ∂mu := by
      rw [integral_add (integrable_const _) (hGSqSumInt.const_mul (eta / 2))]
      rw [integral_const_mul]
      rw [integral_finsetSum (Finset.range T) (fun t ht =>
        hGSqInt t (Finset.mem_range.mp ht))]
      simp

/-- Ordinary per-round second-moment specialization of the exact expected bound. -/
theorem expected_randomEGTrajectory_cumulative_linearizedRegret_of_moment_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (gHat : ℕ → Omega → Fin m → ℝ)
    (G : ℕ → Omega → ℝ) (M : ℕ → ℝ) (eta : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (hG : ∀ t < T, ∀ omega, 0 ≤ G t omega)
    (hg : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHat t omega) (G t omega))
    (hgHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHat eta t omega i) mu)
    (hGSqInt : ∀ t < T, Integrable (fun omega => (G t omega) ^ 2) mu)
    (hMoment : ∀ t < T, (∫ omega, (G t omega) ^ 2 ∂mu) ≤ M t) :
    ∑ t ∈ Finset.range T,
        ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu ≤
      Real.log (m : ℝ) / eta + eta / 2 * ∑ t ∈ Finset.range T, M t := by
  have hExact := expected_randomEGTrajectory_cumulative_linearizedRegret
    mCond hmCond gHat G eta u T hm heta hu hG hg hgHatInt hTrajectoryMeas hGSqInt
  have hSumMoment :
      (∑ t ∈ Finset.range T, ∫ omega, (G t omega) ^ 2 ∂mu) ≤
        ∑ t ∈ Finset.range T, M t := by
    apply Finset.sum_le_sum
    intro t ht
    exact hMoment t (Finset.mem_range.mp ht)
  have hScaled := mul_le_mul_of_nonneg_left hSumMoment (by positivity : 0 ≤ eta / 2)
  linarith

/-- Conditional uniform second-moment specialization. `dualGradSqBound` already denotes the
squared coordinate-size bound and is therefore not squared again. -/
theorem expected_randomEGTrajectory_cumulative_linearizedRegret_of_condMoment_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (gHat : ℕ → Omega → Fin m → ℝ)
    (G : ℕ → Omega → ℝ) (eta dualGradSqBound : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (hG : ∀ t < T, ∀ omega, 0 ≤ G t omega)
    (hg : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHat t omega) (G t omega))
    (hgHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHat eta t omega i) mu)
    (hGSqInt : ∀ t < T, Integrable (fun omega => (G t omega) ^ 2) mu)
    (hCondMoment : ∀ t < T,
      mu[(fun omega => (G t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound) :
    ∑ t ∈ Finset.range T,
        ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu ≤
      Real.log (m : ℝ) / eta +
        eta * (T : ℝ) / 2 * dualGradSqBound := by
  have hMoment : ∀ t < T,
      (∫ omega, (G t omega) ^ 2 ∂mu) ≤ dualGradSqBound := by
    intro t ht
    exact integral_le_const_of_condExp_ae_le
      (hmCond t) (fun omega => (G t omega) ^ 2) dualGradSqBound
        (hGSqInt t ht) (hCondMoment t ht)
  have hOrdinary :=
    expected_randomEGTrajectory_cumulative_linearizedRegret_of_moment_le
      mCond hmCond gHat G (fun _ => dualGradSqBound) eta u T
      hm heta hu hG hg hgHatInt hTrajectoryMeas hGSqInt hMoment
  calc
    ∑ t ∈ Finset.range T,
        ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu ≤
      Real.log (m : ℝ) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, dualGradSqBound := hOrdinary
    _ = Real.log (m : ℝ) / eta +
        eta * (T : ℝ) / 2 * dualGradSqBound := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Average conditional-moment bound for a positive number of rounds. The round count is
coerced to `ℝ`; `dualGradSqBound` remains an already-squared quantity. -/
theorem expected_randomEGTrajectory_average_linearizedRegret_of_condMoment_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (gHat : ℕ → Omega → Fin m → ℝ)
    (G : ℕ → Omega → ℝ) (eta dualGradSqBound : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u) (hT : 0 < T)
    (hG : ∀ t < T, ∀ omega, 0 ≤ G t omega)
    (hg : ∀ t < T, ∀ omega,
      HasCoordinateAbsBound (gHat t omega) (G t omega))
    (hgHatInt : ∀ t < T, ∀ i,
      Integrable (fun omega => gHat t omega i) mu)
    (hTrajectoryMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => randomEGTrajectory gHat eta t omega i) mu)
    (hGSqInt : ∀ t < T, Integrable (fun omega => (G t omega) ^ 2) mu)
    (hCondMoment : ∀ t < T,
      mu[(fun omega => (G t omega) ^ 2) | mCond t] ≤ᵐ[mu]
        fun _ => dualGradSqBound) :
    (1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T,
          ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu ≤
      Real.log (m : ℝ) / (eta * (T : ℝ)) +
        eta / 2 * dualGradSqBound := by
  have hCumulative :=
    expected_randomEGTrajectory_cumulative_linearizedRegret_of_condMoment_le
      mCond hmCond gHat G eta dualGradSqBound u T hm heta hu
      hG hg hgHatInt hTrajectoryMeas hGSqInt hCondMoment
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hScaled := mul_le_mul_of_nonneg_left hCumulative
    (by positivity : 0 ≤ 1 / (T : ℝ))
  calc
    (1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T,
          ∫ omega, randomEGLinearizedRegret gHat eta u t omega ∂mu ≤
      (1 / (T : ℝ)) *
        (Real.log (m : ℝ) / eta +
          eta * (T : ℝ) / 2 * dualGradSqBound) := hScaled
    _ = Real.log (m : ℝ) / (eta * (T : ℝ)) +
        eta / 2 * dualGradSqBound := by
      field_simp

end NegDRO
