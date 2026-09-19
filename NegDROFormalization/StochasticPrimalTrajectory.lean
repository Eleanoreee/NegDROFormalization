import NegDROFormalization.ExpectedPrimalRecursion
import NegDROFormalization.PrimalTrajectory

/-!
# Expected recursion for a random projected primal trajectory

This module applies the deterministic projected-primal trajectory pointwise to a stochastic
gradient sequence and instantiates the existing one-round expected recursion. Predictability
of the current iterates remains explicit: it is not derived from measurability of the stochastic
gradients or of the projection map.

Lean round `t` relates `b_t` and `b_(t+1)`. Later, the population coefficient will be chosen so
that its pairing with `b_t - betaStar` is the already-formalized fixed-witness/current-weight
directional expression. No independence between primal and dual stochastic gradients is needed;
the relevant current iterates need only be measurable with respect to the conditioning
sigma-algebra.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- The deterministic projected-primal construction applied separately at each sample point. -/
noncomputable def randomPrimalTrajectory
    {Omega : Type*} {p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (t : ℕ) (omega : Omega) : Fin p → ℝ :=
  primalTrajectory P bInit etaB (fun s => gHat s omega) t

/-- Expected squared distance of the random primal trajectory from `betaStar`. -/
noncomputable def expectedPrimalTrajectoryDistSq
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (betaStar : Fin p → ℝ) (t : ℕ) : ℝ :=
  ∫ omega, sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar ∂mu

/-- Expected population direction pairing along the random primal trajectory. -/
noncomputable def expectedPrimalTrajectoryDirection
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat F : ℕ → Omega → Fin p → ℝ)
    (betaStar : Fin p → ℝ) (t : ℕ) : ℝ :=
  ∫ omega, vectorDot (F t omega)
    (primalDisplacement (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar) ∂mu

/-- The random primal trajectory starts at the deterministic initial point, samplewise. -/
@[simp] theorem randomPrimalTrajectory_zero
    {Omega : Type*} {p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ) (omega : Omega) :
    randomPrimalTrajectory P bInit etaB gHat 0 omega = bInit := by
  simp [randomPrimalTrajectory]

/-- Pointwise successor recurrence for the random projected trajectory. -/
@[simp] theorem randomPrimalTrajectory_succ
    {Omega : Type*} {p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (t : ℕ) (omega : Omega) :
    randomPrimalTrajectory P bInit etaB gHat (t + 1) omega =
      projectedGradientStep P
        (randomPrimalTrajectory P bInit etaB gHat t omega) etaB (gHat t omega) := by
  simp [randomPrimalTrajectory]

/-- Every samplewise random trajectory iterate is feasible. The base case uses `hInit`; every
successor uses only `MapsIntoFeasibleSet C P`. -/
theorem randomPrimalTrajectory_mem
    {Omega : Type*} {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (t : ℕ) (omega : Omega) :
    randomPrimalTrajectory P bInit etaB gHat t omega ∈ C := by
  simpa [randomPrimalTrajectory] using
    primalTrajectory_mem C P bInit etaB (fun s => gHat s omega)
      hInit hPFeas t

/-- Each coordinate square is at most the explicit finite sum of all coordinate squares. -/
theorem coordinate_sq_le_sqNorm
    {p : ℕ} (x : Fin p → ℝ) (i : Fin p) :
    (x i) ^ 2 ≤ sqNorm x := by
  simp only [sqNorm]
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (x j)) (Finset.mem_univ i)

/-- A bounded feasible domain yields the coordinate displacement bound `2 * B` for every
random trajectory iterate. This is derived from feasibility and the two coordinate squared-norm
bounds; it is not an independent trajectory hypothesis. -/
theorem abs_randomPrimalTrajectory_displacement_le_two_mul
    {Omega : Type*} {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit betaStar : Fin p → ℝ)
    (etaB B : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hB : 0 ≤ B) (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (t : ℕ) (omega : Omega) (i : Fin p) :
    |primalDisplacement
        (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar i| ≤ 2 * B := by
  have hTrajectoryMem :
      randomPrimalTrajectory P bInit etaB gHat t omega ∈ C :=
    randomPrimalTrajectory_mem C P bInit etaB gHat hInit hPFeas t omega
  have hTrajectoryNorm :
      sqNorm (randomPrimalTrajectory P bInit etaB gHat t omega) ≤ B ^ 2 :=
    hCBall _ hTrajectoryMem
  have hbetaNorm : sqNorm betaStar ≤ B ^ 2 :=
    hCBall betaStar hbetaStar
  have hTrajectoryCoordSq :
      (randomPrimalTrajectory P bInit etaB gHat t omega i) ^ 2 ≤ B ^ 2 :=
    (coordinate_sq_le_sqNorm
      (randomPrimalTrajectory P bInit etaB gHat t omega) i).trans hTrajectoryNorm
  have hbetaCoordSq : (betaStar i) ^ 2 ≤ B ^ 2 :=
    (coordinate_sq_le_sqNorm betaStar i).trans hbetaNorm
  have hTrajectoryCoord :
      |randomPrimalTrajectory P bInit etaB gHat t omega i| ≤ B :=
    abs_le_of_sq_le_sq hTrajectoryCoordSq hB
  have hbetaCoord : |betaStar i| ≤ B :=
    abs_le_of_sq_le_sq hbetaCoordSq hB
  rw [primalDisplacement]
  calc
    |randomPrimalTrajectory P bInit etaB gHat t omega i - betaStar i| ≤
        |randomPrimalTrajectory P bInit etaB gHat t omega i| + |betaStar i| :=
      abs_sub _ _
    _ ≤ 2 * B := by linarith

/-- Assumed predictability of the trajectory coordinates implies predictability of the
displacement from deterministic `betaStar`. -/
theorem randomPrimalTrajectory_displacement_aestronglyMeasurable
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (P : (Fin p → ℝ) → Fin p → ℝ) (bInit betaStar : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ) (t : ℕ)
    (hTrajectoryMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega i) mu) :
    ∀ i, AEStronglyMeasurable[mCond]
      (fun omega => primalDisplacement
        (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar i) mu := by
  intro i
  change AEStronglyMeasurable[mCond]
    (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega i - betaStar i) mu
  have hConst : AEStronglyMeasurable[mCond] (fun _ : Omega => betaStar i) mu :=
    aestronglyMeasurable_const
  refine ((hTrajectoryMeas i).sub hConst).congr ?_
  exact Eventually.of_forall (fun _omega => rfl)

/-- Under a probability measure, predictability of the coordinates and the bounded feasible
domain imply integrability of the trajectory's explicit squared distance. -/
theorem integrable_randomPrimalTrajectory_sqDist
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {p : ℕ} (hmCond : mCond ≤ mOmega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (etaB B : ℝ)
    (gHat : ℕ → Omega → Fin p → ℝ)
    (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B) (t : ℕ)
    (hTrajectoryMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => randomPrimalTrajectory P bInit etaB gHat t omega i) mu) :
    Integrable (fun omega =>
      sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar) mu := by
  have hCoordinateMeas : ∀ i,
      AEStronglyMeasurable[mOmega]
        (fun omega =>
          randomPrimalTrajectory P bInit etaB gHat t omega i - betaStar i) mu := by
    intro i
    have hTrajectoryAmbient := (hTrajectoryMeas i).mono hmCond
    have hConst : AEStronglyMeasurable[mOmega] (fun _ : Omega => betaStar i) mu :=
      aestronglyMeasurable_const
    refine (hTrajectoryAmbient.sub hConst).congr ?_
    exact Eventually.of_forall (fun _omega => rfl)
  have hDistMeas : AEStronglyMeasurable (fun omega =>
      sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar) mu := by
    change AEStronglyMeasurable (fun omega =>
      ∑ i, (randomPrimalTrajectory P bInit etaB gHat t omega i - betaStar i) ^ 2) mu
    refine (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _hi => (hCoordinateMeas i).pow 2)).congr ?_
    exact Eventually.of_forall (fun omega => by simp)
  apply Integrable.of_bound hDistMeas (4 * B ^ 2)
  exact Eventually.of_forall (fun omega => by
    have hUpper :
        sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar ≤
          4 * B ^ 2 := by
      simpa [randomPrimalTrajectory] using
        primalTrajectory_sqDist_le_four_mul_sq C P bInit betaStar etaB B
          (fun s => gHat s omega) hInit hPFeas hbetaStar hCBall t
    have hNonneg :
        0 ≤ sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar := by
      simp only [sqDist, sqNorm]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hNonneg] using hUpper)

/-- Exact pointwise distance recursion for the actual random projected trajectory, obtained
from `primalTrajectory_sqDist_le`. No sign assumption on `etaB` is needed. -/
theorem randomPrimalTrajectory_sqDist_le
    {Omega : Type*} {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → Fin p → ℝ) (bInit betaStar : Fin p → ℝ)
    (etaB : ℝ) (gHat : ℕ → Omega → Fin p → ℝ)
    (hbetaStar : betaStar ∈ C) (hPDist : HasProjectionDistanceBound C P)
    (t : ℕ) (omega : Omega) :
    sqDist (randomPrimalTrajectory P bInit etaB gHat (t + 1) omega) betaStar ≤
      sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar -
        2 * etaB * vectorDot (gHat t omega)
          (primalDisplacement
            (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar) +
        etaB ^ 2 * sqNorm (gHat t omega) := by
  simpa [randomPrimalTrajectory] using
    primalTrajectory_sqDist_le C P bInit betaStar etaB
      (fun s => gHat s omega) hbetaStar hPDist t

/-- Expected one-step recursion for the actual stochastic projected-primal trajectory. It has
exactly the scalar `hrec` shape used later by `scalar_proposition_A2`. The quantity
`primalGradSqBound` already denotes `G_b^2` and is not squared again. -/
theorem stochasticPrimalTrajectory_expected_recursion
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (hmCond : ∀ t, mCond t ≤ mOmega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (etaB B primalGradSqBound : ℝ)
    (gHat F : ℕ → Omega → Fin p → ℝ) (t : ℕ)
    (hB : 0 ≤ B) (hInit : bInit ∈ C) (hbetaStar : betaStar ∈ C)
    (hPFeas : MapsIntoFeasibleSet C P)
    (hPDist : HasProjectionDistanceBound C P)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hTrajectoryMeas : ∀ s i,
      AEStronglyMeasurable[mCond s]
        (fun omega => randomPrimalTrajectory P bInit etaB gHat s omega i) mu)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat t omega i) mu)
    (hGradSqInt : Integrable (fun omega => sqNorm (gHat t omega)) mu)
    (hCondUnbiased : ∀ i,
      (fun omega => F t omega i) =ᵐ[mu]
        mu[(fun omega => gHat t omega i) | mCond t])
    (hCondGradSq :
      mu[(fun omega => sqNorm (gHat t omega)) | mCond t] ≤ᵐ[mu]
        fun _ => primalGradSqBound) :
    expectedPrimalTrajectoryDistSq
        (mu := mu) P bInit etaB gHat betaStar (t + 1) ≤
      expectedPrimalTrajectoryDistSq
          (mu := mu) P bInit etaB gHat betaStar t -
        2 * etaB * expectedPrimalTrajectoryDirection
          (mu := mu) P bInit etaB gHat F betaStar t +
        etaB ^ 2 * primalGradSqBound := by
  have hCurrentDistInt : Integrable (fun omega =>
      sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar) mu :=
    integrable_randomPrimalTrajectory_sqDist (hmCond t)
      C P bInit betaStar etaB B gHat hInit hbetaStar hPFeas hCBall t
      (hTrajectoryMeas t)
  have hNextDistInt : Integrable (fun omega =>
      sqDist (randomPrimalTrajectory P bInit etaB gHat (t + 1) omega) betaStar) mu :=
    integrable_randomPrimalTrajectory_sqDist (hmCond (t + 1))
      C P bInit betaStar etaB B gHat hInit hbetaStar hPFeas hCBall (t + 1)
      (hTrajectoryMeas (t + 1))
  have hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond t]
        (fun omega => primalDisplacement
          (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar i) mu :=
    randomPrimalTrajectory_displacement_aestronglyMeasurable
      (mCond := mCond t) (mOmega := mOmega) (mu := mu)
      P bInit betaStar etaB gHat t (hTrajectoryMeas t)
  have hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement
        (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar i‖ ≤ 2 * B := by
    intro i
    exact Eventually.of_forall (fun omega => by
      simpa [Real.norm_eq_abs] using
        abs_randomPrimalTrajectory_displacement_le_two_mul
          C P bInit betaStar etaB B gHat hB hInit hbetaStar
          hPFeas hCBall t omega i)
  have hPathwise : ∀ᵐ omega ∂mu,
      sqDist (randomPrimalTrajectory P bInit etaB gHat (t + 1) omega) betaStar ≤
        sqDist (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar -
          2 * etaB * vectorDot (gHat t omega)
            (primalDisplacement
              (randomPrimalTrajectory P bInit etaB gHat t omega) betaStar) +
          etaB ^ 2 * sqNorm (gHat t omega) :=
    Eventually.of_forall (fun omega =>
      randomPrimalTrajectory_sqDist_le
        C P bInit betaStar etaB gHat hbetaStar hPDist t omega)
  have hExpected :=
    expected_primal_recursion_of_condExpectedSqNorm_le
      (hmCond t)
      (randomPrimalTrajectory P bInit etaB gHat t)
      (randomPrimalTrajectory P bInit etaB gHat (t + 1))
      (fun omega => gHat t omega) (fun omega => F t omega)
      betaStar etaB primalGradSqBound hPathwise hNextDistInt hCurrentDistInt
      hGradSqInt hgHatInt hDisplacementMeas (2 * B) hDisplacementBound
      hCondUnbiased hCondGradSq
  simpa [expectedPrimalTrajectoryDistSq, expectedPrimalTrajectoryDirection,
    expectedSqDist, expectedDirection] using hExpected

end NegDRO
