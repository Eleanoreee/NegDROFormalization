import NegDROFormalization.PrimalTrajectory

/-!
# Finite averages of primal iterates

This module is independent of the NegDRO objective. It proves squared-distance Jensen for the
explicit finite-coordinate distance, first pointwise and then under a probability measure.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Coordinatewise arithmetic average over rounds `0, ..., T - 1`, using real division. -/
noncomputable def primalAverage
    {p : ℕ} (T : ℕ) (b : ℕ → Fin p → ℝ) : Fin p → ℝ :=
  fun i => (∑ t ∈ Finset.range T, b t i) / (T : ℝ)

/-- Samplewise coordinate average of a random finite-vector sequence. -/
noncomputable def randomPrimalAverage
    {Omega : Type*} {p : ℕ} (T : ℕ)
    (b : ℕ → Omega → Fin p → ℝ) : Omega → Fin p → ℝ :=
  fun omega => primalAverage T (fun t => b t omega)

/-- Finite Cauchy--Schwarz for a real sequence over `Finset.range T`. This is the precise
coordinate inequality used below. -/
theorem sq_sum_range_le_card_mul_sum_sq
    (T : ℕ) (x : ℕ → ℝ) :
    (∑ t ∈ Finset.range T, x t) ^ 2 ≤
      (T : ℝ) * ∑ t ∈ Finset.range T, (x t) ^ 2 := by
  simpa only [Finset.card_range] using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.range T) (f := x))

/-- Deterministic squared-distance Jensen inequality for the coordinatewise arithmetic average.
The factor is exactly `1 / T`, and `hT` ensures all real divisions are valid. -/
theorem sqDist_primalAverage_le_average_sqDist
    {p : ℕ} (T : ℕ) (b : ℕ → Fin p → ℝ)
    (betaStar : Fin p → ℝ) (hT : 0 < T) :
    sqDist (primalAverage T b) betaStar ≤
      (1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T, sqDist (b t) betaStar := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTreal
  have hDisplacement : ∀ i,
      primalAverage T b i - betaStar i =
        (∑ t ∈ Finset.range T, (b t i - betaStar i)) / (T : ℝ) := by
    intro i
    simp only [primalAverage, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
  have hCoordinate : ∀ i,
      (primalAverage T b i - betaStar i) ^ 2 ≤
        (1 / (T : ℝ)) *
          ∑ t ∈ Finset.range T, (b t i - betaStar i) ^ 2 := by
    intro i
    rw [hDisplacement i]
    have hCS := sq_sum_range_le_card_mul_sum_sq T
      (fun t => b t i - betaStar i)
    have hDiv := div_le_div_of_nonneg_right hCS (sq_nonneg (T : ℝ))
    calc
      ((∑ t ∈ Finset.range T, (b t i - betaStar i)) / (T : ℝ)) ^ 2 =
          (∑ t ∈ Finset.range T, (b t i - betaStar i)) ^ 2 / (T : ℝ) ^ 2 := by
        rw [div_pow]
      _ ≤
          ((T : ℝ) * ∑ t ∈ Finset.range T,
            (b t i - betaStar i) ^ 2) / (T : ℝ) ^ 2 := hDiv
      _ = (1 / (T : ℝ)) *
          ∑ t ∈ Finset.range T, (b t i - betaStar i) ^ 2 := by
        field_simp
  simp only [sqDist, sqNorm]
  calc
    ∑ i, (primalAverage T b i - betaStar i) ^ 2 ≤
        ∑ i, (1 / (T : ℝ)) *
          ∑ t ∈ Finset.range T, (b t i - betaStar i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hCoordinate i
    _ = (1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T, ∑ i, (b t i - betaStar i) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

/-- Under coordinatewise a.e. strong measurability, bounded-domain membership makes the
squared distance at each relevant round integrable. -/
theorem integrable_randomPrimalSequence_sqDist_of_mem
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {p : ℕ}
    (C : Set (Fin p → ℝ)) (B : ℝ) (betaStar : Fin p → ℝ)
    (b : ℕ → Omega → Fin p → ℝ) (t : ℕ)
    (hCBall : SetContainedInCoordinateSqBall C B) (hbetaStar : betaStar ∈ C)
    (hbMem : ∀ omega, b t omega ∈ C)
    (hbMeas : ∀ i,
      AEStronglyMeasurable (fun omega => b t omega i) mu) :
    Integrable (fun omega => sqDist (b t omega) betaStar) mu := by
  have hCoordinateMeas : ∀ i,
      AEStronglyMeasurable (fun omega => b t omega i - betaStar i) mu := by
    intro i
    have hConst : AEStronglyMeasurable (fun _ : Omega => betaStar i) mu :=
      aestronglyMeasurable_const
    refine ((hbMeas i).sub hConst).congr ?_
    exact Eventually.of_forall (fun _omega => rfl)
  have hDistMeas : AEStronglyMeasurable
      (fun omega => sqDist (b t omega) betaStar) mu := by
    change AEStronglyMeasurable
      (fun omega => ∑ i, (b t omega i - betaStar i) ^ 2) mu
    refine (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _hi => (hCoordinateMeas i).pow 2)).congr ?_
    exact Eventually.of_forall (fun omega => by simp)
  apply Integrable.of_bound hDistMeas (4 * B ^ 2)
  exact Eventually.of_forall (fun omega => by
    have hUpper := sqDist_le_four_mul_sq_of_mem
      C B (b t omega) betaStar hCBall (hbMem omega) hbetaStar
    have hNonneg : 0 ≤ sqDist (b t omega) betaStar := by
      simp only [sqDist, sqNorm]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hNonneg] using hUpper)

/-- The averaged squared distance is integrable when all averaged points lie in a common
bounded coordinate-squared domain and their coordinates are measurable. Convexity of `C` is not
needed: the deterministic Jensen inequality bounds the average's distance by `4 * B^2`. -/
theorem integrable_randomPrimalAverage_sqDist_of_mem
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {p : ℕ}
    (T : ℕ) (hT : 0 < T)
    (C : Set (Fin p → ℝ)) (B : ℝ) (betaStar : Fin p → ℝ)
    (b : ℕ → Omega → Fin p → ℝ)
    (hCBall : SetContainedInCoordinateSqBall C B) (hbetaStar : betaStar ∈ C)
    (hbMem : ∀ t < T, ∀ omega, b t omega ∈ C)
    (hbMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable (fun omega => b t omega i) mu) :
    Integrable (fun omega =>
      sqDist (randomPrimalAverage T b omega) betaStar) mu := by
  have hAverageCoordinateMeas : ∀ i,
      AEStronglyMeasurable (fun omega => randomPrimalAverage T b omega i) mu := by
    intro i
    change AEStronglyMeasurable
      (fun omega => (∑ t ∈ Finset.range T, b t omega i) / (T : ℝ)) mu
    have hSumMeas := Finset.aestronglyMeasurable_sum (Finset.range T)
      (fun t ht => hbMeas t (Finset.mem_range.mp ht) i)
    have hScaled := hSumMeas.const_mul (1 / (T : ℝ))
    refine hScaled.congr ?_
    exact Eventually.of_forall (fun omega => by
      simp [div_eq_mul_inv, mul_comm])
  have hAverageDistMeas : AEStronglyMeasurable (fun omega =>
      sqDist (randomPrimalAverage T b omega) betaStar) mu := by
    have hCoordinateMeas : ∀ i,
        AEStronglyMeasurable (fun omega =>
          randomPrimalAverage T b omega i - betaStar i) mu := by
      intro i
      have hConst : AEStronglyMeasurable (fun _ : Omega => betaStar i) mu :=
        aestronglyMeasurable_const
      refine ((hAverageCoordinateMeas i).sub hConst).congr ?_
      exact Eventually.of_forall (fun _omega => rfl)
    change AEStronglyMeasurable (fun omega =>
      ∑ i, (randomPrimalAverage T b omega i - betaStar i) ^ 2) mu
    refine (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _hi => (hCoordinateMeas i).pow 2)).congr ?_
    exact Eventually.of_forall (fun omega => by simp)
  apply Integrable.of_bound hAverageDistMeas (4 * B ^ 2)
  exact Eventually.of_forall (fun omega => by
    have hJensen := sqDist_primalAverage_le_average_sqDist
      T (fun t => b t omega) betaStar hT
    have hEach : ∀ t ∈ Finset.range T,
        sqDist (b t omega) betaStar ≤ 4 * B ^ 2 := by
      intro t ht
      exact sqDist_le_four_mul_sq_of_mem C B (b t omega) betaStar
        hCBall (hbMem t (Finset.mem_range.mp ht) omega) hbetaStar
    have hSum := Finset.sum_le_sum hEach
    have hScale := mul_le_mul_of_nonneg_left hSum
      (by positivity : 0 ≤ 1 / (T : ℝ))
    have hBound :
        sqDist (randomPrimalAverage T b omega) betaStar ≤ 4 * B ^ 2 := by
      calc
        sqDist (randomPrimalAverage T b omega) betaStar ≤
            (1 / (T : ℝ)) *
              ∑ t ∈ Finset.range T, sqDist (b t omega) betaStar := by
          simpa [randomPrimalAverage] using hJensen
        _ ≤ (1 / (T : ℝ)) *
            ∑ _t ∈ Finset.range T, 4 * B ^ 2 := hScale
        _ = 4 * B ^ 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hTreal : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
          field_simp
    have hNonneg :
        0 ≤ sqDist (randomPrimalAverage T b omega) betaStar := by
      simp only [sqDist, sqNorm]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hNonneg] using hBound)

/-- Expected squared-distance Jensen inequality. Integrability of every term and of the
average is derived from measurable coordinates and common bounded-domain membership. -/
theorem integral_sqDist_randomPrimalAverage_le_average_integral_sqDist
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {p : ℕ}
    (T : ℕ) (hT : 0 < T)
    (C : Set (Fin p → ℝ)) (B : ℝ) (betaStar : Fin p → ℝ)
    (b : ℕ → Omega → Fin p → ℝ)
    (hCBall : SetContainedInCoordinateSqBall C B) (hbetaStar : betaStar ∈ C)
    (hbMem : ∀ t < T, ∀ omega, b t omega ∈ C)
    (hbMeas : ∀ t < T, ∀ i,
      AEStronglyMeasurable (fun omega => b t omega i) mu) :
    (∫ omega, sqDist (randomPrimalAverage T b omega) betaStar ∂mu) ≤
      (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        ∫ omega, sqDist (b t omega) betaStar ∂mu := by
  have hEachInt : ∀ t < T,
      Integrable (fun omega => sqDist (b t omega) betaStar) mu := by
    intro t ht
    exact integrable_randomPrimalSequence_sqDist_of_mem
      C B betaStar b t hCBall hbetaStar (hbMem t ht) (hbMeas t ht)
  have hAverageInt := integrable_randomPrimalAverage_sqDist_of_mem
    T hT C B betaStar b hCBall hbetaStar hbMem hbMeas
  have hSumInt : Integrable (fun omega =>
      ∑ t ∈ Finset.range T, sqDist (b t omega) betaStar) mu :=
    integrable_finsetSum (Finset.range T) (fun t ht =>
      hEachInt t (Finset.mem_range.mp ht))
  have hRightInt := hSumInt.const_mul (1 / (T : ℝ))
  have hIntegrated :
      (∫ omega, sqDist (randomPrimalAverage T b omega) betaStar ∂mu) ≤
        ∫ omega, (1 / (T : ℝ)) *
          ∑ t ∈ Finset.range T, sqDist (b t omega) betaStar ∂mu :=
    integral_mono_ae hAverageInt hRightInt
      (Eventually.of_forall (fun omega => by
        simpa [randomPrimalAverage] using
          sqDist_primalAverage_le_average_sqDist
            T (fun t => b t omega) betaStar hT))
  calc
    (∫ omega, sqDist (randomPrimalAverage T b omega) betaStar ∂mu) ≤
        ∫ omega, (1 / (T : ℝ)) *
          ∑ t ∈ Finset.range T, sqDist (b t omega) betaStar ∂mu := hIntegrated
    _ = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        ∫ omega, sqDist (b t omega) betaStar ∂mu := by
      rw [integral_const_mul]
      rw [integral_finsetSum (Finset.range T) (fun t ht =>
        hEachInt t (Finset.mem_range.mp ht))]

end NegDRO
