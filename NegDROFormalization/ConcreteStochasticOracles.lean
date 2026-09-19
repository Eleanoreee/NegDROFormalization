import NegDROFormalization.MirrorRemainderBound
import NegDROFormalization.QuadraticStructure

/-!
# Concrete single-sample NegDRO stochastic oracles

This module defines the uniformly-environment-scaled sample oracles for the project's online
fresh-sample projected-SGD/EG stochastic extension and proves their deterministic pointwise
algebra.  These are not the literal updates of official v3 Algorithm 1, which exactly maximizes
the empirical risk over `w` before a primal gradient step.  The primal oracle is a descent gradient and uses
the residual `xᵀb - y`; the dual oracle is an ascent gradient and uses the squared residual, so its
sign convention is immaterial there.  No probability or conditional-expectation assumptions occur
in this module.

The explicit `sqNorm` is used for primal vectors.  Dual estimates are coordinatewise
`HasCoordinateAbsBound` statements, not claims about the default norm on a function type.
-/

set_option autoImplicit false

namespace NegDRO

/-- Transparent finite-coordinate indicator, equal to one at `e` and zero elsewhere. -/
def finCoordinateIndicator {m : ℕ} (e j : Fin m) : ℝ :=
  if j = e then 1 else 0

/-- The concrete single-sample primal oracle
`2 m (w_e - a_gamma) x (xᵀ b - y)`.  The factor `m` compensates for uniform environment
sampling. -/
noncomputable def samplePrimalOracle
    {m p : ℕ} (gamma : ℝ) (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ) : Fin p → ℝ :=
  fun i ↦
    2 * (m : ℝ) * (w e - negDROGammaCoefficient m gamma) *
      (vectorDot x b - y) * x i

/-- The concrete single-sample unpenalized dual oracle
`m (y - xᵀ b)² e_e`. -/
def sampleUnpenalizedDualOracle
    {m p : ℕ} (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) : Fin m → ℝ :=
  fun j ↦ (m : ℝ) * (y - vectorDot x b) ^ 2 * finCoordinateIndicator e j

/-- The concrete single-sample penalized dual oracle, with the ascent-gradient correction
`-2 penalty w`. -/
def samplePenalizedDualOracle
    {m p : ℕ} (penalty : ℝ) (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ) : Fin m → ℝ :=
  fun j ↦ sampleUnpenalizedDualOracle e x y b j - 2 * penalty * w j

/-- Exact squared-Euclidean-size expansion of the concrete primal sample oracle. -/
theorem samplePrimalOracle_sqNorm
    {m p : ℕ} (gamma : ℝ) (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ) :
    sqNorm (samplePrimalOracle gamma e x y b w) =
      4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
        (vectorDot x b - y) ^ 2 * sqNorm x := by
  simp only [sqNorm, samplePrimalOracle]
  calc
    ∑ i, (2 * (m : ℝ) * (w e - negDROGammaCoefficient m gamma) *
        (vectorDot x b - y) * x i) ^ 2 =
        ∑ i, (4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
          (vectorDot x b - y) ^ 2) * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
        (vectorDot x b - y) ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

/-- Every coordinate of the unpenalized dual sample oracle is bounded by the nonnegative scalar
`m (y - xᵀb)²`. -/
theorem sampleUnpenalizedDualOracle_coordinate_abs_le
    {m p : ℕ} (e : Fin m) (x : Fin p → ℝ) (y : ℝ) (b : Fin p → ℝ) (j : Fin m) :
    |sampleUnpenalizedDualOracle e x y b j| ≤
      (m : ℝ) * (y - vectorDot x b) ^ 2 := by
  by_cases hje : j = e
  · subst j
    simp [sampleUnpenalizedDualOracle, finCoordinateIndicator, abs_of_nonneg,
      mul_nonneg, sq_nonneg]
  · simp [sampleUnpenalizedDualOracle, finCoordinateIndicator, hje,
      mul_nonneg, sq_nonneg]

/-- Predicate-form coordinate bound for the unpenalized dual sample oracle. -/
theorem sampleUnpenalizedDualOracle_hasCoordinateAbsBound
    {m p : ℕ} (e : Fin m) (x : Fin p → ℝ) (y : ℝ) (b : Fin p → ℝ) :
    HasCoordinateAbsBound (sampleUnpenalizedDualOracle e x y b)
      ((m : ℝ) * (y - vectorDot x b) ^ 2) := by
  intro j
  exact sampleUnpenalizedDualOracle_coordinate_abs_le e x y b j

/-- The penalty contribution has coordinate absolute value at most `2 * penalty` on the simplex. -/
theorem penalty_coordinate_abs_le
    {m : ℕ} (penalty : ℝ) (w : Fin m → ℝ) (j : Fin m)
    (hpenalty : 0 ≤ penalty) (hw : IsSimplex w) :
    |2 * penalty * w j| ≤ 2 * penalty := by
  have hwj := simplex_coordinate_bounds hw j
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpenalty) hwj.1)]
  nlinarith

/-- Every coordinate of the penalized dual sample oracle is bounded by the sample residual bound
plus `2 * penalty`, derived from simplex coordinate bounds. -/
theorem samplePenalizedDualOracle_coordinate_abs_le
    {m p : ℕ} (penalty : ℝ) (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ) (j : Fin m)
    (hpenalty : 0 ≤ penalty) (hw : IsSimplex w) :
    |samplePenalizedDualOracle penalty e x y b w j| ≤
      (m : ℝ) * (y - vectorDot x b) ^ 2 + 2 * penalty := by
  calc
    |samplePenalizedDualOracle penalty e x y b w j| ≤
        |sampleUnpenalizedDualOracle e x y b j| + |2 * penalty * w j| := by
      simpa [samplePenalizedDualOracle] using
        (abs_sub_le (sampleUnpenalizedDualOracle e x y b j) 0 (2 * penalty * w j))
    _ ≤ (m : ℝ) * (y - vectorDot x b) ^ 2 + 2 * penalty :=
      add_le_add
        (sampleUnpenalizedDualOracle_coordinate_abs_le e x y b j)
        (penalty_coordinate_abs_le penalty w j hpenalty hw)

/-- Predicate-form coordinate bound for the penalized dual sample oracle. -/
theorem samplePenalizedDualOracle_hasCoordinateAbsBound
    {m p : ℕ} (penalty : ℝ) (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ)
    (hpenalty : 0 ≤ penalty) (hw : IsSimplex w) :
    HasCoordinateAbsBound (samplePenalizedDualOracle penalty e x y b w)
      ((m : ℝ) * (y - vectorDot x b) ^ 2 + 2 * penalty) := by
  intro j
  exact samplePenalizedDualOracle_coordinate_abs_le penalty e x y b w j hpenalty hw

/-- Elementary two-square estimate used for residuals. -/
theorem sub_sq_le_two_sq_add_two_sq (a b : ℝ) :
    (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- Pure scalar fourth-power residual inequality. -/
theorem sub_fourth_le_eight_fourth_add_eight_fourth (a b : ℝ) :
    (a - b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  have hsq := sub_sq_le_two_sq_add_two_sq a b
  have hnonneg : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have hrhs : 0 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by positivity
  have hsquare := mul_self_le_mul_self hnonneg hsq
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

/-- Finite-dimensional squared Cauchy--Schwarz for the project's explicit dot product and
explicit squared Euclidean size. -/
theorem vectorDot_sq_le_sqNorm_mul_sqNorm
    {p : ℕ} (x b : Fin p → ℝ) :
    (vectorDot x b) ^ 2 ≤ sqNorm x * sqNorm b := by
  simpa only [vectorDot, sqNorm] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p)) x b)

/-- A bound `sqNorm b ≤ B²` converts finite Cauchy--Schwarz into the exact fourth-power
estimate needed by the oracle moments. -/
theorem vectorDot_fourth_le_of_sqNorm_le
    {p : ℕ} (x b : Fin p → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2) :
    (vectorDot x b) ^ 4 ≤ B ^ 4 * (sqNorm x) ^ 2 := by
  have hx : 0 ≤ sqNorm x := sqNorm_nonneg x
  have hBsq : 0 ≤ B ^ 2 := pow_nonneg hB 2
  have hdot : (vectorDot x b) ^ 2 ≤ sqNorm x * B ^ 2 :=
    (vectorDot_sq_le_sqNorm_mul_sqNorm x b).trans
      (mul_le_mul_of_nonneg_left hb hx)
  have hsquare := mul_self_le_mul_self (sq_nonneg (vectorDot x b)) hdot
  calc
    (vectorDot x b) ^ 4 = ((vectorDot x b) ^ 2) ^ 2 := by ring
    _ ≤ (sqNorm x * B ^ 2) ^ 2 := by simpa [pow_two] using hsquare
    _ = B ^ 4 * (sqNorm x) ^ 2 := by ring

/-- Residual fourth-power estimate before applying a domain bound on `b`. -/
theorem residual_fourth_le
    {p : ℕ} (x b : Fin p → ℝ) (y : ℝ) :
    (y - vectorDot x b) ^ 4 ≤ 8 * y ^ 4 + 8 * (vectorDot x b) ^ 4 := by
  exact sub_fourth_le_eight_fourth_add_eight_fourth y (vectorDot x b)

/-- Residual fourth-power estimate under the explicit squared-domain bound
`sqNorm b ≤ B²`. -/
theorem residual_fourth_le_of_sqNorm_le
    {p : ℕ} (x b : Fin p → ℝ) (y B : ℝ)
    (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2) :
    (y - vectorDot x b) ^ 4 ≤
      8 * y ^ 4 + 8 * B ^ 4 * (sqNorm x) ^ 2 := by
  calc
    (y - vectorDot x b) ^ 4 ≤ 8 * y ^ 4 + 8 * (vectorDot x b) ^ 4 :=
      residual_fourth_le x b y
    _ ≤ 8 * y ^ 4 + 8 * (B ^ 4 * (sqNorm x) ^ 2) := by
      gcongr
      exact vectorDot_fourth_le_of_sqNorm_le x b B hB hb
    _ = 8 * y ^ 4 + 8 * B ^ 4 * (sqNorm x) ^ 2 := by ring

/-- The exact pointwise residual-square product estimate retained for the mixed-moment
Cauchy--Schwarz calculation in the next module. -/
theorem sqNorm_mul_residual_sq_le
    {p : ℕ} (x b : Fin p → ℝ) (y B : ℝ)
    (_hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2) :
    sqNorm x * (vectorDot x b - y) ^ 2 ≤
      2 * sqNorm x * y ^ 2 + 2 * B ^ 2 * (sqNorm x) ^ 2 := by
  have hx : 0 ≤ sqNorm x := sqNorm_nonneg x
  have hres := sub_sq_le_two_sq_add_two_sq (vectorDot x b) y
  have hresMul := mul_le_mul_of_nonneg_left hres hx
  have hdot : (vectorDot x b) ^ 2 ≤ sqNorm x * B ^ 2 :=
    (vectorDot_sq_le_sqNorm_mul_sqNorm x b).trans
      (mul_le_mul_of_nonneg_left hb hx)
  have hdotMul := mul_le_mul_of_nonneg_left hdot hx
  nlinarith

/-- Pointwise primal-oracle upper bound, still retaining the exact mixed residual terms for
the following probability module. -/
theorem samplePrimalOracle_sqNorm_le
    {m p : ℕ} (gamma : ℝ) (e : Fin m) (x : Fin p → ℝ) (y B : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ)
    (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2) :
    sqNorm (samplePrimalOracle gamma e x y b w) ≤
      4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
        (2 * sqNorm x * y ^ 2 + 2 * B ^ 2 * (sqNorm x) ^ 2) := by
  rw [samplePrimalOracle_sqNorm]
  have hcoefficient :
      0 ≤ 4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 := by
    positivity
  have hres := sqNorm_mul_residual_sq_le x b y B hB hb
  calc
    4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
          (vectorDot x b - y) ^ 2 * sqNorm x =
        (4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2) *
          (sqNorm x * (vectorDot x b - y) ^ 2) := by ring
    _ ≤ (4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2) *
          (2 * sqNorm x * y ^ 2 + 2 * B ^ 2 * (sqNorm x) ^ 2) :=
      mul_le_mul_of_nonneg_left hres hcoefficient
    _ = 4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
          (2 * sqNorm x * y ^ 2 + 2 * B ^ 2 * (sqNorm x) ^ 2) := by ring

/-- Exact expansion of the shifted simplex coefficient squares. -/
theorem shiftedCoefficient_sq_sum_eq
    {m : ℕ} (gamma : ℝ) (w : Fin m → ℝ) (hw : IsSimplex w) :
    ∑ e, (w e - negDROGammaCoefficient m gamma) ^ 2 =
      sqNorm w - 2 * negDROGammaCoefficient m gamma +
        (m : ℝ) * (negDROGammaCoefficient m gamma) ^ 2 := by
  calc
    ∑ e, (w e - negDROGammaCoefficient m gamma) ^ 2 =
        ∑ e, ((w e) ^ 2 - 2 * negDROGammaCoefficient m gamma * w e +
          (negDROGammaCoefficient m gamma) ^ 2) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = sqNorm w - 2 * negDROGammaCoefficient m gamma +
        (m : ℝ) * (negDROGammaCoefficient m gamma) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sqNorm,
        ← Finset.mul_sum, hw.2, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The shifted coefficients have total squared size at most one on the simplex.  The correction
`-2 a_gamma + m a_gamma²` is proved nonpositive from the explicit formula for `a_gamma`. -/
theorem shiftedCoefficient_sq_sum_le_one
    {m : ℕ} (gamma : ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    ∑ e, (w e - negDROGammaCoefficient m gamma) ^ 2 ≤ 1 := by
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  have ha0 : 0 ≤ negDROGammaCoefficient m gamma := by
    exact div_nonneg hgamma hdenPos.le
  have hma : (m : ℝ) * negDROGammaCoefficient m gamma ≤ 1 := by
    rw [negDROGammaCoefficient, ← mul_div_assoc]
    apply (div_le_iff₀ hdenPos).2
    ring_nf
    linarith
  have hcorrection :
      -2 * negDROGammaCoefficient m gamma +
          (m : ℝ) * (negDROGammaCoefficient m gamma) ^ 2 ≤ 0 := by
    nlinarith
  rw [shiftedCoefficient_sq_sum_eq gamma w hw]
  have hwNorm := (simplex_sqNorm_bounds hw).2
  linarith

end NegDRO
