import NegDROFormalization.ConcreteStochasticOracles

/-!
# Environment-averaged moment bounds for the project's stochastic extension

All environments share one probability space and probability measure in this interface.  This is
a convenient representation of the per-environment laws in the PDF; it does not assert that the
different environment random variables are jointly sampled by the algorithm.  The uniform
environment average is written explicitly, and this module contains no filtration or conditional
expectation claims.

The sample oracles and constants here belong to the online fresh-sample projected-SGD/EG
extension developed in this project, not to the literal exact-`w`-maximization update of official
v3 Algorithm 1.

`KX` bounds `E[(sqNorm X)²] = E[‖X‖₂⁴]` and `KY` bounds `E[Y⁴]`; neither constant is a
square root.  Coordinate measurability and integrability of both fourth-moment random variables
are explicit hypotheses.
-/

set_option autoImplicit false

open MeasureTheory
open scoped MeasureTheory

namespace NegDRO

/-- Explicit uniform average over the finite environment index. -/
noncomputable def envAverage (m : ℕ) (f : Fin m → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ e, f e

/-- PDF constant `G_b² = 4m (2 √(KY KX) + 2 B² KX)`. -/
noncomputable def explicitPrimalGradSqBound
    (m : ℕ) (B KX KY : ℝ) : ℝ :=
  4 * (m : ℝ) * (2 * Real.sqrt (KY * KX) + 2 * B ^ 2 * KX)

/-- Tight unpenalized dual coordinate-bound second-moment constant from the PDF calculation. -/
def explicitUnpenalizedDualGradSqBound
    (m : ℕ) (B KX KY : ℝ) : ℝ :=
  (m : ℝ) ^ 2 * (8 * KY + 8 * B ^ 4 * KX)

/-- Penalized dual coordinate-bound second-moment constant
`2 m² (8 KY + 8 B⁴ KX) + 8 penalty²`. -/
def explicitPenalizedDualGradSqBound
    (m : ℕ) (penalty B KX KY : ℝ) : ℝ :=
  2 * (m : ℝ) ^ 2 * (8 * KY + 8 * B ^ 4 * KX) + 8 * penalty ^ 2

/-- Coordinatewise a.e. strong measurability implies measurability of explicit `sqNorm`. -/
theorem aestronglyMeasurable_sqNorm_of_coordinatewise
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (X : Omega → Fin p → ℝ)
    (hX : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu) :
    AEStronglyMeasurable (fun omega ↦ sqNorm (X omega)) mu := by
  change AEStronglyMeasurable (fun omega ↦ ∑ i, (X omega i) ^ 2) mu
  refine (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _hi ↦ (hX i).pow 2)).congr ?_
  exact ae_of_all mu (fun omega ↦ by simp)

/-- Coordinatewise a.e. strong measurability implies measurability of a dot product with a fixed
finite vector. -/
theorem aestronglyMeasurable_vectorDot_left_of_coordinatewise
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {p : ℕ}
    (X : Omega → Fin p → ℝ) (b : Fin p → ℝ)
    (hX : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu) :
    AEStronglyMeasurable (fun omega ↦ vectorDot (X omega) b) mu := by
  change AEStronglyMeasurable (fun omega ↦ ∑ i, X omega i * b i) mu
  have hTerm : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i * b i) mu := by
    intro i
    have hConst : AEStronglyMeasurable (fun _ : Omega ↦ b i) mu :=
      aestronglyMeasurable_const
    exact (hX i).mul hConst
  refine (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _hi ↦ hTerm i)).congr ?_
  exact ae_of_all mu (fun omega ↦ by simp)

/-- Exact integral Cauchy--Schwarz bound for the mixed fourth-moment term. -/
theorem integral_sqNorm_mul_sq_le_sqrt_mul_sqrt
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (hXMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu)
    (hYMeas : AEStronglyMeasurable Y mu)
    (hX4Int : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hY4Int : Integrable (fun omega ↦ (Y omega) ^ 4) mu) :
    ∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu ≤
      Real.sqrt (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) *
        Real.sqrt (∫ omega, (Y omega) ^ 4 ∂mu) := by
  have hSqNormMeas := aestronglyMeasurable_sqNorm_of_coordinatewise X hXMeas
  have hYSqMeas : AEStronglyMeasurable (fun omega ↦ (Y omega) ^ 2) mu := hYMeas.pow 2
  have hYSqSqInt : Integrable (fun omega ↦ ((Y omega) ^ 2) ^ 2) mu := by
    refine hY4Int.congr ?_
    exact ae_of_all mu (fun omega ↦ by ring)
  have hXMem : MemLp (fun omega ↦ sqNorm (X omega)) 2 mu :=
    (memLp_two_iff_integrable_sq hSqNormMeas).2 hX4Int
  have hYMem : MemLp (fun omega ↦ (Y omega) ^ 2) 2 mu :=
    (memLp_two_iff_integrable_sq hYSqMeas).2 hYSqSqInt
  have hXMem' : MemLp (fun omega ↦ sqNorm (X omega)) (ENNReal.ofReal (2 : ℝ)) mu := by
    norm_num
    exact hXMem
  have hYMem' : MemLp (fun omega ↦ (Y omega) ^ 2) (ENNReal.ofReal (2 : ℝ)) mu := by
    norm_num
    exact hYMem
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (ae_of_all mu (fun omega ↦ sqNorm_nonneg (X omega)))
    (ae_of_all mu (fun omega ↦ sq_nonneg (Y omega))) hXMem' hYMem'
  have hYIntegral :
      (∫ omega, ((Y omega) ^ 2) ^ 2 ∂mu) = ∫ omega, (Y omega) ^ 4 ∂mu := by
    apply integral_congr_ae
    exact ae_of_all mu (fun omega ↦ by ring)
  calc
    ∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu ≤
      Real.sqrt (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, ((Y omega) ^ 2) ^ 2 ∂mu) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hHolder
    _ = Real.sqrt (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, (Y omega) ^ 4 ∂mu) := by rw [hYIntegral]

/-- Mixed moment bounded by the exact geometric mean of the supplied fourth-moment constants. -/
theorem integral_sqNorm_mul_sq_le_sqrt_moment_bounds
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) (KX KY : ℝ)
    (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hXMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu)
    (hYMeas : AEStronglyMeasurable Y mu)
    (hX4Int : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hY4Int : Integrable (fun omega ↦ (Y omega) ^ 4) mu)
    (hX4 : (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) ≤ KX)
    (hY4 : (∫ omega, (Y omega) ^ 4 ∂mu) ≤ KY) :
    ∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu ≤ Real.sqrt (KX * KY) := by
  calc
    ∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu ≤
        Real.sqrt (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) *
          Real.sqrt (∫ omega, (Y omega) ^ 4 ∂mu) :=
      integral_sqNorm_mul_sq_le_sqrt_mul_sqrt mu X Y hXMeas hYMeas hX4Int hY4Int
    _ ≤ Real.sqrt KX * Real.sqrt KY := by
      exact mul_le_mul (Real.sqrt_le_sqrt hX4) (Real.sqrt_le_sqrt hY4)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (KX * KY) := by rw [Real.sqrt_mul hKX]

/-- The mixed product itself is integrable under the two fourth-moment integrability
hypotheses. -/
theorem integrable_sqNorm_mul_sq_of_fourth_moments
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (hXMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu)
    (hYMeas : AEStronglyMeasurable Y mu)
    (hX4Int : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hY4Int : Integrable (fun omega ↦ (Y omega) ^ 4) mu) :
    Integrable (fun omega ↦ sqNorm (X omega) * (Y omega) ^ 2) mu := by
  have hSqNormMeas := aestronglyMeasurable_sqNorm_of_coordinatewise X hXMeas
  have hYSqMeas : AEStronglyMeasurable (fun omega ↦ (Y omega) ^ 2) mu := hYMeas.pow 2
  have hYSqSqInt : Integrable (fun omega ↦ ((Y omega) ^ 2) ^ 2) mu := by
    refine hY4Int.congr ?_
    exact ae_of_all mu (fun omega ↦ by ring)
  have hXMem : MemLp (fun omega ↦ sqNorm (X omega)) 2 mu :=
    (memLp_two_iff_integrable_sq hSqNormMeas).2 hX4Int
  have hYMem : MemLp (fun omega ↦ (Y omega) ^ 2) 2 mu :=
    (memLp_two_iff_integrable_sq hYSqMeas).2 hYSqSqInt
  change Integrable
    ((fun omega ↦ sqNorm (X omega)) * (fun omega ↦ (Y omega) ^ 2)) mu
  exact hXMem.integrable_mul hYMem

/-- Integrability of the fourth residual follows from the pointwise fourth-power estimate; no
independence between `X` and `Y` is used. -/
theorem integrable_residual_fourth_of_fourth_moments
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) (b : Fin p → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2)
    (hXMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu)
    (hYMeas : AEStronglyMeasurable Y mu)
    (hX4Int : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hY4Int : Integrable (fun omega ↦ (Y omega) ^ 4) mu) :
    Integrable (fun omega ↦ (Y omega - vectorDot (X omega) b) ^ 4) mu := by
  have hSqNormMeas := aestronglyMeasurable_sqNorm_of_coordinatewise X hXMeas
  have hDotMeas := aestronglyMeasurable_vectorDot_left_of_coordinatewise X b hXMeas
  have hResidualMeas : AEStronglyMeasurable
      (fun omega ↦ (Y omega - vectorDot (X omega) b) ^ 4) mu :=
    (hYMeas.sub hDotMeas).pow 4
  have hUpperInt : Integrable (fun omega ↦
      8 * (Y omega) ^ 4 + 8 * B ^ 4 * (sqNorm (X omega)) ^ 2) mu :=
    (hY4Int.const_mul 8).add (hX4Int.const_mul (8 * B ^ 4))
  refine hUpperInt.mono_nonneg hResidualMeas
    (ae_of_all mu (fun omega ↦ by positivity)) ?_
  exact ae_of_all mu (fun omega ↦ residual_fourth_le_of_sqNorm_le
    (X omega) b (Y omega) B hB hb)

/-- Integrated fourth-residual bound with the exact `8 KY + 8 B⁴ KX` constant. -/
theorem integral_residual_fourth_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {p : ℕ}
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) (b : Fin p → ℝ)
    (B KX KY : ℝ) (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2)
    (hXMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu)
    (hYMeas : AEStronglyMeasurable Y mu)
    (hX4Int : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hY4Int : Integrable (fun omega ↦ (Y omega) ^ 4) mu)
    (hX4 : (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) ≤ KX)
    (hY4 : (∫ omega, (Y omega) ^ 4 ∂mu) ≤ KY) :
    ∫ omega, (Y omega - vectorDot (X omega) b) ^ 4 ∂mu ≤
      8 * KY + 8 * B ^ 4 * KX := by
  have hResidualInt := integrable_residual_fourth_of_fourth_moments
    mu X Y b B hB hb hXMeas hYMeas hX4Int hY4Int
  have hUpperInt : Integrable (fun omega ↦
      8 * (Y omega) ^ 4 + 8 * B ^ 4 * (sqNorm (X omega)) ^ 2) mu :=
    (hY4Int.const_mul 8).add (hX4Int.const_mul (8 * B ^ 4))
  calc
    ∫ omega, (Y omega - vectorDot (X omega) b) ^ 4 ∂mu ≤
        ∫ omega, (8 * (Y omega) ^ 4 +
          8 * B ^ 4 * (sqNorm (X omega)) ^ 2) ∂mu := by
      apply integral_mono hResidualInt hUpperInt
      intro omega
      exact residual_fourth_le_of_sqNorm_le (X omega) b (Y omega) B hB hb
    _ = 8 * (∫ omega, (Y omega) ^ 4 ∂mu) +
        8 * B ^ 4 * (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) := by
      rw [integral_add (hY4Int.const_mul 8) (hX4Int.const_mul (8 * B ^ 4)),
        integral_const_mul, integral_const_mul]
    _ ≤ 8 * KY + 8 * B ^ 4 * KX := by
      exact add_le_add (mul_le_mul_of_nonneg_left hY4 (by norm_num))
        (mul_le_mul_of_nonneg_left hX4 (by positivity))

/-- Fixed-environment second-moment bound for the concrete primal oracle. -/
theorem integral_samplePrimalOracle_sqNorm_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {m p : ℕ}
    (gamma : ℝ) (e : Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ) (B KX KY : ℝ)
    (hB : 0 ≤ B) (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hb : sqNorm b ≤ B ^ 2)
    (hXMeas : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu)
    (hYMeas : AEStronglyMeasurable Y mu)
    (hX4Int : Integrable (fun omega ↦ (sqNorm (X omega)) ^ 2) mu)
    (hY4Int : Integrable (fun omega ↦ (Y omega) ^ 4) mu)
    (hX4 : (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) ≤ KX)
    (hY4 : (∫ omega, (Y omega) ^ 4 ∂mu) ≤ KY) :
    ∫ omega, sqNorm (samplePrimalOracle gamma e (X omega) (Y omega) b w) ∂mu ≤
      4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
        (2 * Real.sqrt (KY * KX) + 2 * B ^ 2 * KX) := by
  let C : ℝ := 4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hMixedInt := integrable_sqNorm_mul_sq_of_fourth_moments
    mu X Y hXMeas hYMeas hX4Int hY4Int
  have hMixed :
      (∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu) ≤
        Real.sqrt (KY * KX) := by
    simpa [mul_comm] using integral_sqNorm_mul_sq_le_sqrt_moment_bounds
      mu X Y KX KY hKX hKY hXMeas hYMeas hX4Int hY4Int hX4 hY4
  have hDotMeas := aestronglyMeasurable_vectorDot_left_of_coordinatewise X b hXMeas
  have hSqNormMeas := aestronglyMeasurable_sqNorm_of_coordinatewise X hXMeas
  have hOracleMeas : AEStronglyMeasurable (fun omega ↦
      sqNorm (samplePrimalOracle gamma e (X omega) (Y omega) b w)) mu := by
    have hRightMeas : AEStronglyMeasurable (fun omega ↦
        C * ((vectorDot (X omega) b - Y omega) ^ 2 * sqNorm (X omega))) mu :=
      aestronglyMeasurable_const.mul
        ((hDotMeas.sub hYMeas).pow 2 |>.mul hSqNormMeas)
    refine hRightMeas.congr (ae_of_all mu (fun omega ↦ ?_))
    symm
    change sqNorm (samplePrimalOracle gamma e (X omega) (Y omega) b w) =
      C * ((vectorDot (X omega) b - Y omega) ^ 2 * sqNorm (X omega))
    rw [samplePrimalOracle_sqNorm]
    dsimp [C]
    ring
  have hUpperInt : Integrable (fun omega ↦
      C * (2 * sqNorm (X omega) * (Y omega) ^ 2 +
        2 * B ^ 2 * (sqNorm (X omega)) ^ 2)) mu := by
    refine (((hMixedInt.const_mul 2).add
      (hX4Int.const_mul (2 * B ^ 2))).const_mul C).congr ?_
    exact ae_of_all mu (fun omega ↦ by
      change C * (2 * (sqNorm (X omega) * (Y omega) ^ 2) +
        2 * B ^ 2 * (sqNorm (X omega)) ^ 2) =
        C * (2 * sqNorm (X omega) * (Y omega) ^ 2 +
          2 * B ^ 2 * (sqNorm (X omega)) ^ 2)
      ring)
  have hOracleInt : Integrable (fun omega ↦
      sqNorm (samplePrimalOracle gamma e (X omega) (Y omega) b w)) mu := by
    refine hUpperInt.mono_nonneg hOracleMeas
      (ae_of_all mu (fun omega ↦ sqNorm_nonneg _)) ?_
    exact ae_of_all mu (fun omega ↦
      samplePrimalOracle_sqNorm_le gamma e (X omega) (Y omega) B b w hB hb)
  calc
    ∫ omega, sqNorm (samplePrimalOracle gamma e (X omega) (Y omega) b w) ∂mu ≤
        ∫ omega, C * (2 * sqNorm (X omega) * (Y omega) ^ 2 +
          2 * B ^ 2 * (sqNorm (X omega)) ^ 2) ∂mu := by
      apply integral_mono hOracleInt hUpperInt
      intro omega
      exact samplePrimalOracle_sqNorm_le gamma e (X omega) (Y omega) B b w hB hb
    _ = C * (2 * (∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu) +
        2 * B ^ 2 * (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu)) := by
      rw [integral_const_mul]
      have hInner :
          (∫ omega, (2 * sqNorm (X omega) * (Y omega) ^ 2 +
            2 * B ^ 2 * (sqNorm (X omega)) ^ 2) ∂mu) =
          2 * (∫ omega, sqNorm (X omega) * (Y omega) ^ 2 ∂mu) +
            2 * B ^ 2 * (∫ omega, (sqNorm (X omega)) ^ 2 ∂mu) := by
        rw [show (fun omega ↦ 2 * sqNorm (X omega) * (Y omega) ^ 2 +
            2 * B ^ 2 * (sqNorm (X omega)) ^ 2) =
            (fun omega ↦ 2 * (sqNorm (X omega) * (Y omega) ^ 2) +
              2 * B ^ 2 * (sqNorm (X omega)) ^ 2) by
          funext omega
          ring]
        rw [integral_add (hMixedInt.const_mul 2) (hX4Int.const_mul (2 * B ^ 2)),
          integral_const_mul, integral_const_mul]
      rw [hInner]
    _ ≤ C * (2 * Real.sqrt (KY * KX) + 2 * B ^ 2 * KX) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add (mul_le_mul_of_nonneg_left hMixed (by norm_num))
        (mul_le_mul_of_nonneg_left hX4 (by positivity))
    _ = 4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 *
        (2 * Real.sqrt (KY * KX) + 2 * B ^ 2 * KX) := by rfl

/-- Environment-averaged concrete primal-oracle second moment, including the exact cancellation
of one factor of `m` from the uniform `1/m` average. -/
theorem envAverage_integral_samplePrimalOracle_sqNorm_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {m p : ℕ}
    (gamma : ℝ) (X : Fin m → Omega → Fin p → ℝ) (Y : Fin m → Omega → ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ) (B KX KY : ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w)
    (hB : 0 ≤ B) (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hb : sqNorm b ≤ B ^ 2)
    (hXMeas : ∀ e i, AEStronglyMeasurable (fun omega ↦ X e omega i) mu)
    (hYMeas : ∀ e, AEStronglyMeasurable (Y e) mu)
    (hX4Int : ∀ e, Integrable (fun omega ↦ (sqNorm (X e omega)) ^ 2) mu)
    (hY4Int : ∀ e, Integrable (fun omega ↦ (Y e omega) ^ 4) mu)
    (hX4 : ∀ e, (∫ omega, (sqNorm (X e omega)) ^ 2 ∂mu) ≤ KX)
    (hY4 : ∀ e, (∫ omega, (Y e omega) ^ 4 ∂mu) ≤ KY) :
    envAverage m (fun e ↦
      ∫ omega, sqNorm (samplePrimalOracle gamma e (X e omega) (Y e omega) b w) ∂mu) ≤
        explicitPrimalGradSqBound m B KX KY := by
  let M : ℝ := 2 * Real.sqrt (KY * KX) + 2 * B ^ 2 * KX
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hEach : ∀ e,
      (∫ omega, sqNorm
        (samplePrimalOracle gamma e (X e omega) (Y e omega) b w) ∂mu) ≤
        4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 * M := by
    intro e
    exact integral_samplePrimalOracle_sqNorm_le mu gamma e (X e) (Y e) b w B KX KY
      hB hKX hKY hb (hXMeas e) (hYMeas e) (hX4Int e) (hY4Int e) (hX4 e) (hY4 e)
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun e _he ↦ hEach e)
  calc
    envAverage m (fun e ↦
        ∫ omega, sqNorm
          (samplePrimalOracle gamma e (X e omega) (Y e omega) b w) ∂mu) ≤
        (1 / (m : ℝ)) * ∑ e,
          4 * (m : ℝ) ^ 2 * (w e - negDROGammaCoefficient m gamma) ^ 2 * M := by
      exact mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = 4 * (m : ℝ) * M *
        ∑ e, (w e - negDROGammaCoefficient m gamma) ^ 2 := by
      rw [show (∑ e, 4 * (m : ℝ) ^ 2 *
          (w e - negDROGammaCoefficient m gamma) ^ 2 * M) =
          4 * (m : ℝ) ^ 2 * M *
            ∑ e, (w e - negDROGammaCoefficient m gamma) ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring]
      field_simp
    _ ≤ 4 * (m : ℝ) * M := by
      have hCoefficient : 0 ≤ 4 * (m : ℝ) * M :=
        mul_nonneg (mul_nonneg (by norm_num) hmReal.le) hM
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (shiftedCoefficient_sq_sum_le_one gamma w hm hgamma hw) hCoefficient
    _ = explicitPrimalGradSqBound m B KX KY := by rfl

/-- Scalar coordinate bound used by the unpenalized EG oracle. -/
def sampleDualCoordinateBound
    {p : ℕ} (m : ℕ) (x : Fin p → ℝ) (y : ℝ) (b : Fin p → ℝ) : ℝ :=
  (m : ℝ) * (y - vectorDot x b) ^ 2

/-- Scalar coordinate bound used by the penalized EG oracle. -/
def samplePenalizedDualCoordinateBound
    {p : ℕ} (m : ℕ) (penalty : ℝ) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) : ℝ :=
  sampleDualCoordinateBound m x y b + 2 * penalty

/-- The unpenalized sample coordinate bound has exactly the squared form used in the moment
calculation. -/
theorem sampleDualCoordinateBound_sq
    {p : ℕ} (m : ℕ) (x : Fin p → ℝ) (y : ℝ) (b : Fin p → ℝ) :
    (sampleDualCoordinateBound m x y b) ^ 2 =
      (m : ℝ) ^ 2 * (y - vectorDot x b) ^ 4 := by
  simp [sampleDualCoordinateBound]
  ring

/-- The scalar bound indeed supplies the concrete unpenalized dual coordinate interface. -/
theorem sampleUnpenalizedDualOracle_hasCoordinateAbsBound_explicit
    {m p : ℕ} (e : Fin m) (x : Fin p → ℝ) (y : ℝ) (b : Fin p → ℝ) :
    HasCoordinateAbsBound (sampleUnpenalizedDualOracle e x y b)
      (sampleDualCoordinateBound m x y b) :=
  sampleUnpenalizedDualOracle_hasCoordinateAbsBound e x y b

/-- The scalar bound indeed supplies the concrete penalized dual coordinate interface. -/
theorem samplePenalizedDualOracle_hasCoordinateAbsBound_explicit
    {m p : ℕ} (penalty : ℝ) (e : Fin m) (x : Fin p → ℝ) (y : ℝ)
    (b : Fin p → ℝ) (w : Fin m → ℝ)
    (hpenalty : 0 ≤ penalty) (hw : IsSimplex w) :
    HasCoordinateAbsBound (samplePenalizedDualOracle penalty e x y b w)
      (samplePenalizedDualCoordinateBound m penalty x y b) :=
  samplePenalizedDualOracle_hasCoordinateAbsBound penalty e x y b w hpenalty hw

/-- Environment-averaged second moment of the unpenalized dual coordinate-bound scalar. -/
theorem envAverage_integral_sampleDualCoordinateBound_sq_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega) {m p : ℕ}
    (X : Fin m → Omega → Fin p → ℝ) (Y : Fin m → Omega → ℝ)
    (b : Fin p → ℝ) (B KX KY : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2)
    (hXMeas : ∀ e i, AEStronglyMeasurable (fun omega ↦ X e omega i) mu)
    (hYMeas : ∀ e, AEStronglyMeasurable (Y e) mu)
    (hX4Int : ∀ e, Integrable (fun omega ↦ (sqNorm (X e omega)) ^ 2) mu)
    (hY4Int : ∀ e, Integrable (fun omega ↦ (Y e omega) ^ 4) mu)
    (hX4 : ∀ e, (∫ omega, (sqNorm (X e omega)) ^ 2 ∂mu) ≤ KX)
    (hY4 : ∀ e, (∫ omega, (Y e omega) ^ 4 ∂mu) ≤ KY) :
    envAverage m (fun e ↦
      ∫ omega, (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) ≤
        explicitUnpenalizedDualGradSqBound m B KX KY := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hEach : ∀ e,
      (∫ omega, (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) ≤
        (m : ℝ) ^ 2 * (8 * KY + 8 * B ^ 4 * KX) := by
    intro e
    simp_rw [sampleDualCoordinateBound_sq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_residual_fourth_le mu (X e) (Y e) b B KX KY hB hb
        (hXMeas e) (hYMeas e) (hX4Int e) (hY4Int e) (hX4 e) (hY4 e)) (by positivity)
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun e _he ↦ hEach e)
  calc
    envAverage m (fun e ↦
        ∫ omega, (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) ≤
        (1 / (m : ℝ)) * ∑ _e : Fin m,
          (m : ℝ) ^ 2 * (8 * KY + 8 * B ^ 4 * KX) := by
      exact mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = explicitUnpenalizedDualGradSqBound m B KX KY := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        explicitUnpenalizedDualGradSqBound]
      field_simp

/-- Pointwise scalar inequality used to pass from the unpenalized to penalized coordinate-bound
second moment. -/
theorem samplePenalizedDualCoordinateBound_sq_le
    {p : ℕ} (m : ℕ) (penalty : ℝ) (x : Fin p → ℝ) (y : ℝ) (b : Fin p → ℝ) :
    (samplePenalizedDualCoordinateBound m penalty x y b) ^ 2 ≤
      2 * (sampleDualCoordinateBound m x y b) ^ 2 + 8 * penalty ^ 2 := by
  dsimp [samplePenalizedDualCoordinateBound]
  nlinarith [sq_nonneg (sampleDualCoordinateBound m x y b - 2 * penalty)]

/-- Environment-averaged second moment of the penalized dual coordinate-bound scalar. -/
theorem envAverage_integral_samplePenalizedDualCoordinateBound_sq_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    [IsProbabilityMeasure mu] {m p : ℕ}
    (penalty : ℝ) (X : Fin m → Omega → Fin p → ℝ)
    (Y : Fin m → Omega → ℝ) (b : Fin p → ℝ) (B KX KY : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : sqNorm b ≤ B ^ 2)
    (hXMeas : ∀ e i, AEStronglyMeasurable (fun omega ↦ X e omega i) mu)
    (hYMeas : ∀ e, AEStronglyMeasurable (Y e) mu)
    (hX4Int : ∀ e, Integrable (fun omega ↦ (sqNorm (X e omega)) ^ 2) mu)
    (hY4Int : ∀ e, Integrable (fun omega ↦ (Y e omega) ^ 4) mu)
    (hX4 : ∀ e, (∫ omega, (sqNorm (X e omega)) ^ 2 ∂mu) ≤ KX)
    (hY4 : ∀ e, (∫ omega, (Y e omega) ^ 4 ∂mu) ≤ KY) :
    envAverage m (fun e ↦
      ∫ omega,
        (samplePenalizedDualCoordinateBound m penalty (X e omega) (Y e omega) b) ^ 2 ∂mu) ≤
        explicitPenalizedDualGradSqBound m penalty B KX KY := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hUnpen := envAverage_integral_sampleDualCoordinateBound_sq_le
    mu X Y b B KX KY hm hB hb hXMeas hYMeas hX4Int hY4Int hX4 hY4
  have hEachInt : ∀ e, Integrable (fun omega ↦
      (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2) mu := by
    intro e
    have hResidualInt := integrable_residual_fourth_of_fourth_moments
      mu (X e) (Y e) b B hB hb (hXMeas e) (hYMeas e) (hX4Int e) (hY4Int e)
    simpa only [sampleDualCoordinateBound_sq] using
      hResidualInt.const_mul ((m : ℝ) ^ 2)
  have hPenEach : ∀ e,
      (∫ omega,
        (samplePenalizedDualCoordinateBound m penalty (X e omega) (Y e omega) b) ^ 2 ∂mu) ≤
      2 * (∫ omega,
        (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) +
        8 * penalty ^ 2 := by
    intro e
    have hPenMeas : AEStronglyMeasurable (fun omega ↦
        (samplePenalizedDualCoordinateBound m penalty (X e omega) (Y e omega) b) ^ 2) mu := by
      have hDotMeas := aestronglyMeasurable_vectorDot_left_of_coordinatewise
        (X e) b (hXMeas e)
      have hResidualSq : AEStronglyMeasurable
          (fun omega ↦ (Y e omega - vectorDot (X e omega) b) ^ 2) mu :=
        ((hYMeas e).sub hDotMeas).pow 2
      have hSample : AEStronglyMeasurable (fun omega ↦
          sampleDualCoordinateBound m (X e omega) (Y e omega) b) mu := by
        exact aestronglyMeasurable_const.mul hResidualSq
      have hPenaltyConst : AEStronglyMeasurable (fun _ : Omega ↦ 2 * penalty) mu :=
        aestronglyMeasurable_const
      exact (hSample.add hPenaltyConst).pow 2
    have hUpperInt : Integrable (fun omega ↦
        2 * (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 +
          8 * penalty ^ 2) mu :=
      ((hEachInt e).const_mul 2).add (integrable_const (8 * penalty ^ 2))
    have hPenInt := hUpperInt.mono_nonneg hPenMeas
      (ae_of_all mu (fun omega ↦ by positivity))
      (ae_of_all mu (fun omega ↦
        samplePenalizedDualCoordinateBound_sq_le m penalty (X e omega) (Y e omega) b))
    calc
      ∫ omega,
          (samplePenalizedDualCoordinateBound m penalty (X e omega) (Y e omega) b) ^ 2 ∂mu ≤
          ∫ omega, (2 * (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 +
            8 * penalty ^ 2) ∂mu := by
        apply integral_mono hPenInt hUpperInt
        intro omega
        exact samplePenalizedDualCoordinateBound_sq_le m penalty
          (X e omega) (Y e omega) b
      _ = 2 * (∫ omega,
          (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) +
          8 * penalty ^ 2 := by
        rw [integral_add ((hEachInt e).const_mul 2) (integrable_const (8 * penalty ^ 2)),
          integral_const_mul]
        simp
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun e _he ↦ hPenEach e)
  calc
    envAverage m (fun e ↦
        ∫ omega,
          (samplePenalizedDualCoordinateBound m penalty (X e omega) (Y e omega) b) ^ 2 ∂mu) ≤
        envAverage m (fun e ↦
          2 * (∫ omega,
            (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) +
            8 * penalty ^ 2) := by
      exact mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = 2 * envAverage m (fun e ↦
          ∫ omega, (sampleDualCoordinateBound m (X e omega) (Y e omega) b) ^ 2 ∂mu) +
        8 * penalty ^ 2 := by
      simp only [envAverage, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ explicitPenalizedDualGradSqBound m penalty B KX KY := by
      dsimp [explicitPenalizedDualGradSqBound]
      dsimp [explicitUnpenalizedDualGradSqBound] at hUnpen
      linarith

end NegDRO
