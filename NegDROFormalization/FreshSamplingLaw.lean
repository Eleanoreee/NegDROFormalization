import NegDROFormalization.FreshSamplingConditionalOracles

/-!
# A genuine fresh conditional law for finite environments

The central interface quantifies over every integrable real test function of a fresh pair
`(X,Y)`.  Thus it specifies a conditional distribution, rather than listing the finitely many
monomials later needed by the optimization proof.  Testing with the constant function `1`
recovers uniform environment selection; arbitrary tests recover the fixed environment law and
its independence from the past sigma-algebra.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Apply a test function to the observed pair and select environment `e`. -/
def selectedEnvironmentTest
    {Omega : Type*} {m p : ℕ} (E : Omega → Fin m)
    (X : Omega → Fin p → ℝ) (Y : Omega → ℝ) (e : Fin m)
    (phi : (Fin p → ℝ) → ℝ → ℝ) : Omega → ℝ :=
  selectedEnvironmentTerm E e (fun omega ↦ phi (X omega) (Y omega))

/-- Conditional distribution/freshness interface for a uniform finite environment draw.

For every environment and every test function integrable under its fixed environment law, the
selected observed test is integrable and has conditional expectation `1/m` times the environment
expectation.  The quantifier over arbitrary tests is what makes this a law-level interface.
-/
structure HasFreshUniformFiniteEnvironmentLaw
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    (mu : Measure Omega) {m p : ℕ}
    (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (nu : Fin m → Measure SampleSpace)
    (Xenv : Fin m → SampleSpace → Fin p → ℝ)
    (Yenv : Fin m → SampleSpace → ℝ) : Prop where
  envIsProbability : ∀ e, IsProbabilityMeasure (nu e)
  xCoordinateMeasurable : ∀ i, AEStronglyMeasurable (fun omega ↦ X omega i) mu
  yMeasurable : AEStronglyMeasurable Y mu
  condLaw : ∀ (e : Fin m) (phi : (Fin p → ℝ) → ℝ → ℝ),
    Integrable (fun xi ↦ phi (Xenv e xi) (Yenv e xi)) (nu e) →
      Integrable (selectedEnvironmentTest E X Y e phi) mu ∧
      mu[selectedEnvironmentTest E X Y e phi | mCond] =ᵐ[mu]
        fun _ ↦ (1 / (m : ℝ)) *
          ∫ xi, phi (Xenv e xi) (Yenv e xi) ∂nu e

/-- Direct specialization of the universal test-function identity. -/
theorem freshLaw_condExp_selected
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (e : Fin m) (phi : (Fin p → ℝ) → ℝ → ℝ)
    (hInt : Integrable (fun xi ↦ phi (Xenv e xi) (Yenv e xi)) (nu e)) :
    Integrable (selectedEnvironmentTest E X Y e phi) mu ∧
    mu[selectedEnvironmentTest E X Y e phi | mCond] =ᵐ[mu]
      fun _ ↦ (1 / (m : ℝ)) *
        ∫ xi, phi (Xenv e xi) (Yenv e xi) ∂nu e :=
  hLaw.condLaw e phi hInt

/-- Testing the law with `1` shows that the conditional probability of each environment is
exactly `1/m`.  Probability normalization of `nu e` is essential for this conclusion. -/
theorem freshLaw_condExp_selectedEnvironmentIndicator
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (e : Fin m) :
    Integrable (selectedEnvironmentIndicator E e) mu ∧
    mu[selectedEnvironmentIndicator E e | mCond] =ᵐ[mu]
      fun _ ↦ 1 / (m : ℝ) := by
  letI : IsProbabilityMeasure (nu e) := hLaw.envIsProbability e
  have h := hLaw.condLaw e (fun _x _y ↦ (1 : ℝ)) (integrable_const 1)
  have hfun : selectedEnvironmentTest E X Y e (fun _x _y ↦ (1 : ℝ)) =
      selectedEnvironmentIndicator E e := by
    funext omega
    simp [selectedEnvironmentTest, selectedEnvironmentTerm]
  rw [hfun] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h

/-- Actual environment second moments associated with the law. -/
noncomputable def freshLawSigma
    {SampleSpace : Type*} {mSample : MeasurableSpace SampleSpace} {m p : ℕ}
    (nu : Fin m → Measure SampleSpace) (Xenv : Fin m → SampleSpace → Fin p → ℝ) :
    Fin m → Matrix (Fin p) (Fin p) ℝ :=
  fun e i j ↦ ∫ xi, Xenv e xi i * Xenv e xi j ∂nu e

/-- Actual environment `E[XY]` moments associated with the law. -/
noncomputable def freshLawCrossMoment
    {SampleSpace : Type*} {mSample : MeasurableSpace SampleSpace} {m p : ℕ}
    (nu : Fin m → Measure SampleSpace) (Xenv : Fin m → SampleSpace → Fin p → ℝ)
    (Yenv : Fin m → SampleSpace → ℝ) : Fin m → Fin p → ℝ :=
  fun e i ↦ ∫ xi, Xenv e xi i * Yenv e xi ∂nu e

/-- Actual environment `E[Y²]` moments associated with the law. -/
noncomputable def freshLawOutcomeMoment
    {SampleSpace : Type*} {mSample : MeasurableSpace SampleSpace} {m : ℕ}
    (nu : Fin m → Measure SampleSpace) (Yenv : Fin m → SampleSpace → ℝ) : Fin m → ℝ :=
  fun e ↦ ∫ xi, (Yenv e xi) ^ 2 ∂nu e

/-- Coordinate-product specialization, retaining the exact `1/m` factor. -/
theorem freshLaw_condExp_selected_coordinateProduct
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (e : Fin m) (i j : Fin p)
    (hInt : Integrable (fun xi ↦ Xenv e xi i * Xenv e xi j) (nu e)) :
    Integrable (selectedEnvironmentTerm E e (fun omega ↦ X omega i * X omega j)) mu ∧
    mu[selectedEnvironmentTerm E e (fun omega ↦ X omega i * X omega j) | mCond] =ᵐ[mu]
      fun _ ↦ (1 / (m : ℝ)) * freshLawSigma nu Xenv e i j := by
  simpa only [selectedEnvironmentTest, freshLawSigma] using
    hLaw.condLaw e (fun x _y ↦ x i * x j) hInt

/-- `XY` specialization of the universal conditional law. -/
theorem freshLaw_condExp_selected_XY
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (e : Fin m) (i : Fin p)
    (hInt : Integrable (fun xi ↦ Xenv e xi i * Yenv e xi) (nu e)) :
    Integrable (selectedEnvironmentTerm E e (fun omega ↦ X omega i * Y omega)) mu ∧
    mu[selectedEnvironmentTerm E e (fun omega ↦ X omega i * Y omega) | mCond] =ᵐ[mu]
      fun _ ↦ (1 / (m : ℝ)) * freshLawCrossMoment nu Xenv Yenv e i := by
  simpa only [selectedEnvironmentTest, freshLawCrossMoment] using
    hLaw.condLaw e (fun x y ↦ x i * y) hInt

/-- `Y²` specialization of the universal conditional law. -/
theorem freshLaw_condExp_selected_Ysq
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (e : Fin m) (hInt : Integrable (fun xi ↦ (Yenv e xi) ^ 2) (nu e)) :
    Integrable (selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 2)) mu ∧
    mu[selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 2) | mCond] =ᵐ[mu]
      fun _ ↦ (1 / (m : ℝ)) * freshLawOutcomeMoment nu Yenv e := by
  simpa only [selectedEnvironmentTest, freshLawOutcomeMoment] using
    hLaw.condLaw e (fun _x y ↦ y ^ 2) hInt

/-- The universal law implies the existing selected population-moment interface. -/
theorem freshLaw_toFreshPopulationMoments
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (hXX : ∀ e i j, Integrable (fun xi ↦ Xenv e xi i * Xenv e xi j) (nu e))
    (hXY : ∀ e i, Integrable (fun xi ↦ Xenv e xi i * Yenv e xi) (nu e))
    (hYSq : ∀ e, Integrable (fun xi ↦ (Yenv e xi) ^ 2) (nu e)) :
    HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond) mu E X Y
      (freshLawSigma nu Xenv) (freshLawCrossMoment nu Xenv Yenv)
      (freshLawOutcomeMoment nu Yenv) := by
  exact ⟨fun e i j ↦ (freshLaw_condExp_selected_coordinateProduct hLaw e i j (hXX e i j)).1,
    fun e i ↦ (freshLaw_condExp_selected_XY hLaw e i (hXY e i)).1,
    fun e ↦ (freshLaw_condExp_selected_Ysq hLaw e (hYSq e)).1,
    fun e i j ↦ (freshLaw_condExp_selected_coordinateProduct hLaw e i j (hXX e i j)).2,
    fun e i ↦ (freshLaw_condExp_selected_XY hLaw e i (hXY e i)).2,
    fun e ↦ (freshLaw_condExp_selected_Ysq hLaw e (hYSq e)).2⟩

/-- The universal law plus ordinary environment fourth moments implies the existing raw-moment
interface.  The mixed bound is derived by integral Cauchy--Schwarz, not assumed conditionally. -/
theorem freshLaw_toFreshRawMoments
    {Omega SampleSpace : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mSample : MeasurableSpace SampleSpace}
    {mu : Measure Omega} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    {nu : Fin m → Measure SampleSpace}
    {Xenv : Fin m → SampleSpace → Fin p → ℝ}
    {Yenv : Fin m → SampleSpace → ℝ}
    (KX KY : ℝ) (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y nu Xenv Yenv)
    (hXMeas : ∀ e i, AEStronglyMeasurable (fun xi ↦ Xenv e xi i) (nu e))
    (hYMeas : ∀ e, AEStronglyMeasurable (Yenv e) (nu e))
    (hX4Int : ∀ e, Integrable (fun xi ↦ (sqNorm (Xenv e xi)) ^ 2) (nu e))
    (hY4Int : ∀ e, Integrable (fun xi ↦ (Yenv e xi) ^ 4) (nu e))
    (hX4 : ∀ e, (∫ xi, (sqNorm (Xenv e xi)) ^ 2 ∂nu e) ≤ KX)
    (hY4 : ∀ e, (∫ xi, (Yenv e xi) ^ 4 ∂nu e) ≤ KY) :
    HasFreshFiniteEnvironmentRawMoments (mCond := mCond) mu E X Y KX KY := by
  let mixed : (Fin p → ℝ) → ℝ → ℝ := fun x y ↦ sqNorm x * y ^ 2
  let xFourth : (Fin p → ℝ) → ℝ → ℝ := fun x _y ↦ (sqNorm x) ^ 2
  let yFourth : (Fin p → ℝ) → ℝ → ℝ := fun _x y ↦ y ^ 4
  have hMixedInt : ∀ e, Integrable (fun xi ↦ mixed (Xenv e xi) (Yenv e xi)) (nu e) := by
    intro e
    exact integrable_sqNorm_mul_sq_of_fourth_moments (nu e) (Xenv e) (Yenv e)
      (hXMeas e) (hYMeas e) (hX4Int e) (hY4Int e)
  have hMixed : ∀ e,
      (∫ xi, mixed (Xenv e xi) (Yenv e xi) ∂nu e) ≤ Real.sqrt (KY * KX) := by
    intro e
    have h := integral_sqNorm_mul_sq_le_sqrt_moment_bounds (nu e) (Xenv e) (Yenv e)
      KX KY hKX hKY (hXMeas e) (hYMeas e) (hX4Int e) (hY4Int e)
      (hX4 e) (hY4 e)
    simpa only [mixed, mul_comm] using h
  have hMixedLaw : ∀ e,
      Integrable (selectedEnvironmentTest E X Y e mixed) mu ∧
      mu[selectedEnvironmentTest E X Y e mixed | mCond] =ᵐ[mu]
        fun _ ↦ (1 / (m : ℝ)) *
          ∫ xi, mixed (Xenv e xi) (Yenv e xi) ∂nu e :=
    fun e ↦ hLaw.condLaw e mixed (hMixedInt e)
  have hX4Law : ∀ e,
      Integrable (selectedEnvironmentTest E X Y e xFourth) mu ∧
      mu[selectedEnvironmentTest E X Y e xFourth | mCond] =ᵐ[mu]
        fun _ ↦ (1 / (m : ℝ)) *
          ∫ xi, xFourth (Xenv e xi) (Yenv e xi) ∂nu e :=
    fun e ↦ hLaw.condLaw e xFourth (hX4Int e)
  have hY4Law : ∀ e,
      Integrable (selectedEnvironmentTest E X Y e yFourth) mu ∧
      mu[selectedEnvironmentTest E X Y e yFourth | mCond] =ᵐ[mu]
        fun _ ↦ (1 / (m : ℝ)) *
          ∫ xi, yFourth (Xenv e xi) (Yenv e xi) ∂nu e :=
    fun e ↦ hLaw.condLaw e yFourth (hY4Int e)
  refine ⟨hLaw.xCoordinateMeasurable, hLaw.yMeasurable,
    fun e ↦ (hMixedLaw e).1, fun e ↦ (hX4Law e).1, fun e ↦ (hY4Law e).1,
    ?_, ?_, ?_⟩
  · intro e
    filter_upwards [(hMixedLaw e).2] with omega heq
    have heq' :
        mu[selectedEnvironmentTerm E e
          (fun omega ↦ sqNorm (X omega) * (Y omega) ^ 2) | mCond] omega =
          (1 / (m : ℝ)) *
            ∫ xi, sqNorm (Xenv e xi) * (Yenv e xi) ^ 2 ∂nu e := by
      simpa only [selectedEnvironmentTest, mixed] using heq
    rw [heq']
    exact mul_le_mul_of_nonneg_left (hMixed e) (by positivity)
  · intro e
    filter_upwards [(hX4Law e).2] with omega heq
    have heq' :
        mu[selectedEnvironmentTerm E e
          (fun omega ↦ (sqNorm (X omega)) ^ 2) | mCond] omega =
          (1 / (m : ℝ)) * ∫ xi, (sqNorm (Xenv e xi)) ^ 2 ∂nu e := by
      simpa only [selectedEnvironmentTest, xFourth] using heq
    rw [heq']
    exact mul_le_mul_of_nonneg_left (hX4 e) (by positivity)
  · intro e
    filter_upwards [(hY4Law e).2] with omega heq
    have heq' :
        mu[selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 4) | mCond] omega =
          (1 / (m : ℝ)) * ∫ xi, (Yenv e xi) ^ 4 ∂nu e := by
      simpa only [selectedEnvironmentTest, yFourth] using heq
    rw [heq']
    exact mul_le_mul_of_nonneg_left (hY4 e) (by positivity)

end NegDRO
