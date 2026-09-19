import NegDROFormalization.PredictableVectorPairing
import NegDROFormalization.PrimalProjectionRecursion

/-!
# One-round expected primal recursion

This module lifts one a.e. pathwise projected-primal squared-distance recursion to an expected
recursion under a single conditioning sigma-algebra. It uses coordinatewise conditional
unbiasedness for the direction pairing and a scalar conditional second-moment bound.

A future trajectory proof will instantiate, at each round `t`, the conditioning space as
`F_(t-1)`, `b` as `b_t`, `bPlus` as `b_(t+1)`, `gHat` as `gHat_t^b`, and `F` as
`grad_b L(b_t, w_t)`. The proof requires predictability of `b_t - betaStar`, but no independence
between primal and dual stochastic gradients. No filtration, complete trajectory, dual update,
moment constant, or convergence theorem is defined here.
-/

set_option autoImplicit false

open MeasureTheory
open scoped MeasureTheory

namespace NegDRO

/-- Expected explicit coordinate squared distance. -/
noncomputable def expectedSqDist
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {p : ℕ} (b : Omega → Fin p → ℝ) (betaStar : Fin p → ℝ)
    (mu : Measure Omega) : ℝ :=
  ∫ omega, sqDist (b omega) betaStar ∂mu

/-- Expected finite-coordinate population direction pairing. -/
noncomputable def expectedDirection
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {p : ℕ} (F d : Omega → Fin p → ℝ) (mu : Measure Omega) : ℝ :=
  ∫ omega, vectorDot (F omega) (d omega) ∂mu

/-- Expected realized coordinate squared gradient norm. -/
noncomputable def expectedGradSq
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {p : ℕ} (gHat : Omega → Fin p → ℝ) (mu : Measure Omega) : ℝ :=
  ∫ omega, sqNorm (gHat omega) ∂mu

/-- A conditional a.e. upper bound implies the corresponding ordinary integral bound under a
probability measure. The conditional inequality is never strengthened to a pointwise one. -/
theorem integral_le_const_of_condExp_ae_le
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] (hm : m ≤ mOmega)
    (X : Omega → ℝ) (M : ℝ) (_hX : Integrable X mu)
    (hCondBound : mu[X | m] ≤ᵐ[mu] fun _ => M) :
    (∫ omega, X omega ∂mu) ≤ M := by
  have hCondInt : Integrable (mu[X | m]) mu := integrable_condExp
  have hConstInt : Integrable (fun _ : Omega => M) mu := integrable_const M
  have hIntegrated :
      (∫ omega, (mu[X | m]) omega ∂mu) ≤
        ∫ _omega : Omega, M ∂mu :=
    integral_mono_ae hCondInt hConstInt hCondBound
  rw [integral_condExp hm] at hIntegrated
  simpa using hIntegrated

/-- Exact one-round expected primal recursion. The input recursion is a genuinely a.e. pathwise
statement; the stochastic pairing is replaced by its population pairing using coordinatewise
conditional unbiasedness and predictability of the displacement. No sign condition on `eta` is
needed. -/
theorem expected_primal_recursion_exact
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (hm : m ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (b bPlus gHat F : Omega → Fin p → ℝ) (betaStar : Fin p → ℝ)
    (eta : ℝ)
    (hPathwise : ∀ᵐ omega ∂mu,
      sqDist (bPlus omega) betaStar ≤
        sqDist (b omega) betaStar -
          2 * eta * vectorDot (gHat omega)
            (primalDisplacement (b omega) betaStar) +
          eta ^ 2 * sqNorm (gHat omega))
    (hNextDistInt : Integrable (fun omega => sqDist (bPlus omega) betaStar) mu)
    (hCurrentDistInt : Integrable (fun omega => sqDist (b omega) betaStar) mu)
    (hGradSqInt : Integrable (fun omega => sqNorm (gHat omega)) mu)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[m]
        (fun omega => primalDisplacement (b omega) betaStar i) mu)
    (displacementBound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement (b omega) betaStar i‖ ≤ displacementBound)
    (hCondUnbiased : ∀ i,
      (fun omega => F omega i) =ᵐ[mu]
        mu[(fun omega => gHat omega i) | m]) :
    expectedSqDist (mOmega := mOmega) bPlus betaStar mu ≤
      expectedSqDist (mOmega := mOmega) b betaStar mu -
        2 * eta * expectedDirection (mOmega := mOmega) F
          (fun omega => primalDisplacement (b omega) betaStar) mu +
        eta ^ 2 * expectedGradSq (mOmega := mOmega) gHat mu := by
  let d : Omega → Fin p → ℝ :=
    fun omega => primalDisplacement (b omega) betaStar
  have hStochasticPairInt :
      Integrable (fun omega => vectorDot (gHat omega) (d omega)) mu :=
    integrable_vectorDot_of_coordinatewise_integrable_of_predictableBounded
      hm gHat d hgHatInt hDisplacementMeas displacementBound hDisplacementBound
  have hFInt : ∀ i, Integrable (fun omega => F omega i) mu := by
    intro i
    have hCondInt :
        Integrable (mu[(fun omega => gHat omega i) | m]) mu :=
      integrable_condExp
    exact hCondInt.congr (hCondUnbiased i).symm
  have hPopulationPairInt :
      Integrable (fun omega => vectorDot (F omega) (d omega)) mu := by
    simp only [vectorDot]
    apply integrable_finsetSum Finset.univ
    intro i _hi
    have hdAmbient :
        AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
      (hDisplacementMeas i).mono hm
    exact (hFInt i).mul_bdd hdAmbient (hDisplacementBound i)
  have hScaledPairInt :
      Integrable (fun omega => 2 * eta * vectorDot (gHat omega) (d omega)) mu :=
    hStochasticPairInt.const_mul (2 * eta)
  have hScaledGradInt :
      Integrable (fun omega => eta ^ 2 * sqNorm (gHat omega)) mu :=
    hGradSqInt.const_mul (eta ^ 2)
  have hRightInt : Integrable (fun omega =>
      sqDist (b omega) betaStar -
        2 * eta * vectorDot (gHat omega) (d omega) +
        eta ^ 2 * sqNorm (gHat omega)) mu :=
    (hCurrentDistInt.sub hScaledPairInt).add hScaledGradInt
  have hIntegrated :
      (∫ omega, sqDist (bPlus omega) betaStar ∂mu) ≤
        ∫ omega,
          (sqDist (b omega) betaStar -
            2 * eta * vectorDot (gHat omega) (d omega) +
            eta ^ 2 * sqNorm (gHat omega)) ∂mu :=
    integral_mono_ae hNextDistInt hRightInt (by
      filter_upwards [hPathwise] with omega homega
      simpa [d] using homega)
  have hRightIntegral :
      (∫ omega,
          (sqDist (b omega) betaStar -
            2 * eta * vectorDot (gHat omega) (d omega) +
            eta ^ 2 * sqNorm (gHat omega)) ∂mu) =
        (∫ omega, sqDist (b omega) betaStar ∂mu) -
          2 * eta * (∫ omega, vectorDot (gHat omega) (d omega) ∂mu) +
          eta ^ 2 * (∫ omega, sqNorm (gHat omega) ∂mu) := by
    calc
      _ = (∫ omega,
            (sqDist (b omega) betaStar -
              2 * eta * vectorDot (gHat omega) (d omega)) ∂mu) +
            ∫ omega, eta ^ 2 * sqNorm (gHat omega) ∂mu :=
        integral_add (hCurrentDistInt.sub hScaledPairInt) hScaledGradInt
      _ = ((∫ omega, sqDist (b omega) betaStar ∂mu) -
            ∫ omega, 2 * eta * vectorDot (gHat omega) (d omega) ∂mu) +
            ∫ omega, eta ^ 2 * sqNorm (gHat omega) ∂mu := by
        rw [integral_sub hCurrentDistInt hScaledPairInt]
      _ = (∫ omega, sqDist (b omega) betaStar ∂mu) -
          2 * eta * (∫ omega, vectorDot (gHat omega) (d omega) ∂mu) +
          eta ^ 2 * (∫ omega, sqNorm (gHat omega) ∂mu) := by
        rw [integral_const_mul, integral_const_mul]
  have hPairing :
      (∫ omega, vectorDot (gHat omega) (d omega) ∂mu) =
        ∫ omega, vectorDot (F omega) (d omega) ∂mu :=
    integral_vectorDot_eq_of_coordinatewise_condExp_ae_eq
      hm gHat F d hgHatInt hDisplacementMeas displacementBound
      hDisplacementBound hCondUnbiased
  rw [hRightIntegral] at hIntegrated
  rw [hPairing] at hIntegrated
  simpa [expectedSqDist, expectedDirection, expectedGradSq, d] using hIntegrated

/-- Ordinary expected-squared-gradient specialization. `gradSqBound` already denotes a squared
quantity and is not squared again. Only nonnegativity of `eta^2` is used to scale the moment
inequality. -/
theorem expected_primal_recursion_of_expectedSqNorm_le
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (hm : m ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (b bPlus gHat F : Omega → Fin p → ℝ) (betaStar : Fin p → ℝ)
    (eta gradSqBound : ℝ)
    (hPathwise : ∀ᵐ omega ∂mu,
      sqDist (bPlus omega) betaStar ≤
        sqDist (b omega) betaStar -
          2 * eta * vectorDot (gHat omega)
            (primalDisplacement (b omega) betaStar) +
          eta ^ 2 * sqNorm (gHat omega))
    (hNextDistInt : Integrable (fun omega => sqDist (bPlus omega) betaStar) mu)
    (hCurrentDistInt : Integrable (fun omega => sqDist (b omega) betaStar) mu)
    (hGradSqInt : Integrable (fun omega => sqNorm (gHat omega)) mu)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[m]
        (fun omega => primalDisplacement (b omega) betaStar i) mu)
    (displacementBound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement (b omega) betaStar i‖ ≤ displacementBound)
    (hCondUnbiased : ∀ i,
      (fun omega => F omega i) =ᵐ[mu]
        mu[(fun omega => gHat omega i) | m])
    (hExpectedGradSq :
      expectedGradSq (mOmega := mOmega) gHat mu ≤ gradSqBound) :
    expectedSqDist (mOmega := mOmega) bPlus betaStar mu ≤
      expectedSqDist (mOmega := mOmega) b betaStar mu -
        2 * eta * expectedDirection (mOmega := mOmega) F
          (fun omega => primalDisplacement (b omega) betaStar) mu +
        eta ^ 2 * gradSqBound := by
  have hExact := expected_primal_recursion_exact hm b bPlus gHat F betaStar eta
    hPathwise hNextDistInt hCurrentDistInt hGradSqInt hgHatInt
    hDisplacementMeas displacementBound hDisplacementBound hCondUnbiased
  have hScaledMoment :
      eta ^ 2 * expectedGradSq (mOmega := mOmega) gHat mu ≤
        eta ^ 2 * gradSqBound :=
    mul_le_mul_of_nonneg_left hExpectedGradSq (sq_nonneg eta)
  linarith

/-- Conditional second-moment specialization under a probability measure. The scalar a.e.
conditional moment bound is first converted to an ordinary expectation bound; it is never
reinterpreted as a pathwise bound on `sqNorm (gHat omega)`. -/
theorem expected_primal_recursion_of_condExpectedSqNorm_le
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} [IsProbabilityMeasure mu] (hm : m ≤ mOmega)
    (b bPlus gHat F : Omega → Fin p → ℝ) (betaStar : Fin p → ℝ)
    (eta gradSqBound : ℝ)
    (hPathwise : ∀ᵐ omega ∂mu,
      sqDist (bPlus omega) betaStar ≤
        sqDist (b omega) betaStar -
          2 * eta * vectorDot (gHat omega)
            (primalDisplacement (b omega) betaStar) +
          eta ^ 2 * sqNorm (gHat omega))
    (hNextDistInt : Integrable (fun omega => sqDist (bPlus omega) betaStar) mu)
    (hCurrentDistInt : Integrable (fun omega => sqDist (b omega) betaStar) mu)
    (hGradSqInt : Integrable (fun omega => sqNorm (gHat omega)) mu)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[m]
        (fun omega => primalDisplacement (b omega) betaStar i) mu)
    (displacementBound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement (b omega) betaStar i‖ ≤ displacementBound)
    (hCondUnbiased : ∀ i,
      (fun omega => F omega i) =ᵐ[mu]
        mu[(fun omega => gHat omega i) | m])
    (hCondGradSq :
      mu[(fun omega => sqNorm (gHat omega)) | m] ≤ᵐ[mu]
        fun _ => gradSqBound) :
    expectedSqDist (mOmega := mOmega) bPlus betaStar mu ≤
      expectedSqDist (mOmega := mOmega) b betaStar mu -
        2 * eta * expectedDirection (mOmega := mOmega) F
          (fun omega => primalDisplacement (b omega) betaStar) mu +
        eta ^ 2 * gradSqBound := by
  have hExpectedGradSq :
      expectedGradSq (mOmega := mOmega) gHat mu ≤ gradSqBound := by
    simpa [expectedGradSq] using
      (integral_le_const_of_condExp_ae_le hm
        (fun omega => sqNorm (gHat omega)) gradSqBound hGradSqInt hCondGradSq)
  exact expected_primal_recursion_of_expectedSqNorm_le hm
    b bPlus gHat F betaStar eta gradSqBound hPathwise
    hNextDistInt hCurrentDistInt hGradSqInt hgHatInt hDisplacementMeas
    displacementBound hDisplacementBound hCondUnbiased hExpectedGradSq

end NegDRO
