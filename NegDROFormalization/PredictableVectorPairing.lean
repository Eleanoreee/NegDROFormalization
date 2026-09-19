import NegDROFormalization.ConditionalExpectationScalar
import NegDROFormalization.QuadraticStructure

/-!
# Finite-vector predictable conditional-expectation pairing

This module lifts the one-sigma-algebra scalar bridge in
`ConditionalExpectationScalar.lean` to vectors indexed by `Fin p`. It uses the project's
explicit finite-coordinate `vectorDot`, never the default norm on a function space.

Two future instantiations are:

* `(gHat, F, d) = (gHat_t^b, grad_b L(b_t, w_t), b_t - betaStar)`;
* `(gHat, F, d) = (gHat_t^w, grad_w q_t(w_t), w0 - w_t)`.

They require predictability and boundedness of the displacement coordinates, not independence
between the primal and dual stochastic gradients. No filtration, time index, moment bound, or
algorithmic trajectory is defined here.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- The stochastic finite-coordinate pairing is integrable when every stochastic coordinate is
integrable and every predictable multiplier coordinate is a.e. strongly measurable and bounded
by the common scalar `bound`. -/
theorem integrable_vectorDot_of_coordinatewise_integrable_of_predictableBounded
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (hm : m ≤ mOmega)
    (gHat d : Omega → Fin p → ℝ)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hdMeas : ∀ i, AEStronglyMeasurable[m] (fun omega => d omega i) mu)
    (bound : ℝ)
    (hdBound : ∀ i, ∀ᵐ omega ∂mu, ‖d omega i‖ ≤ bound) :
    Integrable (fun omega => vectorDot (gHat omega) (d omega)) mu := by
  simp only [vectorDot]
  apply integrable_finsetSum Finset.univ
  intro i _hi
  have hdAmbient :
      AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
    (hdMeas i).mono hm
  exact (hgHatInt i).mul_bdd hdAmbient (hdBound i)

/-- A finite-vector conditional-unbiasedness identity obtained by expanding `vectorDot`, applying
the scalar predictable pull-out theorem coordinatewise, and exchanging finite sums with
integrals. Conditional unbiasedness remains an a.e. coordinatewise statement.

Population-coordinate integrability is derived from `integrable_condExp` and the supplied a.e.
equality; it is not an additional hypothesis. -/
theorem integral_vectorDot_eq_of_coordinatewise_condExp_ae_eq
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {p : ℕ} (hm : m ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (gHat F d : Omega → Fin p → ℝ)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hdMeas : ∀ i, AEStronglyMeasurable[m] (fun omega => d omega i) mu)
    (bound : ℝ)
    (hdBound : ∀ i, ∀ᵐ omega ∂mu, ‖d omega i‖ ≤ bound)
    (hCondUnbiased : ∀ i,
      (fun omega => F omega i) =ᵐ[mu]
        mu[(fun omega => gHat omega i) | m]) :
    (∫ omega, vectorDot (gHat omega) (d omega) ∂mu) =
      ∫ omega, vectorDot (F omega) (d omega) ∂mu := by
  have hgHatDInt : ∀ i,
      Integrable (fun omega => gHat omega i * d omega i) mu := by
    intro i
    have hdAmbient :
        AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
      (hdMeas i).mono hm
    exact (hgHatInt i).mul_bdd hdAmbient (hdBound i)
  have hFInt : ∀ i, Integrable (fun omega => F omega i) mu := by
    intro i
    have hCondInt :
        Integrable (mu[(fun omega => gHat omega i) | m]) mu :=
      integrable_condExp
    exact hCondInt.congr (hCondUnbiased i).symm
  have hFDInt : ∀ i,
      Integrable (fun omega => F omega i * d omega i) mu := by
    intro i
    have hdAmbient :
        AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
      (hdMeas i).mono hm
    exact (hFInt i).mul_bdd hdAmbient (hdBound i)
  have hCoordinateIntegral : ∀ i,
      (∫ omega, gHat omega i * d omega i ∂mu) =
        ∫ omega, F omega i * d omega i ∂mu := by
    intro i
    calc
      (∫ omega, gHat omega i * d omega i ∂mu) =
          ∫ omega, d omega i * gHat omega i ∂mu := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun omega => mul_comm _ _)
      _ = ∫ omega, d omega i * F omega i ∂mu :=
        integral_mul_eq_of_condExp_ae_eq hm
          (fun omega => gHat omega i) (fun omega => d omega i)
          (fun omega => F omega i) (hgHatInt i) (hdMeas i)
          bound (hdBound i) (hCondUnbiased i)
      _ = ∫ omega, F omega i * d omega i ∂mu := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun omega => mul_comm _ _)
  simp only [vectorDot]
  calc
    (∫ omega, ∑ i, gHat omega i * d omega i ∂mu) =
        ∑ i, ∫ omega, gHat omega i * d omega i ∂mu :=
      integral_finsetSum Finset.univ (fun i _hi => hgHatDInt i)
    _ = ∑ i, ∫ omega, F omega i * d omega i ∂mu := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hCoordinateIntegral i
    _ = ∫ omega, ∑ i, F omega i * d omega i ∂mu :=
      (integral_finsetSum Finset.univ (fun i _hi => hFDInt i)).symm

end NegDRO
