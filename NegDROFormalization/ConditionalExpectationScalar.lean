import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Scalar predictable pull-out for one conditioning sigma-algebra

This module is a one-sigma-algebra scalar bridge. For an integrable real random variable `X`
and a bounded multiplier `Z` measurable with respect to a conditioning sigma-algebra `m`, it
proves that multiplying by `Z` commutes with replacing `X` by its conditional expectation at
the level of integrals.

Later, applying this result coordinatewise and summing over finitely many coordinates will give
`E <gHat_t, d_t> = E <E[gHat_t | F_(t-1)], d_t>` when `d_t` is predictable and bounded. No
conditional independence is required. This module defines neither a filtration nor a stochastic
process and contains no finite-dimensional dot-product statement.
-/

set_option autoImplicit false

open MeasureTheory
open scoped MeasureTheory

namespace NegDRO

/-- A bounded predictable real multiplier may be pulled across conditional expectation inside
an integral. The relation `hm : m ≤ mOmega` explicitly says that the conditioning measurable
space is a sub-sigma-algebra of the ambient one.

The hypotheses derive integrability of both displayed products. The theorem is stated for the
slightly more general situation in which the trimmed measure is sigma-finite; probability and
finite measures provide this condition. -/
theorem integral_mul_condExp_of_predictable
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (hm : m ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (X Z : Omega → ℝ)
    (hX : Integrable X mu)
    (hZ : AEStronglyMeasurable[m] Z mu)
    (bound : ℝ) (hZBound : ∀ᵐ omega ∂mu, ‖Z omega‖ ≤ bound) :
    (∫ omega, Z omega * X omega ∂mu) =
      ∫ omega, Z omega * (mu[X | m]) omega ∂mu := by
  have hZAmbient : AEStronglyMeasurable[mOmega] Z mu := hZ.mono hm
  have hZX : Integrable (fun omega => Z omega * X omega) mu :=
    hX.bdd_mul hZAmbient hZBound
  have hCondX : Integrable (mu[X | m]) mu := integrable_condExp
  have _hZCondX : Integrable (fun omega => Z omega * (mu[X | m]) omega) mu :=
    hCondX.bdd_mul hZAmbient hZBound
  have hPullOut :
      mu[fun omega => Z omega * X omega | m] =ᵐ[mu]
        fun omega => Z omega * (mu[X | m]) omega :=
    condExp_mul_of_aestronglyMeasurable_left hZ hZX hX
  calc
    (∫ omega, Z omega * X omega ∂mu) =
        ∫ omega, (mu[fun omega => Z omega * X omega | m]) omega ∂mu := by
      symm
      exact integral_condExp hm
    _ = ∫ omega, Z omega * (mu[X | m]) omega ∂mu :=
      integral_congr_ae hPullOut

/-- Conditional-unbiasedness specialization. If `F` is almost everywhere equal to the
conditional expectation of `X`, then every bounded predictable multiplier gives the same
integral pairing with `X` and `F`.

The equality hypothesis is deliberately almost-everywhere equality, not pointwise equality. -/
theorem integral_mul_eq_of_condExp_ae_eq
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (hm : m ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (X Z F : Omega → ℝ)
    (hX : Integrable X mu)
    (hZ : AEStronglyMeasurable[m] Z mu)
    (bound : ℝ) (hZBound : ∀ᵐ omega ∂mu, ‖Z omega‖ ≤ bound)
    (hF : F =ᵐ[mu] mu[X | m]) :
    (∫ omega, Z omega * X omega ∂mu) =
      ∫ omega, Z omega * F omega ∂mu := by
  have hZAmbient : AEStronglyMeasurable[mOmega] Z mu := hZ.mono hm
  have hCondX : Integrable (mu[X | m]) mu := integrable_condExp
  have hFInt : Integrable F mu := hCondX.congr hF.symm
  have _hZF : Integrable (fun omega => Z omega * F omega) mu :=
    hFInt.bdd_mul hZAmbient hZBound
  calc
    (∫ omega, Z omega * X omega ∂mu) =
        ∫ omega, Z omega * (mu[X | m]) omega ∂mu :=
      integral_mul_condExp_of_predictable hm X Z hX hZ bound hZBound
    _ = ∫ omega, Z omega * F omega ∂mu := by
      apply integral_congr_ae
      filter_upwards [hF] with omega homega
      rw [homega]

end NegDRO
