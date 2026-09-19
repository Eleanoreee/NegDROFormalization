import NegDROFormalization.SecondMomentMatrixBridge
import NegDROFormalization.FreshSamplingConditionalOracles

/-!
# Family-level interfaces for the corrected additive-intervention SEM

This module packages the model-level moments proved in
`AdditiveInterventionPopulationBridge` into the exact deterministic fields consumed by the
fresh-sampling convergence wrappers.  It does not identify model moments with the conditional
law of sampled observations: `HasFreshFiniteEnvironmentPopulationMoments` remains the separate
sampling-law premise.

The convention is the one forced by source Eq. (10): `GT` denotes mathematical `Gᵀ`, and
`X = GT (BYX * etaY + etaX + delta_e)`.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- The SEM second-moment matrix in each intervention environment. -/
noncomputable def additiveInterventionSigmaFamily
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ) (etaX : Omega → Fin p → ℝ)
    (delta : Fin m → Omega → Fin p → ℝ) :
    Fin m → Matrix (Fin p) (Fin p) ℝ :=
  fun e ↦ semSecondMoment mu GT BYX etaY etaX (delta e)

/-- The actual population `E[X Y]` vector in each realized intervention environment. -/
noncomputable def additiveInterventionCrossMomentFamily
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun e ↦ populationCrossMoment mu
    (fun omega ↦ semCovariate GT BYX (etaX omega) (delta e omega) (etaY omega))
    (semOutcome (fun omega ↦ semCovariate GT BYX
      (etaX omega) (delta e omega) (etaY omega)) betaStar etaY)

/-- The actual population `E[Y²]` scalar in each realized intervention environment. -/
noncomputable def additiveInterventionOutcomeMomentFamily
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ) :
    Fin m → ℝ :=
  fun e ↦ populationOutcomeSecondMoment mu
    (semOutcome (fun omega ↦ semCovariate GT BYX
      (etaX omega) (delta e omega) (etaY omega)) betaStar etaY)

/-- The corrected additive SEM automatically supplies `c_e = Sigma_e betaStar - v`. -/
theorem additiveInterventionFamily_hasCrossMomentRelation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments mu etaY etaX (delta e))
    (hZero : ∀ e, HasZeroSystematicInterventionCrossMoments mu etaY etaX (delta e)) :
    HasNegDROCrossMomentRelation
      (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta)
      (additiveInterventionCrossMomentFamily mu GT BYX betaStar etaY etaX delta)
      (semV mu GT BYX etaY etaX) betaStar := by
  intro e i
  exact additiveIntervention_crossMomentRelation GT BYX betaStar etaY etaX (delta e)
    (hInt e) (hZero e) i

/-- The corrected additive SEM automatically supplies the outcome-moment relation used by the
Appendix Lemma 1 risk expansion. -/
theorem additiveInterventionFamily_hasOutcomeMomentRelation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments mu etaY etaX (delta e))
    (hZero : ∀ e, HasZeroSystematicInterventionCrossMoments mu etaY etaX (delta e)) :
    HasNegDROOutcomeMomentRelation
      (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta)
      (additiveInterventionOutcomeMomentFamily mu GT BYX betaStar etaY etaX delta)
      (∫ omega, etaY omega * etaY omega ∂mu)
      (semV mu GT BYX etaY etaX) betaStar := by
  intro e
  exact additiveIntervention_outcomeMomentRelation GT BYX betaStar etaY etaX (delta e)
    (hInt e) (hZero e)

/-- Model second moments discharge the per-environment PSD interface in the common convergence
assumptions. -/
theorem additiveInterventionFamily_sigmaQuadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ) (etaX : Omega → Fin p → ℝ)
    (delta : Fin m → Omega → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments mu etaY etaX (delta e)) :
    ∀ e, QuadNonneg (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta e) := by
  exact semSecondMomentFamily_quadNonneg GT BYX etaY etaX delta hInt

/-- Model second moments discharge the symmetry interface in the sampling wrappers. -/
theorem additiveInterventionFamily_sigmaIsSymm
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ) (etaX : Omega → Fin p → ℝ)
    (delta : Fin m → Omega → Fin p → ℝ) :
    ∀ e, (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta e).IsSymm := by
  exact semSecondMomentFamily_isSymm mu GT BYX etaY etaX delta

/-- A compact bundle of exactly the four deterministic fields supplied by the SEM construction.
The witness curvature, projection, and sampling-law assumptions are intentionally absent. -/
theorem additiveInterventionFamily_deterministicInterfaces
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments mu etaY etaX (delta e))
    (hZero : ∀ e, HasZeroSystematicInterventionCrossMoments mu etaY etaX (delta e)) :
    (∀ e, QuadNonneg (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta e)) ∧
    (∀ e, (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta e).IsSymm) ∧
    HasNegDROCrossMomentRelation
      (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta)
      (additiveInterventionCrossMomentFamily mu GT BYX betaStar etaY etaX delta)
      (semV mu GT BYX etaY etaX) betaStar ∧
    HasNegDROOutcomeMomentRelation
      (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta)
      (additiveInterventionOutcomeMomentFamily mu GT BYX betaStar etaY etaX delta)
      (∫ omega, etaY omega * etaY omega ∂mu)
      (semV mu GT BYX etaY etaX) betaStar := by
  exact ⟨additiveInterventionFamily_sigmaQuadNonneg GT BYX etaY etaX delta hInt,
    additiveInterventionFamily_sigmaIsSymm mu GT BYX etaY etaX delta,
    additiveInterventionFamily_hasCrossMomentRelation GT BYX betaStar etaY etaX delta hInt hZero,
    additiveInterventionFamily_hasOutcomeMomentRelation GT BYX betaStar etaY etaX delta hInt hZero⟩

end NegDRO
