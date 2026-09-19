import NegDROFormalization.FreshSamplingLaw
import NegDROFormalization.AdditiveInterventionPopulationInterfaces

/-!
# Identification of fresh-sampling moments with corrected additive-SEM moments

The environment law below uses exactly the same random variables and measure as the realized
additive-intervention SEM.  Consequently its `Sigma`, `c`, and `q` are not parallel postulated
objects: they reduce to the existing model integrals.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- Environment covariate used simultaneously by the sampling law and the SEM bridge. -/
def additiveInterventionEnvironmentX
    {Noise : Type*} {m p : ℕ} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) : Fin m → Noise → Fin p → ℝ :=
  fun e xi ↦ semCovariate GT BYX (etaX xi) (delta e xi) (etaY xi)

/-- Environment outcome from the same realized structural equation. -/
def additiveInterventionEnvironmentY
    {Noise : Type*} {m p : ℕ} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) : Fin m → Noise → ℝ :=
  fun e ↦ semOutcome (additiveInterventionEnvironmentX GT BYX etaY etaX delta e)
    betaStar etaY

/-- The sampling-law covariance is definitionally the SEM covariance family. -/
theorem freshLawSigma_eq_additiveInterventionSigmaFamily
    {Noise : Type*} {mNoise : MeasurableSpace Noise} {m p : ℕ}
    (nu : Measure Noise) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) :
    freshLawSigma (fun _ ↦ nu)
        (additiveInterventionEnvironmentX GT BYX etaY etaX delta) =
      additiveInterventionSigmaFamily nu GT BYX etaY etaX delta := by
  rfl

/-- The sampling-law `E[XY]` family is the actual SEM population cross moment. -/
theorem freshLawCrossMoment_eq_additiveInterventionCrossMomentFamily
    {Noise : Type*} {mNoise : MeasurableSpace Noise} {m p : ℕ}
    (nu : Measure Noise) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) :
    freshLawCrossMoment (fun _ ↦ nu)
        (additiveInterventionEnvironmentX GT BYX etaY etaX delta)
        (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta) =
      additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta := by
  rfl

/-- The sampling-law `E[Y²]` family is the actual SEM outcome moment. -/
theorem freshLawOutcomeMoment_eq_additiveInterventionOutcomeMomentFamily
    {Noise : Type*} {mNoise : MeasurableSpace Noise} {m p : ℕ}
    (nu : Measure Noise) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ) :
    freshLawOutcomeMoment (fun _ ↦ nu)
        (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta) =
      additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta := by
  rfl

/-- A fresh conditional law whose environment maps are the SEM maps supplies the old population
moment interface with exactly the SEM `Sigma`, `c`, and `q`. -/
theorem additiveInterventionFreshLaw_toFreshPopulationMoments
    {Omega Noise : Type*}
    {mCond mOmega : MeasurableSpace Omega} {mNoise : MeasurableSpace Noise}
    {mu : Measure Omega} {nu : Measure Noise} {m p : ℕ}
    {E : Omega → Fin m} {X : Omega → Fin p → ℝ} {Y : Omega → ℝ}
    (GT : Matrix (Fin p) (Fin p) ℝ) (BYX betaStar : Fin p → ℝ)
    (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (hLaw : HasFreshUniformFiniteEnvironmentLaw (mCond := mCond) mu E X Y
      (fun _ ↦ nu) (additiveInterventionEnvironmentX GT BYX etaY etaX delta)
      (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta))
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments nu etaY etaX (delta e)) :
    HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond) mu E X Y
      (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta)
      (additiveInterventionCrossMomentFamily nu GT BYX betaStar etaY etaX delta)
      (additiveInterventionOutcomeMomentFamily nu GT BYX betaStar etaY etaX delta) := by
  have hMom : ∀ e, HasIntegrablePopulationQuadraticMonomials nu
      (additiveInterventionEnvironmentX GT BYX etaY etaX delta e)
      (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta e) := by
    intro e
    exact sem_hasIntegrablePopulationQuadraticMonomials GT BYX betaStar etaY etaX
      (delta e) (hInt e)
  have h := freshLaw_toFreshPopulationMoments hLaw
    (fun e i j ↦ (hMom e).xx i j) (fun e i ↦ (hMom e).xy i)
    (fun e ↦ (hMom e).ySq)
  simpa only [freshLawSigma_eq_additiveInterventionSigmaFamily,
    freshLawCrossMoment_eq_additiveInterventionCrossMomentFamily,
    freshLawOutcomeMoment_eq_additiveInterventionOutcomeMomentFamily] using h

/-- Sampling `c` is automatically `Sigma betaStar - vSEM`. -/
theorem additiveInterventionSampling_hasCrossMomentRelation
    {Noise : Type*} {mNoise : MeasurableSpace Noise} {m p : ℕ}
    {nu : Measure Noise} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments nu etaY etaX (delta e))
    (hZero : ∀ e, HasZeroSystematicInterventionCrossMoments nu etaY etaX (delta e)) :
    HasNegDROCrossMomentRelation
      (freshLawSigma (fun _ ↦ nu)
        (additiveInterventionEnvironmentX GT BYX etaY etaX delta))
      (freshLawCrossMoment (fun _ ↦ nu)
        (additiveInterventionEnvironmentX GT BYX etaY etaX delta)
        (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta))
      (semV nu GT BYX etaY etaX) betaStar := by
  simpa only [freshLawSigma_eq_additiveInterventionSigmaFamily,
    freshLawCrossMoment_eq_additiveInterventionCrossMomentFamily] using
    additiveInterventionFamily_hasCrossMomentRelation GT BYX betaStar etaY etaX delta hInt hZero

/-- Sampling `q` automatically has the corrected SEM outcome-moment expansion. -/
theorem additiveInterventionSampling_hasOutcomeMomentRelation
    {Noise : Type*} {mNoise : MeasurableSpace Noise} {m p : ℕ}
    {nu : Measure Noise} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments nu etaY etaX (delta e))
    (hZero : ∀ e, HasZeroSystematicInterventionCrossMoments nu etaY etaX (delta e)) :
    HasNegDROOutcomeMomentRelation
      (freshLawSigma (fun _ ↦ nu)
        (additiveInterventionEnvironmentX GT BYX etaY etaX delta))
      (freshLawOutcomeMoment (fun _ ↦ nu)
        (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta))
      (∫ xi, etaY xi * etaY xi ∂nu) (semV nu GT BYX etaY etaX) betaStar := by
  simpa only [freshLawSigma_eq_additiveInterventionSigmaFamily,
    freshLawOutcomeMoment_eq_additiveInterventionOutcomeMomentFamily] using
    additiveInterventionFamily_hasOutcomeMomentRelation GT BYX betaStar etaY etaX delta hInt hZero

/-- Every environment squared loss is the already proved expanded environmental risk. -/
theorem additiveInterventionSampling_environmentRisk_eq_expanded
    {Noise : Type*} {mNoise : MeasurableSpace Noise} {m p : ℕ}
    {nu : Measure Noise} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar b : Fin p → ℝ) (etaY : Noise → ℝ) (etaX : Noise → Fin p → ℝ)
    (delta : Fin m → Noise → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments nu etaY etaX (delta e))
    (hZero : ∀ e, HasZeroSystematicInterventionCrossMoments nu etaY etaX (delta e))
    (e : Fin m) :
    finitePopulationSquaredRisk nu
      (additiveInterventionEnvironmentX GT BYX etaY etaX delta e)
      (additiveInterventionEnvironmentY GT BYX betaStar etaY etaX delta e) b =
      expandedEnvironmentalRisk (∫ xi, etaY xi * etaY xi ∂nu)
        (semV nu GT BYX etaY etaX) b betaStar
        (additiveInterventionSigmaFamily nu GT BYX etaY etaX delta e) := by
  exact additiveIntervention_populationRisk_eq_expandedEnvironmentalRisk GT BYX betaStar b
    etaY etaX (delta e) (hInt e) (hZero e)

end NegDRO
