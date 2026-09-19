import NegDROFormalization.AdditiveInterventionPopulationBridge

/-!
# Symmetry and PSD-interface propagation for actual second moments

This module transports symmetry of actual coordinate second-moment matrices to the matrix
combinations used by NegDRO.  It deliberately does not claim that the heterogeneity matrix or
`negDROQ` is positive semidefinite: their scalar coefficients can be negative.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- A finite sum of symmetric square matrices is symmetric. -/
theorem finset_sum_isSymm
    {ι : Type*} {p : ℕ} (s : Finset ι)
    (M : ι → Matrix (Fin p) (Fin p) ℝ)
    (hM : ∀ i ∈ s, (M i).IsSymm) :
    (∑ i ∈ s, M i).IsSymm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hM i (Finset.mem_insert_self i s)).add
        (ih (fun j hj ↦ hM j (Finset.mem_insert_of_mem hj)))

/-- The average of symmetric environmental second-moment matrices is symmetric. -/
theorem averageCovariance_isSymm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (hSigma : ∀ e, (Sigma e).IsSymm) :
    (negDROAverageCovariance Sigma).IsSymm := by
  unfold negDROAverageCovariance
  exact (finset_sum_isSymm Finset.univ Sigma (fun e _he ↦ hSigma e)).smul _

/-- The signed heterogeneity matrix is symmetric.  No PSD conclusion is asserted. -/
theorem negDROHeterogeneityMatrix_isSymm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (w : Fin m → ℝ) (hSigma : ∀ e, (Sigma e).IsSymm) :
    (negDROHeterogeneityMatrix Sigma w).IsSymm := by
  unfold negDROHeterogeneityMatrix
  exact finset_sum_isSymm Finset.univ
    (fun e ↦ (w e - 1 / (m : ℝ)) • Sigma e)
    (fun e _he ↦ (hSigma e).smul _)

/-- The shifted covariance combination `negDROQ` is symmetric.  Its signed coefficients do not
permit a general PSD conclusion. -/
theorem negDROQ_isSymm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ) (hSigma : ∀ e, (Sigma e).IsSymm) :
    (negDROQ Sigma gamma w).IsSymm := by
  unfold negDROQ
  exact finset_sum_isSymm Finset.univ
    (fun e ↦ (w e - negDROGammaCoefficient m gamma) • Sigma e)
    (fun e _he ↦ (hSigma e).smul _)

/-- A family of actual population second moments automatically supplies the existing
`QuadNonneg` interface. -/
theorem populationSecondMomentFamily_quadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : Fin m → Measure Omega) (X : Fin m → Omega → Fin p → ℝ)
    (hXX : ∀ e i j, Integrable (fun omega ↦ X e omega i * X e omega j) (mu e)) :
    ∀ e, QuadNonneg (populationSecondMomentMatrix (mu e) (X e)) := by
  intro e
  exact populationSecondMomentMatrix_quadNonneg (mu e) (X e) (hXX e)

/-- A family of actual SEM covariances automatically supplies the existing per-environment
`QuadNonneg` premise. -/
theorem semSecondMomentFamily_quadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ)
    (hInt : ∀ e, HasIntegrableAdditiveInterventionMoments mu etaY etaX (delta e)) :
    ∀ e, QuadNonneg (semSecondMoment mu GT BYX etaY etaX (delta e)) := by
  intro e
  exact semSecondMoment_quadNonneg GT BYX etaY etaX (delta e) (hInt e)

/-- The same SEM family is symmetric coordinatewise. -/
theorem semSecondMomentFamily_isSymm
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) (delta : Fin m → Omega → Fin p → ℝ) :
    ∀ e, (semSecondMoment mu GT BYX etaY etaX (delta e)).IsSymm := by
  intro e
  exact semSecondMoment_symmetric mu GT BYX etaY etaX (delta e)

end NegDRO
