import NegDROFormalization.SpectralCurvatureBridge
import NegDROFormalization.AdditiveInterventionPopulationInterfaces

/-!
# Spectral witness interface

This interface records symmetry and a lower bound on Mathlib's actual Hermitian eigenvalues.  It
does not contain the project's quadratic curvature conclusion.
-/

set_option autoImplicit false

namespace NegDRO

/-- A genuine spectral lower-bound condition on the NegDRO witness matrix. -/
structure SpectralWitnessAtLeast
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (w0 : Fin m → ℝ) (lam : ℝ) : Prop where
  isSymm : (negDROHeterogeneityMatrix Sigma w0).IsSymm
  eigenvalueLower : ∀ i, lam ≤
    (Matrix.isHermitian_iff_isSymm.mpr isSymm).eigenvalues i

/-- The spectral witness condition implies the existing quadratic curvature interface. -/
theorem SpectralWitnessAtLeast.curvatureAtLeast
    {m p : ℕ} {Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ}
    {w0 : Fin m → ℝ} {lam : ℝ}
    (h : SpectralWitnessAtLeast Sigma w0 lam) :
    CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam :=
  curvatureAtLeast_of_le_eigenvalues _ _ h.isSymm h.eigenvalueLower

/-- For the additive SEM family, symmetry is derived; the caller supplies only the genuine
eigenvalue lower bound. -/
theorem additiveInterventionFamily_spectralWitnessAtLeast
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {m p : ℕ}
    (mu : MeasureTheory.Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ) (etaX : Omega → Fin p → ℝ)
    (delta : Fin m → Omega → Fin p → ℝ) (w0 : Fin m → ℝ) (lam : ℝ)
    (hEigen : ∀ i, lam ≤
      (Matrix.isHermitian_iff_isSymm.mpr
        (negDROHeterogeneityMatrix_isSymm
          (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta) w0
          (additiveInterventionFamily_sigmaIsSymm mu GT BYX etaY etaX delta))).eigenvalues i) :
    SpectralWitnessAtLeast
      (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta) w0 lam := by
  exact ⟨negDROHeterogeneityMatrix_isSymm
      (additiveInterventionSigmaFamily mu GT BYX etaY etaX delta) w0
      (additiveInterventionFamily_sigmaIsSymm mu GT BYX etaY etaX delta),
    hEigen⟩

end NegDRO
