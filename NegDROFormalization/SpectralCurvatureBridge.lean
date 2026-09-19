import NegDROFormalization.SecondMomentMatrixBridge
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral lower bounds imply project curvature

For a real symmetric finite matrix, Mathlib's Hermitian spectral theorem supplies actual
eigenvalues.  A common lower bound on all of those eigenvalues makes `A - lambda I` positive
semidefinite, which is then converted to the project's explicit coordinate quadratic form.
-/

set_option autoImplicit false

namespace NegDRO

/-- A lower bound on every Mathlib eigenvalue makes the shifted symmetric matrix PSD. -/
theorem shifted_posSemidef_of_le_eigenvalues
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (lam : ℝ)
    (hA : A.IsSymm)
    (hlam : ∀ i, lam ≤
      (Matrix.isHermitian_iff_isSymm.mpr hA).eigenvalues i) :
    (A - lam • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef := by
  let hHerm : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  let U := hHerm.eigenvectorUnitary
  let d : Fin p → ℝ := fun i ↦ hHerm.eigenvalues i - lam
  have hd : ∀ i, 0 ≤ d i := fun i ↦ sub_nonneg.mpr (hlam i)
  have hdiag : (Matrix.diagonal d).PosSemidef := Matrix.PosSemidef.diagonal hd
  have hU : IsUnit (U : Matrix (Fin p) (Fin p) ℝ) := Unitary.isUnit_coe
  have hconj :
      ((U : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal d *
        star (U : Matrix (Fin p) (Fin p) ℝ)).PosSemidef :=
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU).mpr hdiag
  have hshift : A - lam • (1 : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal d *
        star (U : Matrix (Fin p) (Fin p) ℝ) := by
    rw [hHerm.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    change (U : Matrix (Fin p) (Fin p) ℝ) *
        Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) *
          star (U : Matrix (Fin p) (Fin p) ℝ) -
            lam • (1 : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal d *
        star (U : Matrix (Fin p) (Fin p) ℝ)
    have hdmat : Matrix.diagonal d =
        Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) -
          lam • (1 : Matrix (Fin p) (Fin p) ℝ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [d]
      · simp [Matrix.diagonal_apply, hij, d]
    have hscale : (U : Matrix (Fin p) (Fin p) ℝ) *
        (lam • (1 : Matrix (Fin p) (Fin p) ℝ)) *
          star (U : Matrix (Fin p) (Fin p) ℝ) =
        lam • (1 : Matrix (Fin p) (Fin p) ℝ) := by
      calc
        (U : Matrix (Fin p) (Fin p) ℝ) * (lam • 1) *
            star (U : Matrix (Fin p) (Fin p) ℝ) =
            (lam • (U : Matrix (Fin p) (Fin p) ℝ)) *
              star (U : Matrix (Fin p) (Fin p) ℝ) := by simp
        _ = lam • ((U : Matrix (Fin p) (Fin p) ℝ) *
              star (U : Matrix (Fin p) (Fin p) ℝ)) := by
          rw [Matrix.smul_mul]
        _ = lam • 1 := by
          have hunit : (U : Matrix (Fin p) (Fin p) ℝ) *
              star (U : Matrix (Fin p) (Fin p) ℝ) = 1 := U.prop.2
          rw [hunit]
    rw [hdmat, mul_sub, sub_mul, hscale]
  rw [hshift]
  exact hconj

/-- Genuine spectral-to-curvature bridge.  The hypothesis is a lower bound on Mathlib's
eigenvalues, not the desired quadratic inequality under another name.  It also covers `p = 0`
vacuously. -/
theorem curvatureAtLeast_of_le_eigenvalues
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (lam : ℝ)
    (hA : A.IsSymm)
    (hlam : ∀ i, lam ≤
      (Matrix.isHermitian_iff_isSymm.mpr hA).eigenvalues i) :
    CurvatureAtLeast A lam := by
  have hPSD := shifted_posSemidef_of_le_eigenvalues A lam hA hlam
  intro z
  have hz := hPSD.dotProduct_mulVec_nonneg z
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul] at hz
  have hz' : 0 ≤ matrixQuad A z - lam * sqNorm z := by
    simpa [matrixQuad, vectorDot, sqNorm, dotProduct, pow_two] using hz
  exact sub_nonneg.mp hz'

end NegDRO
