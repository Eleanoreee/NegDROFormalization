import NegDROFormalization.Simplex

/-!
# Finite-dimensional quadratic structure for the NegDRO fixed witness

Vectors are functions `Fin p → ℝ`, and matrices are actual values of type
`Matrix (Fin p) (Fin p) ℝ`. Positivity is stated directly through quadratic forms, which is
exactly the property used in Appendix equations (61)--(63); symmetry is not needed here.
-/

set_option autoImplicit false

namespace NegDRO

/-- Finite real-vector dot product. -/
def vectorDot {p : ℕ} (x y : Fin p → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- The quadratic form `xᵀ M x`, using Mathlib's matrix-vector multiplication `M *ᵥ x`. -/
def matrixQuad {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) : ℝ :=
  vectorDot x (Matrix.mulVec M x)

/-- A quadratic form is additive in its matrix argument. -/
theorem matrixQuad_add
    {p : ℕ} (M N : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) :
    matrixQuad (M + N) x = matrixQuad M x + matrixQuad N x := by
  rw [matrixQuad, Matrix.add_mulVec]
  simp [matrixQuad, vectorDot, mul_add, Finset.sum_add_distrib]

/-- A quadratic form commutes with real scalar multiplication of its matrix argument. -/
theorem matrixQuad_smul
    {p : ℕ} (a : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) :
    matrixQuad (a • M) x = a * matrixQuad M x := by
  rw [matrixQuad, Matrix.smul_mulVec]
  simp only [matrixQuad, vectorDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form of a finite matrix sum is the sum of the quadratic forms. -/
theorem matrixQuad_sum
    {ι : Type}
    {p : ℕ} (s : Finset ι) (M : ι → Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) :
    matrixQuad (∑ i ∈ s, M i) x = ∑ i ∈ s, matrixQuad (M i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixQuad, vectorDot, Matrix.mulVec]
  | @insert i s hi ih =>
      simp [hi, matrixQuad_add, ih]

/-- Quadratic-form nonnegativity, the precise PSD-like property needed in the paper. No
matrix symmetry is imposed. -/
def QuadNonneg {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ x, 0 ≤ matrixQuad M x

/-- `M` has quadratic curvature at least `lam` when `lam * sqNorm x ≤ xᵀ M x` for every
finite vector `x`. This is the precise lower-curvature property used by the fixed witness. -/
def CurvatureAtLeast {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (lam : ℝ) : Prop :=
  ∀ x, lam * sqNorm x ≤ matrixQuad M x

/-- The environmental average covariance `barSigma = (1/m) ∑ₑ Sigmaₑ`. Its intended use
requires `0 < m`; the definition itself remains a total matrix-valued function. -/
noncomputable def negDROAverageCovariance
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (1 / (m : ℝ)) • ∑ e, Sigma e

/-- The heterogeneity matrix `A(w) = ∑ₑ (wₑ - 1/m) Sigmaₑ`. It need not itself be a
covariance matrix or quadratically nonnegative. -/
noncomputable def negDROHeterogeneityMatrix
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ) (w : Fin m → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  ∑ e, (w e - 1 / (m : ℝ)) • Sigma e

/-- The coefficient `a_gamma = gamma / (1 + gamma m)`. -/
noncomputable def negDROGammaCoefficient (m : ℕ) (gamma : ℝ) : ℝ :=
  gamma / (1 + gamma * (m : ℝ))

/-- The covariance combination `Q(w) = ∑ₑ (wₑ - a_gamma) Sigmaₑ`. -/
noncomputable def negDROQ
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ e, (w e - negDROGammaCoefficient m gamma) • Sigma e

/-- Under the model assumptions `0 < m` and `0 ≤ gamma`, the denominator
`1 + gamma m` is strictly positive. -/
theorem negDRO_denominator_pos
    {m : ℕ} (gamma : ℝ) (hm : 0 < m) (hgamma : 0 ≤ gamma) :
    0 < 1 + gamma * (m : ℝ) := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hprod : 0 ≤ gamma * (m : ℝ) := mul_nonneg hgamma hmReal.le
  linarith

/-- The simplex coefficient identity used in Appendix Eq. (63):
`∑ₑ (wₑ - a_gamma) = 1 / (1 + gamma m)`. Denominator nonzeroness is derived from
`0 < m` and `0 ≤ gamma`, rather than assumed separately. -/
theorem negDRO_coefficient_sum
    {m : ℕ} {w : Fin m → ℝ} (gamma : ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    ∑ e, (w e - negDROGammaCoefficient m gamma) =
      1 / (1 + gamma * (m : ℝ)) := by
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  have hden : 1 + gamma * (m : ℝ) ≠ 0 := ne_of_gt hdenPos
  rw [Finset.sum_sub_distrib, hw.2]
  simp only [negDROGammaCoefficient, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hden]
  ring

/-- Appendix Eq. (61), as an actual matrix equality:
`Q(w) = A(w) + (1 / (1 + gamma m)) • barSigma`.

The assumption `0 < m` makes `1/m` valid, while `0 ≤ gamma` makes `1 + gamma m`
strictly positive. Simplex membership is not needed for this algebraic matrix decomposition. -/
theorem negDRO_q_decomposition
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) :
    negDROQ Sigma gamma w =
      negDROHeterogeneityMatrix Sigma w +
        (1 / (1 + gamma * (m : ℝ))) • negDROAverageCovariance Sigma := by
  classical
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  have hden : 1 + gamma * (m : ℝ) ≠ 0 := ne_of_gt hdenPos
  ext i j
  simp only [negDROQ, negDROHeterogeneityMatrix, negDROAverageCovariance,
    negDROGammaCoefficient, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
  have hscale :
      (∑ e, (1 / (1 + gamma * (m : ℝ))) * (1 / (m : ℝ)) * Sigma e i j) =
        (1 / (1 + gamma * (m : ℝ))) *
          ((1 / (m : ℝ)) * ∑ e, Sigma e i j) := by
    calc
      _ = ∑ e, (1 / (1 + gamma * (m : ℝ))) *
          ((1 / (m : ℝ)) * Sigma e i j) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = (1 / (1 + gamma * (m : ℝ))) *
          ∑ e, (1 / (m : ℝ)) * Sigma e i j := by
        rw [Finset.mul_sum]
      _ = (1 / (1 + gamma * (m : ℝ))) *
          ((1 / (m : ℝ)) * ∑ e, Sigma e i j) := by
        congr 1
        rw [Finset.mul_sum]
  calc
    (∑ e, (w e - gamma / (1 + gamma * (m : ℝ))) * Sigma e i j) =
        ∑ e, ((w e - 1 / (m : ℝ)) * Sigma e i j +
          (1 / (1 + gamma * (m : ℝ))) * (1 / (m : ℝ)) * Sigma e i j) := by
      apply Finset.sum_congr rfl
      intro e _
      field_simp [hmNe, hden]
      ring
    _ = (∑ e, (w e - 1 / (m : ℝ)) * Sigma e i j) +
        (1 / (1 + gamma * (m : ℝ))) *
          ((1 / (m : ℝ)) * ∑ e, Sigma e i j) := by
      rw [Finset.sum_add_distrib]
      rw [hscale]

/-- A positive scalar multiple of a quadratically nonnegative matrix remains quadratically
nonnegative. -/
theorem quadNonneg_smul
    {p : ℕ} (a : ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (ha : 0 ≤ a) (hM : QuadNonneg M) :
    QuadNonneg (a • M) := by
  intro x
  rw [matrixQuad_smul]
  exact mul_nonneg ha (hM x)

/-- If every environmental covariance is quadratically nonnegative, then their average
covariance is quadratically nonnegative. -/
theorem averageCovariance_quadNonneg
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (hm : 0 < m) (hSigma : ∀ e, QuadNonneg (Sigma e)) :
    QuadNonneg (negDROAverageCovariance Sigma) := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  intro x
  rw [negDROAverageCovariance, matrixQuad_smul, matrixQuad_sum]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun e _ ↦ hSigma e x))

/-- With `0 < m` and `0 ≤ gamma`, the scaled average term in Eq. (61) is quadratically
nonnegative. -/
theorem scaledAverageCovariance_quadNonneg
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (hm : 0 < m) (hgamma : 0 ≤ gamma)
    (hSigma : ∀ e, QuadNonneg (Sigma e)) :
    QuadNonneg
      ((1 / (1 + gamma * (m : ℝ))) • negDROAverageCovariance Sigma) := by
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  exact quadNonneg_smul _ _ (by positivity) (averageCovariance_quadNonneg Sigma hm hSigma)

/-- Fixed-witness curvature transfer:
`Q(w⁰) = A(w⁰) + barSigma/(1 + gamma m)` from Eq. (61), and the added average-covariance
term is quadratically nonnegative. Hence curvature at least `lam` transfers from `A(w⁰)` to
`Q(w⁰)`. No positivity assumption is made on `A(w)` for any other weight vector. -/
theorem fixedWitness_curvature_transfer
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma lam : ℝ) (w₀ : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w₀) lam) :
    CurvatureAtLeast (negDROQ Sigma gamma w₀) lam := by
  have hdecomp := negDRO_q_decomposition Sigma gamma w₀ hm hgamma
  have hscaled := scaledAverageCovariance_quadNonneg Sigma gamma hm hgamma hSigma
  intro x
  rw [hdecomp, matrixQuad_add]
  nlinarith [hcurvature x, hscaled x]

end NegDRO
