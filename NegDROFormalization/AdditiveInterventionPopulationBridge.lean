import NegDROFormalization.PopulationRiskMomentBridge

/-!
# Additive-intervention population bridge, with the source sign audited

The source is arXiv:2412.11850v3, Section 3.1 and Appendix E.1.  Equation (10) says

`Y = betaStarᵀ X + epsilonY` and
`X = BYX Y + BXX X + epsilonX`.

Consequently, for
`S = (I - BXX) - BYX betaStarᵀ`, direct substitution gives

`S X = BYX epsilonY + epsilonX`.

Thus, if `GT` is the inverse of `S`, the mathematically forced formula is

`X = GT (BYX epsilonY + epsilonX)`.

In particular the lower-left block of `(I-B)⁻¹` is **`+ GT BYX`**.  Appendix E.1,
Eq. (97), prints `- GT BYX`; that sign contradicts Eq. (10).  The contradiction is already
visible in the scalar specialization `betaStar = 0`, `BXX = 0`, `BYX = c`, where
`[[1,0],[-c,1]]⁻¹ = [[1,0],[c,1]]`.

The same Appendix subsequently prints negative cross terms in `H`, while its displayed PSD
factorization with the block column `[BYX; I]` produces positive cross terms under ordinary
matrix multiplication.  This module therefore follows Eq. (10), using the corrected positive
convention throughout; it does not formalize the inconsistent printed convention.

Equation (12) is equality *in distribution*.  Here `etaY`, `etaX`, and `delta` are an explicit
realization/coupling on one probability space.  No theorem below silently turns equality in
distribution into pointwise equality.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- Explicit finite-coordinate outer product. -/
def outerProduct {p : ℕ} (x y : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ x i * y j

/-- Explicit matrix product.  Naming it avoids the competing pointwise multiplication instance
for function types when matrices are written as lambdas. -/
def matrixProduct {p : ℕ} (A B : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i k ↦ ∑ j, A i j * B j k

theorem matrixProduct_mulVec {p : ℕ} (A B : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin p → ℝ) :
    Matrix.mulVec (matrixProduct A B) x = Matrix.mulVec A (Matrix.mulVec B x) := by
  funext i
  simp only [matrixProduct, Matrix.mulVec, dotProduct]
  calc
    (∑ k, (∑ j, A i j * B j k) * x k) =
        ∑ k, ∑ j, (A i j * B j k) * x k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ = ∑ j, ∑ k, (A i j * B j k) * x k := Finset.sum_comm
    _ = ∑ j, A i j * ∑ k, B j k * x k := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- The Schur matrix forced by source Eq. (10): `I - BXX - BYX betaStarᵀ`. -/
def semSchurMatrix {p : ℕ} (BXX : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  1 - BXX - outerProduct BYX betaStar

/-- Systematic covariate noise under the sign convention forced by Eq. (10). -/
def systematicCovariateNoise {p : ℕ} (BYX etaX : Fin p → ℝ) (etaY : ℝ) :
    Fin p → ℝ :=
  fun i ↦ BYX i * etaY + etaX i

/-- The realized Eq. (12) covariate noise, systematic noise plus intervention. -/
def intervenedCovariateNoise {p : ℕ} (BYX etaX delta : Fin p → ℝ) (etaY : ℝ) :
    Fin p → ℝ :=
  fun i ↦ systematicCovariateNoise BYX etaX etaY i + delta i

/-- Covariate generated from the explicitly oriented inverse `GT = Gᵀ`. -/
def semCovariate {p : ℕ} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX etaX delta : Fin p → ℝ) (etaY : ℝ) : Fin p → ℝ :=
  Matrix.mulVec GT (intervenedCovariateNoise BYX etaX delta etaY)

/-- Coordinate form of `S X = BYX epsilonY + epsilonX`, derived from the two structural
equations rather than assumed as a block-inverse identity. -/
theorem semSchur_mulVec
    {p : ℕ} (BXX : Matrix (Fin p) (Fin p) ℝ) (BYX betaStar X epsilonX : Fin p → ℝ)
    (Y epsilonY : ℝ)
    (hY : Y = vectorDot betaStar X + epsilonY)
    (hX : X = fun i ↦ BYX i * Y + Matrix.mulVec BXX X i + epsilonX i) :
    Matrix.mulVec (semSchurMatrix BXX BYX betaStar) X =
      fun i ↦ BYX i * epsilonY + epsilonX i := by
  rw [semSchurMatrix, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  have hXi := congrFun hX i
  rw [hY] at hXi
  change X i = BYX i * ((∑ j, betaStar j * X j) + epsilonY) +
    (∑ j, BXX i j * X j) + epsilonX i at hXi
  simp only [Pi.sub_apply, outerProduct, Matrix.mulVec, dotProduct]
  have hOuter : (∑ j, BYX i * betaStar j * X j) =
      BYX i * ∑ j, betaStar j * X j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hOuter]
  nlinarith

/-- Direct elimination plus a left-inverse condition gives the corrected covariate formula.
Only `GT S = I` is needed in this direction. -/
theorem semCovariate_eq_of_structuralEquations
    {p : ℕ} (BXX GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar X epsilonX : Fin p → ℝ) (Y epsilonY : ℝ)
    (hInv : matrixProduct GT (semSchurMatrix BXX BYX betaStar) = 1)
    (hY : Y = vectorDot betaStar X + epsilonY)
    (hX : X = fun i ↦ BYX i * Y + Matrix.mulVec BXX X i + epsilonX i) :
    X = Matrix.mulVec GT (fun i ↦ BYX i * epsilonY + epsilonX i) := by
  have hS := semSchur_mulVec BXX BYX betaStar X epsilonX Y epsilonY hY hX
  calc
    X = Matrix.mulVec (1 : Matrix (Fin p) (Fin p) ℝ) X := by
      simp
    _ = Matrix.mulVec (matrixProduct GT (semSchurMatrix BXX BYX betaStar)) X := by rw [hInv]
    _ = Matrix.mulVec GT
        (Matrix.mulVec (semSchurMatrix BXX BYX betaStar) X) := by
      rw [matrixProduct_mulVec]
    _ = Matrix.mulVec GT (fun i ↦ BYX i * epsilonY + epsilonX i) := by rw [hS]

/-- Eq. (10) plus the realized Eq. (12) decomposition gives the concrete `semCovariate`.
The equalities for the noises are realization/coupling hypotheses, not claims that equality in
distribution is pointwise equality. -/
theorem semCovariate_eq_inverseNoise
    {p : ℕ} (BXX GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar X epsilonX etaX delta : Fin p → ℝ)
    (Y epsilonY etaY : ℝ)
    (hInv : matrixProduct GT (semSchurMatrix BXX BYX betaStar) = 1)
    (hY : Y = vectorDot betaStar X + epsilonY)
    (hX : X = fun i ↦ BYX i * Y + Matrix.mulVec BXX X i + epsilonX i)
    (hEpsilonY : epsilonY = etaY)
    (hEpsilonX : epsilonX = fun i ↦ etaX i + delta i) :
    X = semCovariate GT BYX etaX delta etaY := by
  rw [semCovariate_eq_of_structuralEquations BXX GT BYX betaStar X epsilonX Y epsilonY
    hInv hY hX]
  subst epsilonY
  subst epsilonX
  rw [semCovariate]
  congr 1
  funext i
  simp only [intervenedCovariateNoise, systematicCovariateNoise]
  ring

/-- Formal scalar countercheck for the source sign: the printed lower-left `-c` cannot be the
inverse entry, while `+c` is. -/
theorem scalar_block_inverse_sign_audit (c : ℝ) :
    matrixProduct ((fun i j : Fin 2 ↦ if i = 0 then (if j = 0 then 1 else 0)
      else (if j = 0 then -c else 1)) : Matrix (Fin 2) (Fin 2) ℝ)
      ((fun i j : Fin 2 ↦ if i = 0 then (if j = 0 then 1 else 0)
        else (if j = 0 then c else 1)) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixProduct, Fin.sum_univ_two]

/-- Actual systematic second moment `Hplus = E[U Uᵀ]`, where
`U = BYX etaY + etaX`. -/
noncomputable def systematicSecondMoment
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  populationSecondMomentMatrix mu
    (fun omega ↦ systematicCovariateNoise BYX (etaX omega) (etaY omega))

/-- Actual intervention second moment `Delta = E[delta deltaᵀ]`. -/
noncomputable def interventionSecondMoment
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (delta : Omega → Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  populationSecondMomentMatrix mu delta

/-- The actual SEM covariate second moment. -/
noncomputable def semSecondMoment
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  populationSecondMomentMatrix mu
    (fun omega ↦ semCovariate GT BYX (etaX omega) (delta omega) (etaY omega))

/-- Primitive integrability assumptions needed to distribute finite sums through all moments. -/
structure HasIntegrableAdditiveInterventionMoments
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ) : Prop where
  etaYSq : Integrable (fun omega ↦ etaY omega * etaY omega) mu
  etaYEtaX : ∀ i, Integrable (fun omega ↦ etaY omega * etaX omega i) mu
  etaYDelta : ∀ i, Integrable (fun omega ↦ etaY omega * delta omega i) mu
  etaXPair : ∀ i j, Integrable (fun omega ↦ etaX omega i * etaX omega j) mu
  etaXDelta : ∀ i j, Integrable (fun omega ↦ etaX omega i * delta omega j) mu
  deltaEtaX : ∀ i j, Integrable (fun omega ↦ delta omega i * etaX omega j) mu
  deltaPair : ∀ i j, Integrable (fun omega ↦ delta omega i * delta omega j) mu

/-- Orthogonality in the realized Eq. (12), including the outcome-noise row and all covariate
rows of `E[eta deltaᵀ] = 0`. -/
structure HasZeroSystematicInterventionCrossMoments
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ) : Prop where
  etaYDelta : ∀ j, ∫ omega, etaY omega * delta omega j ∂mu = 0
  etaXDelta : ∀ i j, ∫ omega, etaX omega i * delta omega j ∂mu = 0
  deltaEtaX : ∀ i j, ∫ omega, delta omega i * etaX omega j ∂mu = 0

/-- Corrected source vector `E[etaY (BYX etaY + etaX)]`. -/
noncomputable def systematicCrossMomentVector
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) : Fin p → ℝ :=
  fun i ↦ (∫ omega, etaY omega * etaY omega ∂mu) * BYX i +
    ∫ omega, etaY omega * etaX omega i ∂mu

/-- Every actual coordinate second-moment matrix is symmetric. -/
theorem populationSecondMomentMatrix_symmetric
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ) :
    (populationSecondMomentMatrix mu X).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [populationSecondMomentMatrix, Matrix.transpose_apply]
  apply integral_congr_ae
  filter_upwards [] with omega
  ring

/-- An actual coordinate second-moment matrix is quadratically nonnegative.  Coordinate-product
integrability is used only to exchange the finite sums and the integral. -/
theorem populationSecondMomentMatrix_quadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (X : Omega → Fin p → ℝ)
    (hXX : ∀ i j, Integrable (fun omega ↦ X omega i * X omega j) mu) :
    QuadNonneg (populationSecondMomentMatrix mu X) := by
  intro z
  have hTerms : ∀ i j, Integrable (fun omega ↦
      (z i * z j) * (X omega i * X omega j)) mu :=
    fun i j ↦ (hXX i j).const_mul (z i * z j)
  have hEq : matrixQuad (populationSecondMomentMatrix mu X) z =
      ∫ omega, (vectorDot (X omega) z) ^ 2 ∂mu := by
    rw [show (fun omega ↦ (vectorDot (X omega) z) ^ 2) =
        (fun omega ↦ ∑ i, ∑ j,
          (z i * z j) * (X omega i * X omega j)) by
      funext omega
      rw [vectorDot, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hTerms i j))]
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ hTerms _ j)]
    simp_rw [integral_const_mul]
    simp only [matrixQuad, vectorDot, populationSecondMomentMatrix, Matrix.mulVec,
      dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hEq]
  exact integral_nonneg_of_ae (ae_of_all mu fun omega ↦ sq_nonneg _)

/-- Integrability of all systematic-noise coordinate products. -/
theorem integrable_systematicCovariateNoise_pair
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (i j : Fin p) :
    Integrable (fun omega ↦
      systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
      systematicCovariateNoise BYX (etaX omega) (etaY omega) j) mu := by
  have h1 := hInt.etaYSq.const_mul (BYX i * BYX j)
  have h2 := (hInt.etaYEtaX j).const_mul (BYX i)
  have h3 : Integrable (fun omega ↦ BYX j * (etaY omega * etaX omega i)) mu :=
    (hInt.etaYEtaX i).const_mul (BYX j)
  have h4 := hInt.etaXPair i j
  have hsum := h1.add h2 |>.add h3 |>.add h4
  refine hsum.congr (ae_of_all mu fun omega ↦ ?_)
  change BYX i * BYX j * (etaY omega * etaY omega) +
      BYX i * (etaY omega * etaX omega j) +
      BYX j * (etaY omega * etaX omega i) + etaX omega i * etaX omega j = _
  simp only [systematicCovariateNoise]
  ring

/-- Integrability of all intervened-noise coordinate products. -/
theorem integrable_intervenedCovariateNoise_pair
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (i j : Fin p) :
    Integrable (fun omega ↦
      intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) i *
      intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j) mu := by
  have hU := integrable_systematicCovariateNoise_pair BYX etaY etaX delta hInt i j
  have hUD : Integrable (fun omega ↦
      systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j) mu := by
    have h1 := (hInt.etaYDelta j).const_mul (BYX i)
    have hsum := h1.add (hInt.etaXDelta i j)
    refine hsum.congr (ae_of_all mu fun omega ↦ ?_)
    change BYX i * (etaY omega * delta omega j) + etaX omega i * delta omega j = _
    simp only [systematicCovariateNoise]
    ring
  have hDU : Integrable (fun omega ↦ delta omega i *
      systematicCovariateNoise BYX (etaX omega) (etaY omega) j) mu := by
    have h1 : Integrable (fun omega ↦ BYX j * (etaY omega * delta omega i)) mu :=
      (hInt.etaYDelta i).const_mul (BYX j)
    have hsum := h1.add (hInt.deltaEtaX i j)
    refine hsum.congr (ae_of_all mu fun omega ↦ ?_)
    change BYX j * (etaY omega * delta omega i) + delta omega i * etaX omega j = _
    simp only [systematicCovariateNoise]
    ring
  have hsum := hU.add hUD |>.add hDU |>.add (hInt.deltaPair i j)
  refine hsum.congr (ae_of_all mu fun omega ↦ ?_)
  change systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
      systematicCovariateNoise BYX (etaX omega) (etaY omega) j +
      systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j +
      delta omega i * systematicCovariateNoise BYX (etaX omega) (etaY omega) j +
      delta omega i * delta omega j = _
  simp only [intervenedCovariateNoise]
  ring

/-- The corrected cross moment, proved from the actual random variables and the orthogonality
rows of Eq. (12): `E[X etaY] = GT (sigmaYSq BYX + crossEta)`. -/
theorem sem_crossMoment_eq
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (hZero : HasZeroSystematicInterventionCrossMoments mu etaY etaX delta) :
    populationCrossMoment mu
      (fun omega ↦ semCovariate GT BYX (etaX omega) (delta omega) (etaY omega)) etaY =
      Matrix.mulVec GT (systematicCrossMomentVector mu BYX etaY etaX) := by
  funext i
  have hTerm : ∀ j, Integrable (fun omega ↦ GT i j *
      (intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j *
        etaY omega)) mu := by
    intro j
    have hBase : Integrable (fun omega ↦
        intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j *
          etaY omega) mu := by
      have h1 := (hInt.etaYSq.const_mul (BYX j))
      have h2 : Integrable (fun omega ↦ etaX omega j * etaY omega) mu :=
        (hInt.etaYEtaX j).congr (ae_of_all mu fun omega ↦ by ring)
      have h3 : Integrable (fun omega ↦ delta omega j * etaY omega) mu :=
        (hInt.etaYDelta j).congr (ae_of_all mu fun omega ↦ by ring)
      have hsum := h1.add h2 |>.add h3
      refine hsum.congr (ae_of_all mu fun omega ↦ ?_)
      change BYX j * (etaY omega * etaY omega) + etaX omega j * etaY omega +
        delta omega j * etaY omega = _
      simp only [intervenedCovariateNoise, systematicCovariateNoise]
      ring
    simpa only using hBase.const_mul (GT i j)
  simp only [populationCrossMoment, semCovariate, Matrix.mulVec, dotProduct]
  rw [show (fun omega ↦ (∑ j, GT i j *
      intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j) *
      etaY omega) = (fun omega ↦ ∑ j, GT i j *
        (intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j *
          etaY omega)) by
    funext omega
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [integral_finset_sum Finset.univ (fun j _ ↦ hTerm j)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [systematicCrossMomentVector]
  congr 1
  have hA := integral_add (hInt.etaYSq.const_mul (BYX j))
    ((hInt.etaYEtaX j).add (hInt.etaYDelta j))
  rw [show (fun omega ↦
      intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j *
        etaY omega) =
      (fun omega ↦ BYX j * (etaY omega * etaY omega)) +
        ((fun omega ↦ etaY omega * etaX omega j) +
          fun omega ↦ etaY omega * delta omega j) by
    funext omega
    simp only [intervenedCovariateNoise, systematicCovariateNoise, Pi.add_apply]
    ring]
  calc
    integral mu
        ((fun omega ↦ BYX j * (etaY omega * etaY omega)) +
          ((fun omega ↦ etaY omega * etaX omega j) +
            fun omega ↦ etaY omega * delta omega j)) =
        (∫ omega, BYX j * (etaY omega * etaY omega) ∂mu) +
          ∫ omega, etaY omega * etaX omega j + etaY omega * delta omega j ∂mu := hA
    _ = (∫ omega, etaY omega * etaY omega ∂mu) * BYX j +
          ∫ omega, etaY omega * etaX omega j ∂mu := by
      rw [integral_const_mul,
        integral_add (hInt.etaYEtaX j) (hInt.etaYDelta j), hZero.etaYDelta j]
      ring

/-- The corrected expansion of `Hplus`.  Both directed outer products are retained. -/
theorem systematicSecondMoment_eq_expanded
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) :
    systematicSecondMoment mu BYX etaY etaX =
      (∫ omega, etaY omega * etaY omega ∂mu) • outerProduct BYX BYX +
      outerProduct BYX (fun i ↦ ∫ omega, etaY omega * etaX omega i ∂mu) +
      outerProduct (fun i ↦ ∫ omega, etaY omega * etaX omega i ∂mu) BYX +
      populationSecondMomentMatrix mu etaX := by
  ext i j
  simp only [systematicSecondMoment, populationSecondMomentMatrix,
    systematicCovariateNoise, Matrix.add_apply, Matrix.smul_apply, outerProduct,
    smul_eq_mul]
  rw [show (fun omega ↦
      (BYX i * etaY omega + etaX omega i) *
        (BYX j * etaY omega + etaX omega j)) =
      (fun omega ↦ (BYX i * BYX j) * (etaY omega * etaY omega)) +
        ((fun omega ↦ BYX i * (etaY omega * etaX omega j)) +
          ((fun omega ↦ BYX j * (etaY omega * etaX omega i)) +
            fun omega ↦ etaX omega i * etaX omega j)) by
    funext omega
    simp only [Pi.add_apply]
    ring]
  calc
    integral mu
        ((fun omega ↦ (BYX i * BYX j) * (etaY omega * etaY omega)) +
          ((fun omega ↦ BYX i * (etaY omega * etaX omega j)) +
            ((fun omega ↦ BYX j * (etaY omega * etaX omega i)) +
              fun omega ↦ etaX omega i * etaX omega j))) =
        (∫ omega, (BYX i * BYX j) * (etaY omega * etaY omega) ∂mu) +
          ∫ omega, BYX i * (etaY omega * etaX omega j) +
            (BYX j * (etaY omega * etaX omega i) + etaX omega i * etaX omega j) ∂mu :=
      integral_add (hInt.etaYSq.const_mul (BYX i * BYX j))
        ((hInt.etaYEtaX j).const_mul (BYX i) |>.add
          ((hInt.etaYEtaX i).const_mul (BYX j) |>.add (hInt.etaXPair i j)))
    _ = (∫ omega, etaY omega * etaY omega ∂mu) * (BYX i * BYX j) +
          BYX i * (∫ omega, etaY omega * etaX omega j ∂mu) +
          BYX j * (∫ omega, etaY omega * etaX omega i ∂mu) +
          ∫ omega, etaX omega i * etaX omega j ∂mu := by
      have hInner := integral_add ((hInt.etaYEtaX i).const_mul (BYX j))
        (hInt.etaXPair i j)
      have hInnerPoint :
          (∫ omega, BYX j * (etaY omega * etaX omega i) +
            etaX omega i * etaX omega j ∂mu) =
          (∫ omega, BYX j * (etaY omega * etaX omega i) ∂mu) +
            ∫ omega, etaX omega i * etaX omega j ∂mu := by
        convert hInner using 1 <;> simp only [Pi.add_apply]
      have hOuter := integral_add ((hInt.etaYEtaX j).const_mul (BYX i))
        ((hInt.etaYEtaX i).const_mul (BYX j) |>.add (hInt.etaXPair i j))
      have hOuterPoint :
          (∫ omega, BYX i * (etaY omega * etaX omega j) +
            (BYX j * (etaY omega * etaX omega i) + etaX omega i * etaX omega j) ∂mu) =
          (∫ omega, BYX i * (etaY omega * etaX omega j) ∂mu) +
            ∫ omega, BYX j * (etaY omega * etaX omega i) +
              etaX omega i * etaX omega j ∂mu := by
        convert hOuter using 1 <;> simp only [Pi.add_apply]
      rw [integral_const_mul, hOuterPoint, integral_const_mul, hInnerPoint,
        integral_const_mul]
      ring
    _ = _ := by ring

/-- `Hplus = E[U Uᵀ]` is symmetric. -/
theorem systematicSecondMoment_symmetric
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) :
    (systematicSecondMoment mu BYX etaY etaX).IsSymm :=
  populationSecondMomentMatrix_symmetric mu _

/-- `Hplus = E[U Uᵀ]` is quadratically nonnegative, derived from integral squares. -/
theorem systematicSecondMoment_quadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) :
    QuadNonneg (systematicSecondMoment mu BYX etaY etaX) :=
  populationSecondMomentMatrix_quadNonneg mu _
    (integrable_systematicCovariateNoise_pair BYX etaY etaX delta hInt)

/-- `Delta = E[delta deltaᵀ]` is symmetric. -/
theorem interventionSecondMoment_symmetric
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (delta : Omega → Fin p → ℝ) :
    (interventionSecondMoment mu delta).IsSymm :=
  populationSecondMomentMatrix_symmetric mu delta

/-- `Delta = E[delta deltaᵀ]` is quadratically nonnegative. -/
theorem interventionSecondMoment_quadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) :
    QuadNonneg (interventionSecondMoment mu delta) :=
  populationSecondMomentMatrix_quadNonneg mu delta hInt.deltaPair

/-- Orthogonality removes the two systematic/intervention cross matrices. -/
theorem intervenedSecondMoment_eq_systematic_add_intervention
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (hZero : HasZeroSystematicInterventionCrossMoments mu etaY etaX delta) :
    populationSecondMomentMatrix mu (fun omega ↦
      intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega)) =
      systematicSecondMoment mu BYX etaY etaX + interventionSecondMoment mu delta := by
  ext i j
  simp only [populationSecondMomentMatrix, systematicSecondMoment,
    interventionSecondMoment, intervenedCovariateNoise, Matrix.add_apply]
  have hUD : ∫ omega,
      systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j ∂mu = 0 := by
    rw [show (fun omega ↦
        systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j) =
        (fun omega ↦ BYX i * (etaY omega * delta omega j)) +
          fun omega ↦ etaX omega i * delta omega j by
      funext omega
      simp only [systematicCovariateNoise, Pi.add_apply]
      ring]
    calc
      integral mu ((fun omega ↦ BYX i * (etaY omega * delta omega j)) +
          fun omega ↦ etaX omega i * delta omega j) =
          (∫ omega, BYX i * (etaY omega * delta omega j) ∂mu) +
            ∫ omega, etaX omega i * delta omega j ∂mu :=
        integral_add ((hInt.etaYDelta j).const_mul (BYX i)) (hInt.etaXDelta i j)
      _ = 0 := by
        rw [integral_const_mul, hZero.etaYDelta j, hZero.etaXDelta i j]
        ring
  have hDU : ∫ omega, delta omega i *
      systematicCovariateNoise BYX (etaX omega) (etaY omega) j ∂mu = 0 := by
    rw [show (fun omega ↦ delta omega i *
        systematicCovariateNoise BYX (etaX omega) (etaY omega) j) =
        (fun omega ↦ BYX j * (etaY omega * delta omega i)) +
          fun omega ↦ delta omega i * etaX omega j by
      funext omega
      simp only [systematicCovariateNoise, Pi.add_apply]
      ring]
    calc
      integral mu ((fun omega ↦ BYX j * (etaY omega * delta omega i)) +
          fun omega ↦ delta omega i * etaX omega j) =
          (∫ omega, BYX j * (etaY omega * delta omega i) ∂mu) +
            ∫ omega, delta omega i * etaX omega j ∂mu :=
        integral_add ((hInt.etaYDelta i).const_mul (BYX j)) (hInt.deltaEtaX i j)
      _ = 0 := by
        rw [integral_const_mul, hZero.etaYDelta i, hZero.deltaEtaX i j]
        ring
  rw [show (fun omega ↦
      (systematicCovariateNoise BYX (etaX omega) (etaY omega) i + delta omega i) *
        (systematicCovariateNoise BYX (etaX omega) (etaY omega) j + delta omega j)) =
      (fun omega ↦ systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
        systematicCovariateNoise BYX (etaX omega) (etaY omega) j) +
      ((fun omega ↦ systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
        delta omega j) +
      ((fun omega ↦ delta omega i *
        systematicCovariateNoise BYX (etaX omega) (etaY omega) j) +
        fun omega ↦ delta omega i * delta omega j)) by
    funext omega
    simp only [Pi.add_apply]
    ring]
  have hUInt := integrable_systematicCovariateNoise_pair BYX etaY etaX delta hInt i j
  have hUDInt : Integrable (fun omega ↦
      systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j) mu := by
    have hs := (hInt.etaYDelta j).const_mul (BYX i) |>.add (hInt.etaXDelta i j)
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change BYX i * (etaY omega * delta omega j) + etaX omega i * delta omega j = _
    simp only [systematicCovariateNoise]
    ring
  have hDUInt : Integrable (fun omega ↦ delta omega i *
      systematicCovariateNoise BYX (etaX omega) (etaY omega) j) mu := by
    have hs := (hInt.etaYDelta i).const_mul (BYX j) |>.add (hInt.deltaEtaX i j)
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change BYX j * (etaY omega * delta omega i) + delta omega i * etaX omega j = _
    simp only [systematicCovariateNoise]
    ring
  calc
    integral mu
        ((fun omega ↦ systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
          systematicCovariateNoise BYX (etaX omega) (etaY omega) j) +
        ((fun omega ↦ systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
          delta omega j) +
        ((fun omega ↦ delta omega i *
          systematicCovariateNoise BYX (etaX omega) (etaY omega) j) +
          fun omega ↦ delta omega i * delta omega j))) =
        (∫ omega, systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
          systematicCovariateNoise BYX (etaX omega) (etaY omega) j ∂mu) +
        ∫ omega, systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j +
          (delta omega i * systematicCovariateNoise BYX (etaX omega) (etaY omega) j +
            delta omega i * delta omega j) ∂mu :=
      integral_add hUInt (hUDInt.add (hDUInt.add (hInt.deltaPair i j)))
    _ = (∫ omega, systematicCovariateNoise BYX (etaX omega) (etaY omega) i *
          systematicCovariateNoise BYX (etaX omega) (etaY omega) j ∂mu) +
        ∫ omega, delta omega i * delta omega j ∂mu := by
      have hInner := integral_add hDUInt (hInt.deltaPair i j)
      have hInnerPoint :
          (∫ omega, delta omega i *
            systematicCovariateNoise BYX (etaX omega) (etaY omega) j +
            delta omega i * delta omega j ∂mu) =
          (∫ omega, delta omega i *
            systematicCovariateNoise BYX (etaX omega) (etaY omega) j ∂mu) +
            ∫ omega, delta omega i * delta omega j ∂mu := by
        convert hInner using 1 <;> simp only [Pi.add_apply]
      have hOuter := integral_add hUDInt (hDUInt.add (hInt.deltaPair i j))
      have hOuterPoint :
          (∫ omega,
            systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j +
            (delta omega i * systematicCovariateNoise BYX (etaX omega) (etaY omega) j +
              delta omega i * delta omega j) ∂mu) =
          (∫ omega,
            systematicCovariateNoise BYX (etaX omega) (etaY omega) i * delta omega j ∂mu) +
            ∫ omega, delta omega i *
              systematicCovariateNoise BYX (etaX omega) (etaY omega) j +
              delta omega i * delta omega j ∂mu := by
        convert hOuter using 1 <;> simp only [Pi.add_apply]
      rw [hOuterPoint, hInnerPoint, hUD, hDU]
      ring

/-- Second moments commute with a fixed finite linear map: if `X = A U`, then
`E[X Xᵀ] = A E[U Uᵀ] Aᵀ`. -/
theorem populationSecondMomentMatrix_mulVec_eq_congruence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (A : Matrix (Fin p) (Fin p) ℝ)
    (U : Omega → Fin p → ℝ)
    (hUU : ∀ i j, Integrable (fun omega ↦ U omega i * U omega j) mu) :
    populationSecondMomentMatrix mu (fun omega ↦ Matrix.mulVec A (U omega)) =
      matrixProduct (matrixProduct A (populationSecondMomentMatrix mu U)) A.transpose := by
  ext i j
  have hTerm : ∀ a b, Integrable (fun omega ↦
      (A i a * A j b) * (U omega a * U omega b)) mu :=
    fun a b ↦ (hUU a b).const_mul (A i a * A j b)
  simp only [populationSecondMomentMatrix, Matrix.mulVec, dotProduct]
  rw [show (fun omega ↦ (∑ a, A i a * U omega a) * (∑ b, A j b * U omega b)) =
      (fun omega ↦ ∑ a, ∑ b, (A i a * A j b) * (U omega a * U omega b)) by
    funext omega
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring]
  rw [integral_finset_sum Finset.univ (fun a _ ↦
    integrable_finsetSum Finset.univ (fun b _ ↦ hTerm a b))]
  simp_rw [integral_finset_sum Finset.univ (fun b _ ↦ hTerm _ b), integral_const_mul]
  simp only [matrixProduct, Matrix.transpose_apply, populationSecondMomentMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Every pair of coordinates of the SEM covariate is integrable under the primitive moment
assumptions. -/
theorem integrable_semCovariate_pair
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (i j : Fin p) :
    Integrable (fun omega ↦
      semCovariate GT BYX (etaX omega) (delta omega) (etaY omega) i *
      semCovariate GT BYX (etaX omega) (delta omega) (etaY omega) j) mu := by
  let U : Omega → Fin p → ℝ := fun omega ↦
    intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega)
  have hTerm : ∀ a b, Integrable (fun omega ↦
      (GT i a * GT j b) * (U omega a * U omega b)) mu := fun a b ↦
    (integrable_intervenedCovariateNoise_pair BYX etaY etaX delta hInt a b).const_mul
      (GT i a * GT j b)
  have hSum : Integrable (fun omega ↦ ∑ a, ∑ b,
      (GT i a * GT j b) * (U omega a * U omega b)) mu :=
    integrable_finsetSum Finset.univ (fun a _ ↦
      integrable_finsetSum Finset.univ (fun b _ ↦ hTerm a b))
  refine hSum.congr (ae_of_all mu fun omega ↦ ?_)
  simp only [semCovariate, Matrix.mulVec, dotProduct, U]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Corrected covariance formula with explicit orientation:
`Sigma = GT (Hplus + Delta) GTᵀ`.  Since `GT` denotes mathematical `Gᵀ`, the final
factor `GTᵀ` is mathematical `G`. -/
theorem sem_secondMoment_eq
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (hZero : HasZeroSystematicInterventionCrossMoments mu etaY etaX delta) :
    semSecondMoment mu GT BYX etaY etaX delta =
      matrixProduct
        (matrixProduct GT
          (systematicSecondMoment mu BYX etaY etaX + interventionSecondMoment mu delta))
        GT.transpose := by
  change populationSecondMomentMatrix mu (fun omega ↦ Matrix.mulVec GT
    (intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega))) = _
  rw [populationSecondMomentMatrix_mulVec_eq_congruence GT _
    (integrable_intervenedCovariateNoise_pair BYX etaY etaX delta hInt)]
  rw [intervenedSecondMoment_eq_systematic_add_intervention BYX etaY etaX delta hInt hZero]

/-- The actual SEM second moment is symmetric. -/
theorem semSecondMoment_symmetric
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ) :
    (semSecondMoment mu GT BYX etaY etaX delta).IsSymm :=
  populationSecondMomentMatrix_symmetric mu _

/-- The actual SEM second moment is quadratically nonnegative, with no PSD assumption. -/
theorem semSecondMoment_quadNonneg
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) :
    QuadNonneg (semSecondMoment mu GT BYX etaY etaX delta) :=
  populationSecondMomentMatrix_quadNonneg mu _
    (integrable_semCovariate_pair GT BYX etaY etaX delta hInt)

/-- The common linear coefficient in the project-note quadratic risk expansion under the
corrected source convention:
`semV = -E[X etaY]`. -/
noncomputable def semV
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    (mu : Measure Omega) (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX : Omega → Fin p → ℝ) : Fin p → ℝ :=
  fun i ↦ -Matrix.mulVec GT (systematicCrossMomentVector mu BYX etaY etaX) i

/-- The realized outcome equation `Y = betaStarᵀ X + etaY`. -/
def semOutcome {Omega : Type*} {p : ℕ} (X : Omega → Fin p → ℝ)
    (betaStar : Fin p → ℝ) (etaY : Omega → ℝ) : Omega → ℝ :=
  fun omega ↦ vectorDot (X omega) betaStar + etaY omega

theorem integrable_intervenedCovariateNoise_mul_etaY
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) (j : Fin p) :
    Integrable (fun omega ↦
      intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j *
        etaY omega) mu := by
  have h1 := hInt.etaYSq.const_mul (BYX j)
  have h2 : Integrable (fun omega ↦ etaX omega j * etaY omega) mu :=
    (hInt.etaYEtaX j).congr (ae_of_all mu fun omega ↦ by ring)
  have h3 : Integrable (fun omega ↦ delta omega j * etaY omega) mu :=
    (hInt.etaYDelta j).congr (ae_of_all mu fun omega ↦ by ring)
  have hs := h1.add h2 |>.add h3
  refine hs.congr (ae_of_all mu fun omega ↦ ?_)
  change BYX j * (etaY omega * etaY omega) + etaX omega j * etaY omega +
    delta omega j * etaY omega = _
  simp only [intervenedCovariateNoise, systematicCovariateNoise]
  ring

theorem integrable_semCovariate_mul_etaY
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) (i : Fin p) :
    Integrable (fun omega ↦
      semCovariate GT BYX (etaX omega) (delta omega) (etaY omega) i * etaY omega) mu := by
  have hs : Integrable (fun omega ↦ ∑ j, GT i j *
      (intervenedCovariateNoise BYX (etaX omega) (delta omega) (etaY omega) j *
        etaY omega)) mu := integrable_finsetSum Finset.univ (fun j _ ↦
    (integrable_intervenedCovariateNoise_mul_etaY BYX etaY etaX delta hInt j).const_mul
      (GT i j))
  refine hs.congr (ae_of_all mu fun omega ↦ ?_)
  simp only [semCovariate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All monomials required by the existing population-risk bridge are integrable for the
realized additive-intervention SEM. -/
theorem sem_hasIntegrablePopulationQuadraticMonomials
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta) :
    HasIntegrablePopulationQuadraticMonomials mu
      (fun omega ↦ semCovariate GT BYX (etaX omega) (delta omega) (etaY omega))
      (semOutcome (fun omega ↦ semCovariate GT BYX
        (etaX omega) (delta omega) (etaY omega)) betaStar etaY) := by
  let X : Omega → Fin p → ℝ := fun omega ↦
    semCovariate GT BYX (etaX omega) (delta omega) (etaY omega)
  have hXX : ∀ i j, Integrable (fun omega ↦ X omega i * X omega j) mu :=
    integrable_semCovariate_pair GT BYX etaY etaX delta hInt
  have hXE : ∀ i, Integrable (fun omega ↦ X omega i * etaY omega) mu :=
    integrable_semCovariate_mul_etaY GT BYX etaY etaX delta hInt
  have hDotSq : Integrable (fun omega ↦ (vectorDot (X omega) betaStar) ^ 2) mu := by
    have hs : Integrable (fun omega ↦ ∑ i, ∑ j,
        (betaStar i * betaStar j) * (X omega i * X omega j)) mu :=
      integrable_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ (fun j _ ↦
          (hXX i j).const_mul (betaStar i * betaStar j)))
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change (∑ i, ∑ j, (betaStar i * betaStar j) *
      (X omega i * X omega j)) = (∑ i, X omega i * betaStar i) ^ 2
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hDotEta : Integrable (fun omega ↦
      vectorDot (X omega) betaStar * etaY omega) mu := by
    have hs : Integrable (fun omega ↦ ∑ i,
        betaStar i * (X omega i * etaY omega)) mu :=
      integrable_finsetSum Finset.univ (fun i _ ↦ (hXE i).const_mul (betaStar i))
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change (∑ i, betaStar i * (X omega i * etaY omega)) =
      (∑ i, X omega i * betaStar i) * etaY omega
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨?_, ?_, hXX⟩
  · have hs := hDotSq.add ((hDotEta.const_mul 2).add hInt.etaYSq)
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change (vectorDot (X omega) betaStar) ^ 2 +
      (2 * (vectorDot (X omega) betaStar * etaY omega) +
        etaY omega * etaY omega) = _
    simp only [semOutcome, X]
    ring
  · intro i
    have hDot : Integrable (fun omega ↦ X omega i * vectorDot (X omega) betaStar) mu := by
      have hs : Integrable (fun omega ↦ ∑ j,
          betaStar j * (X omega i * X omega j)) mu :=
        integrable_finsetSum Finset.univ (fun j _ ↦ (hXX i j).const_mul (betaStar j))
      refine hs.congr (ae_of_all mu fun omega ↦ ?_)
      change (∑ j, betaStar j * (X omega i * X omega j)) =
        X omega i * ∑ j, X omega j * betaStar j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hs := hDot.add (hXE i)
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change X omega i * vectorDot (X omega) betaStar + X omega i * etaY omega = _
    simp only [semOutcome, X]
    ring

/-- Corrected model-specific cross-moment relation required by the expanded environmental-risk
bridge (Appendix Lemma 1 / project-note numbering). -/
theorem additiveIntervention_crossMomentRelation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (hZero : HasZeroSystematicInterventionCrossMoments mu etaY etaX delta) :
    ∀ i,
      populationCrossMoment mu
        (fun omega ↦ semCovariate GT BYX (etaX omega) (delta omega) (etaY omega))
        (semOutcome (fun omega ↦ semCovariate GT BYX
          (etaX omega) (delta omega) (etaY omega)) betaStar etaY) i =
      Matrix.mulVec (semSecondMoment mu GT BYX etaY etaX delta) betaStar i -
        semV mu GT BYX etaY etaX i := by
  let X : Omega → Fin p → ℝ := fun omega ↦
    semCovariate GT BYX (etaX omega) (delta omega) (etaY omega)
  have hXX : ∀ i j, Integrable (fun omega ↦ X omega i * X omega j) mu :=
    integrable_semCovariate_pair GT BYX etaY etaX delta hInt
  have hXE : ∀ i, Integrable (fun omega ↦ X omega i * etaY omega) mu :=
    integrable_semCovariate_mul_etaY GT BYX etaY etaX delta hInt
  have hCrossEta := sem_crossMoment_eq GT BYX etaY etaX delta hInt hZero
  intro i
  have hDot : Integrable (fun omega ↦ X omega i * vectorDot (X omega) betaStar) mu := by
    have hs : Integrable (fun omega ↦ ∑ j,
        betaStar j * (X omega i * X omega j)) mu :=
      integrable_finsetSum Finset.univ (fun j _ ↦ (hXX i j).const_mul (betaStar j))
    refine hs.congr (ae_of_all mu fun omega ↦ ?_)
    change (∑ j, betaStar j * (X omega i * X omega j)) =
      X omega i * ∑ j, X omega j * betaStar j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [populationCrossMoment, semOutcome]
  have hSplit := integral_add hDot (hXE i)
  change (∫ omega, X omega i * vectorDot (X omega) betaStar +
    X omega i * etaY omega ∂mu) = _ at hSplit
  rw [show (fun omega ↦ X omega i *
      (vectorDot (X omega) betaStar + etaY omega)) =
      (fun omega ↦ X omega i * vectorDot (X omega) betaStar +
        X omega i * etaY omega) by
    funext omega
    ring, hSplit]
  have hDotMoment : (∫ omega, X omega i * vectorDot (X omega) betaStar ∂mu) =
      Matrix.mulVec (semSecondMoment mu GT BYX etaY etaX delta) betaStar i := by
    rw [show (fun omega ↦ X omega i * vectorDot (X omega) betaStar) =
        (fun omega ↦ ∑ j, betaStar j * (X omega i * X omega j)) by
      funext omega
      rw [vectorDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [integral_finset_sum Finset.univ (fun j _ ↦ (hXX i j).const_mul (betaStar j))]
    simp_rw [integral_const_mul]
    simp only [semSecondMoment, populationSecondMomentMatrix, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hDotMoment]
  have hCrossCoord := congrFun hCrossEta i
  change (∫ omega, X omega i * etaY omega ∂mu) =
    Matrix.mulVec GT (systematicCrossMomentVector mu BYX etaY etaX) i at hCrossCoord
  rw [hCrossCoord]
  simp only [semV]
  ring

/-- Corrected outcome-second-moment relation required by the expanded environmental-risk bridge. -/
theorem additiveIntervention_outcomeMomentRelation
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (hZero : HasZeroSystematicInterventionCrossMoments mu etaY etaX delta) :
    populationOutcomeSecondMoment mu
      (semOutcome (fun omega ↦ semCovariate GT BYX
        (etaX omega) (delta omega) (etaY omega)) betaStar etaY) =
      (∫ omega, etaY omega * etaY omega ∂mu) +
        matrixQuad (semSecondMoment mu GT BYX etaY etaX delta) betaStar -
        2 * vectorDot (semV mu GT BYX etaY etaX) betaStar := by
  let X : Omega → Fin p → ℝ := fun omega ↦
    semCovariate GT BYX (etaX omega) (delta omega) (etaY omega)
  let Y : Omega → ℝ := semOutcome X betaStar etaY
  have hMom := sem_hasIntegrablePopulationQuadraticMonomials GT BYX betaStar
    etaY etaX delta hInt
  have hRisk := finitePopulationSquaredRisk_eq_momentRisk X Y betaStar hMom
  have hRiskAtTruth : finitePopulationSquaredRisk mu X Y betaStar =
      ∫ omega, etaY omega * etaY omega ∂mu := by
    rw [finitePopulationSquaredRisk]
    apply integral_congr_ae
    filter_upwards [] with omega
    simp only [Y, semOutcome]
    ring
  rw [hRiskAtTruth] at hRisk
  have hCross := additiveIntervention_crossMomentRelation GT BYX betaStar etaY
    etaX delta hInt hZero
  have hCrossXY : ∀ i, populationCrossMoment mu X Y i =
      Matrix.mulVec (semSecondMoment mu GT BYX etaY etaX delta) betaStar i -
        semV mu GT BYX etaY etaX i := by
    intro i
    simpa only [X, Y] using hCross i
  have hCrossDot :
      vectorDot (populationCrossMoment mu X Y) betaStar =
        matrixQuad (semSecondMoment mu GT BYX etaY etaX delta) betaStar -
          vectorDot (semV mu GT BYX etaY etaX) betaStar := by
    rw [vectorDot]
    simp_rw [hCrossXY]
    simp only [matrixQuad, vectorDot]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [finiteMomentEnvironmentalRisk] at hRisk
  rw [hCrossDot] at hRisk
  have hSigma : populationSecondMomentMatrix mu X =
      semSecondMoment mu GT BYX etaY etaX delta := by rfl
  rw [hSigma] at hRisk
  linarith

/-- The actual squared loss satisfies the expanded environmental-risk identity used by this
project, with both model-specific moment relations derived from the corrected SEM and actual
integrals.  This theorem deliberately calls the
existing `finitePopulationSquaredRisk_eq_expandedEnvironmentalRisk` bridge. -/
theorem additiveIntervention_populationRisk_eq_expandedEnvironmentalRisk
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {p : ℕ}
    {mu : Measure Omega} (GT : Matrix (Fin p) (Fin p) ℝ)
    (BYX betaStar b : Fin p → ℝ) (etaY : Omega → ℝ)
    (etaX delta : Omega → Fin p → ℝ)
    (hInt : HasIntegrableAdditiveInterventionMoments mu etaY etaX delta)
    (hZero : HasZeroSystematicInterventionCrossMoments mu etaY etaX delta) :
    finitePopulationSquaredRisk mu
      (fun omega ↦ semCovariate GT BYX (etaX omega) (delta omega) (etaY omega))
      (semOutcome (fun omega ↦ semCovariate GT BYX
        (etaX omega) (delta omega) (etaY omega)) betaStar etaY) b =
      expandedEnvironmentalRisk
        (∫ omega, etaY omega * etaY omega ∂mu)
        (semV mu GT BYX etaY etaX) b betaStar
        (semSecondMoment mu GT BYX etaY etaX delta) := by
  exact finitePopulationSquaredRisk_eq_expandedEnvironmentalRisk _ _ _ _ _ _
    (sem_hasIntegrablePopulationQuadraticMonomials GT BYX betaStar etaY etaX delta hInt)
    (additiveIntervention_crossMomentRelation GT BYX betaStar etaY etaX delta hInt hZero)
    (additiveIntervention_outcomeMomentRelation GT BYX betaStar etaY etaX delta hInt hZero)
end NegDRO
