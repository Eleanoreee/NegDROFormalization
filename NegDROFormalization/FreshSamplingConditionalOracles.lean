import NegDROFormalization.FreshFiniteEnvironmentMoments

/-!
# Conditional finite-mixture realization of the concrete oracles

The primitive sampling interface in this module specifies only selected-environment conditional
monomials `XX`, `XY`, and `Y²`.  Current iterates do not occur in that interface.  Predictable
finite-coordinate algebra then derives the conditional means of the concrete primal and dual
sample oracles.  This is a conditional finite-mixture moment realization, not a construction of a
regular conditional probability kernel.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Environmental risk expressed through population moments. -/
noncomputable def finiteMomentEnvironmentalRisk
    {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin p → ℝ) (q : ℝ) : ℝ :=
  q - 2 * vectorDot c b + matrixQuad Sigma b

/-- The score `Sigma b - c` appearing in the primal oracle mean. -/
noncomputable def finiteMomentEnvironmentalScore
    {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (c b : Fin p → ℝ) : Fin p → ℝ :=
  fun i ↦ Matrix.mulVec Sigma b i - c i

/-- Weight- and iterate-independent conditional monomial law for a fresh finite environment. -/
structure HasFreshFiniteEnvironmentPopulationMoments
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ) : Prop where
  selectedXXIntegrable : ∀ e i j, Integrable
    (selectedEnvironmentTerm E e (fun omega ↦ X omega i * X omega j)) mu
  selectedXYIntegrable : ∀ e i, Integrable
    (selectedEnvironmentTerm E e (fun omega ↦ X omega i * Y omega)) mu
  selectedYSqIntegrable : ∀ e, Integrable
    (selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 2)) mu
  selectedXXCond : ∀ e i j,
    mu[selectedEnvironmentTerm E e (fun omega ↦ X omega i * X omega j) |
      mCond] =ᵐ[mu] fun _ ↦ (1 / (m : ℝ)) * Sigma e i j
  selectedXYCond : ∀ e i,
    mu[selectedEnvironmentTerm E e (fun omega ↦ X omega i * Y omega) |
      mCond] =ᵐ[mu] fun _ ↦ (1 / (m : ℝ)) * c e i
  selectedYSqCond : ∀ e,
    mu[selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 2) |
      mCond] =ᵐ[mu] fun _ ↦ (1 / (m : ℝ)) * q e

/-- Lambda-form finite-sum linearity for conditional expectation. -/
theorem condExp_finset_sum_apply
    {Omega ι : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (s : Finset ι) (f : ι → Omega → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) mu) :
    mu[(fun omega ↦ ∑ i ∈ s, f i omega) | mCond] =ᵐ[mu]
      fun omega ↦ ∑ i ∈ s, (mu[f i | mCond]) omega := by
  have h := condExp_finsetSum hf mCond
  have hInput : (∑ i ∈ s, f i) = (fun omega ↦ ∑ i ∈ s, f i omega) := by
    funext omega
    simp
  have hOutput : (∑ i ∈ s, mu[f i | mCond]) =
      (fun omega ↦ ∑ i ∈ s, (mu[f i | mCond]) omega) := by
    funext omega
    simp
  rw [← hInput, ← hOutput]
  exact h

/-- Pull a predictable scalar through conditional expectation and replace the remaining
conditional mean by an a.e. identified function. -/
theorem condExp_predictable_mul_ae_eq
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (a Z F : Omega → ℝ)
    (ha : AEStronglyMeasurable[mCond] a mu)
    (hZ : Integrable Z mu) (haZ : Integrable (fun omega ↦ a omega * Z omega) mu)
    (hCond : mu[Z | mCond] =ᵐ[mu] F) :
    mu[(fun omega ↦ a omega * Z omega) | mCond] =ᵐ[mu]
      fun omega ↦ a omega * F omega := by
  have hPull : mu[a * Z | mCond] =ᵐ[mu] a * mu[Z | mCond] :=
    condExp_mul_of_aestronglyMeasurable_left ha haZ hZ
  exact hPull.trans (EventuallyEq.mul (EventuallyEq.refl _ _) hCond)

/-- A coordinate of an explicitly squared-norm-bounded vector is bounded by `B`. -/
theorem norm_coordinate_le_of_sqNorm_le
    {p : ℕ} (b : Fin p → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : sqNorm b ≤ B ^ 2) (i : Fin p) :
    ‖b i‖ ≤ B := by
  rw [Real.norm_eq_abs]
  exact abs_le_of_sq_le_sq ((coordinate_sq_le_sqNorm b i).trans hb) hB

/-- Selected primal residual coordinate, before the external NegDRO weight. -/
noncomputable def selectedPrimalResidualCoordinate
    {Omega : Type*} {m p : ℕ}
    (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ) (e : Fin m) (i : Fin p) : Omega → ℝ :=
  selectedEnvironmentTerm E e
    (fun omega ↦ X omega i * (vectorDot (X omega) (b omega) - Y omega))

/-- Conditional mean of the selected primal residual coordinate from `XX` and `XY` monomials. -/
theorem condExp_selectedPrimalResidualCoordinate
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (b : Omega → Fin p → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ j, AEStronglyMeasurable[mCond] (fun omega ↦ b omega j) mu)
    (hmCond : mCond ≤ mOmega)
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q) (e : Fin m) (i : Fin p) :
    Integrable (selectedPrimalResidualCoordinate E X Y b e i) mu ∧
    mu[selectedPrimalResidualCoordinate E X Y b e i | mCond] =ᵐ[mu]
      fun omega ↦ (1 / (m : ℝ)) * finiteMomentEnvironmentalScore
        (Sigma e) (c e) (b omega) i := by
  let xx : Fin p → Omega → ℝ := fun j ↦
    selectedEnvironmentTerm E e (fun omega ↦ X omega i * X omega j)
  let xy : Omega → ℝ :=
    selectedEnvironmentTerm E e (fun omega ↦ X omega i * Y omega)
  let weightedXX : Fin p → Omega → ℝ := fun j omega ↦ b omega j * xx j omega
  have hbAmbient : ∀ j, AEStronglyMeasurable (fun omega ↦ b omega j) mu :=
    fun j ↦ (hbMeas j).mono hmCond
  have hWeightedInt : ∀ j, Integrable (weightedXX j) mu := by
    intro j
    exact (hMom.selectedXXIntegrable e i j).bdd_mul (hbAmbient j)
      (ae_of_all mu (fun omega ↦ norm_coordinate_le_of_sqNorm_le
        (b omega) B hB (hb omega) j))
  have hWeightedCond : ∀ j,
      mu[weightedXX j | mCond] =ᵐ[mu]
        fun omega ↦ b omega j * ((1 / (m : ℝ)) * Sigma e i j) := by
    intro j
    exact condExp_predictable_mul_ae_eq
      (fun omega ↦ b omega j) (xx j)
      (fun _ ↦ (1 / (m : ℝ)) * Sigma e i j)
      (hbMeas j) (hMom.selectedXXIntegrable e i j) (hWeightedInt j)
      (hMom.selectedXXCond e i j)
  have hSumInt : Integrable (fun omega ↦ ∑ j, weightedXX j omega) mu :=
    integrable_finsetSum Finset.univ (fun j _hj ↦ hWeightedInt j)
  have hResidualEq : selectedPrimalResidualCoordinate E X Y b e i =
      (fun omega ↦ (∑ j, weightedXX j omega) - xy omega) := by
    funext omega
    dsimp [selectedPrimalResidualCoordinate, selectedEnvironmentTerm,
      weightedXX, xx, xy, vectorDot]
    have hInner : X omega i * (∑ j, X omega j * b omega j) =
        ∑ j, X omega i * X omega j * b omega j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    rw [mul_sub]
    rw [hInner]
    rw [mul_sub, Finset.mul_sum]
    apply congrArg (fun z ↦ z -
      selectedEnvironmentIndicator E e omega * (X omega i * Y omega))
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hResidualInt : Integrable (selectedPrimalResidualCoordinate E X Y b e i) mu := by
    rw [hResidualEq]
    exact hSumInt.sub (hMom.selectedXYIntegrable e i)
  refine ⟨hResidualInt, ?_⟩
  rw [hResidualEq]
  have hSumCond := condExp_finset_sum_apply (mCond := mCond) Finset.univ weightedXX
    (fun j _hj ↦ hWeightedInt j)
  have hSubCond := condExp_sub hSumInt (hMom.selectedXYIntegrable e i) mCond
  have hSubInput :
      (fun omega ↦ (∑ j, weightedXX j omega) - xy omega) =
        (fun omega ↦ ∑ j, weightedXX j omega) - xy := by
    funext omega
    rfl
  have hSubOutput :
      (fun omega ↦ (mu[(fun omega ↦ ∑ j, weightedXX j omega) | mCond]) omega -
        (mu[xy | mCond]) omega) =
      mu[(fun omega ↦ ∑ j, weightedXX j omega) | mCond] - mu[xy | mCond] := by
    funext omega
    rfl
  have hSubCond' :
      mu[(fun omega ↦ (∑ j, weightedXX j omega) - xy omega) | mCond] =ᵐ[mu]
        fun omega ↦ (mu[(fun omega ↦ ∑ j, weightedXX j omega) | mCond]) omega -
          (mu[xy | mCond]) omega := by
    rw [hSubInput, hSubOutput]
    exact hSubCond
  filter_upwards [hSubCond', hSumCond, ae_all_iff.2 hWeightedCond,
    hMom.selectedXYCond e i] with omega hsub hsum hweighted hxy
  rw [hsub, hsum, hxy]
  simp_rw [hweighted]
  dsimp [finiteMomentEnvironmentalScore, Matrix.mulVec, dotProduct]
  rw [show (∑ j, b omega j * (1 / (m : ℝ) * Sigma e i j)) =
      (1 / (m : ℝ)) * ∑ j, Sigma e i j * b omega j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  ring

/-- Moment relation `c_e = Sigma_e betaStar - v`. -/
def HasNegDROCrossMomentRelation
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (v betaStar : Fin p → ℝ) : Prop :=
  ∀ e i, c e i = Matrix.mulVec (Sigma e) betaStar i - v i

/-- The moment score becomes the existing expanded displacement score. -/
theorem finiteMomentEnvironmentalScore_eq
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (v betaStar b : Fin p → ℝ)
    (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar)
    (e : Fin m) (i : Fin p) :
    finiteMomentEnvironmentalScore (Sigma e) (c e) b i =
      v i + Matrix.mulVec (Sigma e) (primalDisplacement b betaStar) i := by
  change (∑ j, Sigma e i j * b j) - c e i =
    v i + ∑ j, Sigma e i j * (b j - betaStar j)
  have hc : c e i = (∑ j, Sigma e i j * betaStar j) - v i := by
    simpa only [Matrix.mulVec, dotProduct] using hCross e i
  rw [hc]
  rw [show (∑ j, Sigma e i j * (b j - betaStar j)) =
      (∑ j, Sigma e i j * b j) - ∑ j, Sigma e i j * betaStar j by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  ring

/-- Selected squared residual, before the external uniform-sampling factor `m`. -/
noncomputable def selectedResidualSq
    {Omega : Type*} {m p : ℕ}
    (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (b : Omega → Fin p → ℝ) (e : Fin m) : Omega → ℝ :=
  selectedEnvironmentTerm E e
    (fun omega ↦ (Y omega - vectorDot (X omega) (b omega)) ^ 2)

/-- Conditional mean of a selected squared residual, derived solely from the selected
`XX`, `XY`, and `Y²` conditional moment identities. -/
theorem condExp_selectedResidualSq
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (b : Omega → Fin p → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ j, AEStronglyMeasurable[mCond] (fun omega ↦ b omega j) mu)
    (hmCond : mCond ≤ mOmega)
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q) (e : Fin m) :
    Integrable (selectedResidualSq E X Y b e) mu ∧
    mu[selectedResidualSq E X Y b e | mCond] =ᵐ[mu]
      fun omega ↦ (1 / (m : ℝ)) *
        finiteMomentEnvironmentalRisk (Sigma e) (c e) (b omega) (q e) := by
  let yy : Omega → ℝ :=
    selectedEnvironmentTerm E e (fun omega ↦ (Y omega) ^ 2)
  let xy : Fin p → Omega → ℝ := fun j ↦
    selectedEnvironmentTerm E e (fun omega ↦ X omega j * Y omega)
  let xx : Fin p × Fin p → Omega → ℝ := fun jk ↦
    selectedEnvironmentTerm E e (fun omega ↦ X omega jk.1 * X omega jk.2)
  let weightedXY : Fin p → Omega → ℝ := fun j omega ↦ b omega j * xy j omega
  let weightedXX : Fin p × Fin p → Omega → ℝ := fun jk omega ↦
    (b omega jk.1 * b omega jk.2) * xx jk omega
  have hbAmbient : ∀ j, AEStronglyMeasurable (fun omega ↦ b omega j) mu :=
    fun j ↦ (hbMeas j).mono hmCond
  have hbCoord : ∀ j, ∀ omega, ‖b omega j‖ ≤ B := by
    intro j omega
    exact norm_coordinate_le_of_sqNorm_le (b omega) B hB (hb omega) j
  have hWeightedXYInt : ∀ j, Integrable (weightedXY j) mu := by
    intro j
    exact (hMom.selectedXYIntegrable e j).bdd_mul (hbAmbient j)
      (ae_of_all mu (fun omega ↦ hbCoord j omega))
  have hWeightedXXInt : ∀ jk, Integrable (weightedXX jk) mu := by
    intro jk
    have hCoeffMeas : AEStronglyMeasurable
        (fun omega ↦ b omega jk.1 * b omega jk.2) mu :=
      (hbAmbient jk.1).mul (hbAmbient jk.2)
    apply (hMom.selectedXXIntegrable e jk.1 jk.2).bdd_mul hCoeffMeas
    filter_upwards [] with omega
    rw [norm_mul]
    exact mul_le_mul (hbCoord jk.1 omega) (hbCoord jk.2 omega)
      (norm_nonneg _) hB
  have hWeightedXYCond : ∀ j,
      mu[weightedXY j | mCond] =ᵐ[mu]
        fun omega ↦ b omega j * ((1 / (m : ℝ)) * c e j) := by
    intro j
    exact condExp_predictable_mul_ae_eq
      (fun omega ↦ b omega j) (xy j)
      (fun _ ↦ (1 / (m : ℝ)) * c e j)
      (hbMeas j) (hMom.selectedXYIntegrable e j) (hWeightedXYInt j)
      (hMom.selectedXYCond e j)
  have hWeightedXXCond : ∀ jk,
      mu[weightedXX jk | mCond] =ᵐ[mu]
        fun omega ↦ (b omega jk.1 * b omega jk.2) *
          ((1 / (m : ℝ)) * Sigma e jk.1 jk.2) := by
    intro jk
    exact condExp_predictable_mul_ae_eq
      (fun omega ↦ b omega jk.1 * b omega jk.2) (xx jk)
      (fun _ ↦ (1 / (m : ℝ)) * Sigma e jk.1 jk.2)
      ((hbMeas jk.1).mul (hbMeas jk.2))
      (hMom.selectedXXIntegrable e jk.1 jk.2) (hWeightedXXInt jk)
      (hMom.selectedXXCond e jk.1 jk.2)
  have hXYSumInt : Integrable (fun omega ↦ ∑ j, weightedXY j omega) mu :=
    integrable_finsetSum Finset.univ (fun j _hj ↦ hWeightedXYInt j)
  have hXXSumInt : Integrable (fun omega ↦ ∑ jk, weightedXX jk omega) mu :=
    integrable_finsetSum Finset.univ (fun jk _hjk ↦ hWeightedXXInt jk)
  have hResidualEq : selectedResidualSq E X Y b e =
      (fun omega ↦ yy omega - 2 * (∑ j, weightedXY j omega) +
        ∑ jk, weightedXX jk omega) := by
    funext omega
    simp only [selectedResidualSq, selectedEnvironmentTerm, yy, xy, xx,
      weightedXY, weightedXX, vectorDot]
    by_cases he : E omega = e
    · simp only [selectedEnvironmentIndicator, he]
      simp only [finCoordinateIndicator, if_true, one_mul]
      have hCross : 2 * (∑ i, b omega i * (X omega i * Y omega)) =
          2 * Y omega * ∑ i, X omega i * b omega i := by
        calc
          2 * (∑ i, b omega i * (X omega i * Y omega)) =
              ∑ i, 2 * (b omega i * (X omega i * Y omega)) :=
            Finset.mul_sum _ _ _
          _ = ∑ i, (2 * Y omega) * (X omega i * b omega i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = 2 * Y omega * ∑ i, X omega i * b omega i :=
            (Finset.mul_sum _ _ _).symm
      have hQuad : (∑ x : Fin p × Fin p,
          b omega x.1 * b omega x.2 * (X omega x.1 * X omega x.2)) =
          (∑ i, X omega i * b omega i) ^ 2 := by
        rw [pow_two, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_product']
        apply Finset.sum_congr rfl
        intro jk _hjk
        ring
      rw [hCross, hQuad]
      ring
    · have he' : e ≠ E omega := Ne.symm he
      simp [selectedEnvironmentIndicator, finCoordinateIndicator, he']
  have hResidualInt : Integrable (selectedResidualSq E X Y b e) mu := by
    rw [hResidualEq]
    exact ((hMom.selectedYSqIntegrable e).sub (hXYSumInt.const_mul 2)).add hXXSumInt
  refine ⟨hResidualInt, ?_⟩
  rw [hResidualEq]
  have hXYSumCond := condExp_finset_sum_apply (mCond := mCond) Finset.univ weightedXY
    (fun j _hj ↦ hWeightedXYInt j)
  have hXXSumCond := condExp_finset_sum_apply (mCond := mCond) Finset.univ weightedXX
    (fun jk _hjk ↦ hWeightedXXInt jk)
  have hTwoXYInt : Integrable (fun omega ↦ 2 * (∑ j, weightedXY j omega)) mu :=
    hXYSumInt.const_mul 2
  have hSubCond := condExp_sub (hMom.selectedYSqIntegrable e) hTwoXYInt mCond
  change mu[(fun omega ↦ yy omega - 2 * (∑ j, weightedXY j omega)) | mCond] =ᵐ[mu]
    fun omega ↦ (mu[yy | mCond]) omega -
      (mu[(fun omega ↦ 2 * (∑ j, weightedXY j omega)) | mCond]) omega at hSubCond
  have hTwoCond := condExp_smul (μ := mu) (2 : ℝ)
    (fun omega ↦ ∑ j, weightedXY j omega) mCond
  change mu[(fun omega ↦ 2 * (∑ j, weightedXY j omega)) | mCond] =ᵐ[mu]
    fun omega ↦ 2 *
      (mu[(fun omega ↦ ∑ j, weightedXY j omega) | mCond]) omega at hTwoCond
  have hFirstInt : Integrable
      (fun omega ↦ yy omega - 2 * (∑ j, weightedXY j omega)) mu :=
    (hMom.selectedYSqIntegrable e).sub hTwoXYInt
  have hAddCond := condExp_add hFirstInt hXXSumInt mCond
  change mu[(fun omega ↦ yy omega - 2 * (∑ j, weightedXY j omega) +
      ∑ jk, weightedXX jk omega) | mCond] =ᵐ[mu]
    fun omega ↦
      (mu[(fun omega ↦ yy omega - 2 * (∑ j, weightedXY j omega)) | mCond]) omega +
      (mu[(fun omega ↦ ∑ jk, weightedXX jk omega) | mCond]) omega at hAddCond
  filter_upwards [hAddCond, hSubCond, hTwoCond, hXYSumCond, hXXSumCond,
    ae_all_iff.2 hWeightedXYCond, ae_all_iff.2 hWeightedXXCond,
    hMom.selectedYSqCond e] with omega hadd hsub htwo hxysum hxxsum hxy hxx hyy
  rw [hadd, hsub, htwo, hxysum, hxxsum, hyy]
  simp_rw [hxy, hxx]
  dsimp [finiteMomentEnvironmentalRisk, matrixQuad, vectorDot,
    Matrix.mulVec, dotProduct]
  rw [show (∑ jk : Fin p × Fin p,
        (b omega jk.1 * b omega jk.2) *
          (1 / (m : ℝ) * Sigma e jk.1 jk.2)) =
      (1 / (m : ℝ)) *
        ∑ i, b omega i * ∑ j, Sigma e i j * b omega j by
    rw [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show (1 / (m : ℝ)) *
        (b omega i * ∑ j, Sigma e i j * b omega j) =
        ((1 / (m : ℝ)) * b omega i) *
          ∑ j, Sigma e i j * b omega j by ring]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [show (∑ j, b omega j * (1 / (m : ℝ) * c e j)) =
      (1 / (m : ℝ)) * ∑ j, c e j * b omega j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  ring

/-- Outcome second-moment relation from the additive structural model. -/
def HasNegDROOutcomeMomentRelation
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (q : Fin m → ℝ) (sigmaYSq : ℝ) (v betaStar : Fin p → ℝ) : Prop :=
  ∀ e, q e = sigmaYSq + matrixQuad (Sigma e) betaStar -
    2 * vectorDot v betaStar

/-- Symmetry turns the two mixed bilinear terms into the same scalar. -/
theorem vectorDot_mulVec_comm_of_isSymm
    {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (x y : Fin p → ℝ)
    (hM : M.IsSymm) :
    vectorDot x (Matrix.mulVec M y) =
      vectorDot y (Matrix.mulVec M x) := by
  have h := Matrix.dotProduct_transpose_mulVec M x y
  rw [hM.eq] at h
  change x ⬝ᵥ Matrix.mulVec M y = y ⬝ᵥ Matrix.mulVec M x
  exact h

/-- The primitive `XX`, `XY`, and `Y²` population moments recover the expanded
environmental-risk identity from Appendix Lemma 1 used by this project.  Official v3 Eq. (13) is
the minimax identification formulation; any Eq. (13) label in older project notes is not the PDF
equation number.  Symmetry is explicit because identifying the mixed terms requires it. -/
theorem finiteMomentEnvironmentalRisk_eq_expandedEnvironmentalRisk
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (sigmaYSq : ℝ) (v betaStar b : Fin p → ℝ)
    (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar)
    (hOutcome : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar)
    (hSymm : ∀ e, (Sigma e).IsSymm) (e : Fin m) :
    finiteMomentEnvironmentalRisk (Sigma e) (c e) b (q e) =
      expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e) := by
  have hcDot : vectorDot (c e) b =
      vectorDot (Matrix.mulVec (Sigma e) betaStar) b - vectorDot v b := by
    simp only [vectorDot]
    calc
      (∑ i, c e i * b i) =
          ∑ i, (Matrix.mulVec (Sigma e) betaStar i - v i) * b i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hCross e i]
      _ = ∑ i, Matrix.mulVec (Sigma e) betaStar i * b i -
          ∑ i, v i * b i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hMixed :
      vectorDot betaStar (Matrix.mulVec (Sigma e) b) =
        vectorDot b (Matrix.mulVec (Sigma e) betaStar) :=
    vectorDot_mulVec_comm_of_isSymm (Sigma e) betaStar b (hSymm e)
  have hDotComm :
      vectorDot (Matrix.mulVec (Sigma e) betaStar) b =
        vectorDot b (Matrix.mulVec (Sigma e) betaStar) := by
    simp only [vectorDot]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hQuadExpand :
      matrixQuad (Sigma e) (primalDisplacement b betaStar) =
        matrixQuad (Sigma e) b -
          2 * vectorDot b (Matrix.mulVec (Sigma e) betaStar) +
          matrixQuad (Sigma e) betaStar := by
    have hMul : Matrix.mulVec (Sigma e) (primalDisplacement b betaStar) =
        Matrix.mulVec (Sigma e) b - Matrix.mulVec (Sigma e) betaStar := by
      funext i
      change (∑ j, (Sigma e) i j * (b j - betaStar j)) =
        (∑ j, (Sigma e) i j * b j) -
          ∑ j, (Sigma e) i j * betaStar j
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hMixed' :
        (∑ i, betaStar i * Matrix.mulVec (Sigma e) b i) =
          ∑ i, b i * Matrix.mulVec (Sigma e) betaStar i := by
      simpa only [vectorDot] using hMixed
    simp only [matrixQuad]
    rw [hMul]
    simp only [vectorDot, primalDisplacement, Pi.sub_apply]
    simp_rw [mul_sub, sub_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hMixed']
    ring
  have hvDot : vectorDot v (primalDisplacement b betaStar) =
      vectorDot v b - vectorDot v betaStar := by
    simp only [vectorDot, primalDisplacement, mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [finiteMomentEnvironmentalRisk, expandedEnvironmentalRisk, hOutcome e, hcDot,
    hQuadExpand, hvDot, hDotComm]
  ring

/-- The one-hot unpenalized dual sample oracle has the moment environmental risk as its
conditional mean. -/
theorem condExp_sampleUnpenalizedDualOracle
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (b : Omega → Fin p → ℝ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ i, AEStronglyMeasurable[mCond] (fun omega ↦ b omega i) mu)
    (hmCond : mCond ≤ mOmega)
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q) (j : Fin m) :
    Integrable (fun omega ↦ sampleUnpenalizedDualOracle
      (E omega) (X omega) (Y omega) (b omega) j) mu ∧
    mu[(fun omega ↦ sampleUnpenalizedDualOracle
      (E omega) (X omega) (Y omega) (b omega) j) | mCond] =ᵐ[mu]
      fun omega ↦ finiteMomentEnvironmentalRisk
        (Sigma j) (c j) (b omega) (q j) := by
  have hSelected := condExp_selectedResidualSq E X Y Sigma c q b B hB hb
    hbMeas hmCond hMom j
  have hPath :
      (fun omega ↦ sampleUnpenalizedDualOracle
        (E omega) (X omega) (Y omega) (b omega) j) =
      (fun omega ↦ (m : ℝ) * selectedResidualSq E X Y b j omega) := by
    funext omega
    simp only [sampleUnpenalizedDualOracle, selectedResidualSq,
      selectedEnvironmentTerm, selectedEnvironmentIndicator]
    ring
  rw [hPath]
  refine ⟨hSelected.1.const_mul (m : ℝ), ?_⟩
  have hScale := condExp_smul (μ := mu) (m : ℝ)
    (selectedResidualSq E X Y b j) mCond
  change mu[(fun omega ↦ (m : ℝ) * selectedResidualSq E X Y b j omega) | mCond] =ᵐ[mu]
    fun omega ↦ (m : ℝ) *
      (mu[selectedResidualSq E X Y b j | mCond]) omega at hScale
  filter_upwards [hScale, hSelected.2] with omega hscale hselected
  rw [hscale, hselected]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

/-- Penalized dual conditional mean. The current weight, not the comparator or next iterate,
appears in the predictable penalty correction. -/
theorem condExp_samplePenalizedDualOracle
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] (hmCond : mCond ≤ mOmega)
    [SigmaFinite (mu.trim hmCond)]
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ) (penalty B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ i, AEStronglyMeasurable[mCond] (fun omega ↦ b omega i) mu)
    (hwMeas : ∀ j, AEStronglyMeasurable[mCond] (fun omega ↦ w omega j) mu)
    (hw : ∀ omega, IsSimplex (w omega))
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q) (j : Fin m) :
    Integrable (fun omega ↦ samplePenalizedDualOracle penalty
      (E omega) (X omega) (Y omega) (b omega) (w omega) j) mu ∧
    mu[(fun omega ↦ samplePenalizedDualOracle penalty
      (E omega) (X omega) (Y omega) (b omega) (w omega) j) | mCond] =ᵐ[mu]
      fun omega ↦ finiteMomentEnvironmentalRisk
        (Sigma j) (c j) (b omega) (q j) - 2 * penalty * w omega j := by
  have hUnpen := condExp_sampleUnpenalizedDualOracle E X Y Sigma c q b B
    hm hB hb hbMeas hmCond hMom j
  have hwInt : Integrable (fun omega ↦ w omega j) mu := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((hwMeas j).mono hmCond)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (simplex_coordinate_bounds (hw omega) j).1]
    exact (simplex_coordinate_bounds (hw omega) j).2
  have hPenaltyInt : Integrable (fun omega ↦ 2 * penalty * w omega j) mu :=
    hwInt.const_mul (2 * penalty)
  have hTotalInt : Integrable (fun omega ↦ samplePenalizedDualOracle penalty
      (E omega) (X omega) (Y omega) (b omega) (w omega) j) mu := by
    change Integrable
      ((fun omega ↦ sampleUnpenalizedDualOracle
        (E omega) (X omega) (Y omega) (b omega) j) -
      (fun omega ↦ 2 * penalty * w omega j)) mu
    exact hUnpen.1.sub hPenaltyInt
  refine ⟨hTotalInt, ?_⟩
  change mu[(fun omega ↦ sampleUnpenalizedDualOracle
      (E omega) (X omega) (Y omega) (b omega) j -
        2 * penalty * w omega j) | mCond] =ᵐ[mu]
    fun omega ↦ finiteMomentEnvironmentalRisk
      (Sigma j) (c j) (b omega) (q j) - 2 * penalty * w omega j
  have hSub := condExp_sub hUnpen.1 hPenaltyInt mCond
  have hPenaltyMeas : AEStronglyMeasurable[mCond]
      (fun omega ↦ 2 * penalty * w omega j) mu :=
    (hwMeas j).const_mul (2 * penalty)
  have hPenaltyCond := condExp_of_aestronglyMeasurable' hmCond hPenaltyMeas hPenaltyInt
  change mu[(fun omega ↦ sampleUnpenalizedDualOracle
      (E omega) (X omega) (Y omega) (b omega) j -
        2 * penalty * w omega j) | mCond] =ᵐ[mu]
    fun omega ↦
      (mu[(fun omega ↦ sampleUnpenalizedDualOracle
        (E omega) (X omega) (Y omega) (b omega) j) | mCond]) omega -
      (mu[(fun omega ↦ 2 * penalty * w omega j) | mCond]) omega at hSub
  filter_upwards [hSub, hUnpen.2, hPenaltyCond] with omega hsub hunpen hpenalty
  rw [hsub, hunpen, hpenalty]

/-- Conditional mean of the actual primal sample oracle in finite-moment score form. -/
theorem condExp_samplePrimalOracle
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ) (gamma B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ j, AEStronglyMeasurable[mCond] (fun omega ↦ b omega j) mu)
    (hwMeas : ∀ e, AEStronglyMeasurable[mCond] (fun omega ↦ w omega e) mu)
    (hw : ∀ omega, IsSimplex (w omega))
    (hmCond : mCond ≤ mOmega)
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q) (i : Fin p) :
    Integrable (fun omega ↦ samplePrimalOracle gamma
      (E omega) (X omega) (Y omega) (b omega) (w omega) i) mu ∧
    mu[(fun omega ↦ samplePrimalOracle gamma
      (E omega) (X omega) (Y omega) (b omega) (w omega) i) | mCond] =ᵐ[mu]
      fun omega ↦ 2 * ∑ e,
        (w omega e - negDROGammaCoefficient m gamma) *
          finiteMomentEnvironmentalScore (Sigma e) (c e) (b omega) i := by
  let a := negDROGammaCoefficient m gamma
  let residual : Fin m → Omega → ℝ := fun e ↦
    selectedPrimalResidualCoordinate E X Y b e i
  let coeff : Fin m → Omega → ℝ := fun e omega ↦
    2 * (m : ℝ) * (w omega e - a)
  let term : Fin m → Omega → ℝ := fun e omega ↦ coeff e omega * residual e omega
  have hResidual : ∀ e,
      Integrable (residual e) mu ∧
      mu[residual e | mCond] =ᵐ[mu]
        fun omega ↦ (1 / (m : ℝ)) *
          finiteMomentEnvironmentalScore (Sigma e) (c e) (b omega) i := by
    intro e
    exact condExp_selectedPrimalResidualCoordinate E X Y Sigma c q b B hB hb
      hbMeas hmCond hMom e i
  have hCoeffMeas : ∀ e, AEStronglyMeasurable[mCond] (coeff e) mu := by
    intro e
    exact ((hwMeas e).sub aestronglyMeasurable_const).const_mul (2 * (m : ℝ))
  have hCoeffAmbient : ∀ e, AEStronglyMeasurable (coeff e) mu :=
    fun e ↦ (hCoeffMeas e).mono hmCond
  have hCoeffBound : ∀ e, ∀ omega,
      ‖coeff e omega‖ ≤ ‖(2 : ℝ) * (m : ℝ)‖ * (1 + ‖a‖) := by
    intro e omega
    have hwe := simplex_coordinate_bounds (hw omega) e
    have hwNorm : ‖w omega e‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hwe.1]
      exact hwe.2
    calc
      ‖coeff e omega‖ = ‖(2 : ℝ) * (m : ℝ)‖ * ‖w omega e - a‖ := by
        simp only [coeff, norm_mul]
      _ ≤ ‖(2 : ℝ) * (m : ℝ)‖ * (‖w omega e‖ + ‖a‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖(2 : ℝ) * (m : ℝ)‖ * (1 + ‖a‖) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hwNorm]) (norm_nonneg _)
  have hTermInt : ∀ e, Integrable (term e) mu := by
    intro e
    exact (hResidual e).1.bdd_mul (hCoeffAmbient e)
      (ae_of_all mu (fun omega ↦ hCoeffBound e omega))
  have hTermCond : ∀ e,
      mu[term e | mCond] =ᵐ[mu]
        fun omega ↦ coeff e omega *
          ((1 / (m : ℝ)) *
            finiteMomentEnvironmentalScore (Sigma e) (c e) (b omega) i) := by
    intro e
    exact condExp_predictable_mul_ae_eq (coeff e) (residual e)
      (fun omega ↦ (1 / (m : ℝ)) *
        finiteMomentEnvironmentalScore (Sigma e) (c e) (b omega) i)
      (hCoeffMeas e) (hResidual e).1 (hTermInt e) (hResidual e).2
  have hPath :
      (fun omega ↦ samplePrimalOracle gamma
        (E omega) (X omega) (Y omega) (b omega) (w omega) i) =
      (fun omega ↦ ∑ e, term e omega) := by
    funext omega
    simp only [samplePrimalOracle, term, coeff, residual,
      selectedPrimalResidualCoordinate, selectedEnvironmentTerm, a]
    have hSelect := selectedEnvironmentIndicator_sum_apply E
      (fun e ↦ w omega e - negDROGammaCoefficient m gamma) omega
    rw [hSelect]
    rw [show (2 * (m : ℝ) *
        ∑ e, selectedEnvironmentIndicator E e omega *
          (w omega e - negDROGammaCoefficient m gamma)) *
          (vectorDot (X omega) (b omega) - Y omega) * X omega i =
        (∑ e, selectedEnvironmentIndicator E e omega *
          (w omega e - negDROGammaCoefficient m gamma)) *
          (2 * (m : ℝ) * (vectorDot (X omega) (b omega) - Y omega) *
            X omega i) by ring]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _he
    ring
  have hSumInt : Integrable (fun omega ↦ ∑ e, term e omega) mu :=
    integrable_finsetSum Finset.univ (fun e _he ↦ hTermInt e)
  rw [hPath]
  refine ⟨hSumInt, ?_⟩
  have hSumCond := condExp_finset_sum_apply (mCond := mCond) Finset.univ term
    (fun e _he ↦ hTermInt e)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  filter_upwards [hSumCond, ae_all_iff.2 hTermCond] with omega hsum hterm
  rw [hsum]
  simp_rw [hterm]
  dsimp [coeff, a]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  field_simp

/-- The weighted finite-moment score is exactly the existing expanded primal coefficient. -/
theorem weighted_finiteMomentEnvironmentalScore_eq_expandedPrimalCoefficient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (gamma : ℝ) (v betaStar b : Fin p → ℝ)
    (w : Fin m → ℝ) (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar)
    (i : Fin p) :
    2 * ∑ e, (w e - negDROGammaCoefficient m gamma) *
        finiteMomentEnvironmentalScore (Sigma e) (c e) b i =
      expandedPrimalCoefficient Sigma gamma v b betaStar w i := by
  simp_rw [finiteMomentEnvironmentalScore_eq Sigma c v betaStar b hCross]
  simp only [expandedPrimalCoefficient, negDROAlpha, negDROQ,
    Matrix.sum_mulVec, Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring_nf
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _he
    ring
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _he
    ring

/-- Actual primal-oracle conditional unbiasedness, derived from fresh finite monomial moments. -/
theorem samplePrimalOracle_condUnbiased_expanded
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma : ℝ) (v betaStar : Fin p → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ j, AEStronglyMeasurable[mCond] (fun omega ↦ b omega j) mu)
    (hwMeas : ∀ e, AEStronglyMeasurable[mCond] (fun omega ↦ w omega e) mu)
    (hw : ∀ omega, IsSimplex (w omega)) (hmCond : mCond ≤ mOmega)
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q)
    (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar) (i : Fin p) :
    (fun omega ↦ expandedPrimalCoefficient Sigma gamma v
      (b omega) betaStar (w omega) i) =ᵐ[mu]
    mu[(fun omega ↦ samplePrimalOracle gamma
      (E omega) (X omega) (Y omega) (b omega) (w omega) i) | mCond] := by
  have hCond := (condExp_samplePrimalOracle E X Y Sigma c q b w gamma B
    hm hB hb hbMeas hwMeas hw hmCond hMom i).2
  filter_upwards [hCond] with omega hcond
  rw [hcond]
  exact (weighted_finiteMomentEnvironmentalScore_eq_expandedPrimalCoefficient
    Sigma c gamma v betaStar (b omega) (w omega) hCross i).symm

/-- Actual unpenalized dual-oracle conditional unbiasedness in the existing expanded model. -/
theorem sampleUnpenalizedDualOracle_condUnbiased_expanded
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (b : Omega → Fin p → ℝ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ i, AEStronglyMeasurable[mCond] (fun omega ↦ b omega i) mu)
    (hmCond : mCond ≤ mOmega)
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q)
    (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar)
    (hOutcome : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar)
    (hSymm : ∀ e, (Sigma e).IsSymm) (j : Fin m) :
    (fun omega ↦ expandedDualGradient Sigma sigmaYSq v (b omega) betaStar j) =ᵐ[mu]
    mu[(fun omega ↦ sampleUnpenalizedDualOracle
      (E omega) (X omega) (Y omega) (b omega) j) | mCond] := by
  have hCond := (condExp_sampleUnpenalizedDualOracle E X Y Sigma c q b B
    hm hB hb hbMeas hmCond hMom j).2
  filter_upwards [hCond] with omega hcond
  rw [hcond]
  exact (finiteMomentEnvironmentalRisk_eq_expandedEnvironmentalRisk Sigma c q
    sigmaYSq v betaStar (b omega) hCross hOutcome hSymm j).symm

/-- Actual penalized dual-oracle conditional unbiasedness in the existing expanded model. -/
theorem samplePenalizedDualOracle_condUnbiased_expanded
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] (hmCond : mCond ≤ mOmega)
    [SigmaFinite (mu.trim hmCond)]
    {m p : ℕ} (E : Omega → Fin m) (X : Omega → Fin p → ℝ) (Y : Omega → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (sigmaYSq penalty : ℝ) (v betaStar : Fin p → ℝ)
    (b : Omega → Fin p → ℝ) (w : Omega → Fin m → ℝ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2)
    (hbMeas : ∀ i, AEStronglyMeasurable[mCond] (fun omega ↦ b omega i) mu)
    (hwMeas : ∀ j, AEStronglyMeasurable[mCond] (fun omega ↦ w omega j) mu)
    (hw : ∀ omega, IsSimplex (w omega))
    (hMom : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond)
      mu E X Y Sigma c q)
    (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar)
    (hOutcome : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar)
    (hSymm : ∀ e, (Sigma e).IsSymm) (j : Fin m) :
    (fun omega ↦ expandedPenalizedDualGradient Sigma sigmaYSq v
      (b omega) betaStar (w omega) penalty j) =ᵐ[mu]
    mu[(fun omega ↦ samplePenalizedDualOracle penalty
      (E omega) (X omega) (Y omega) (b omega) (w omega) j) | mCond] := by
  have hCond := (condExp_samplePenalizedDualOracle hmCond E X Y Sigma c q b w
    penalty B hm hB hb hbMeas hwMeas hw hMom j).2
  filter_upwards [hCond] with omega hcond
  rw [hcond]
  rw [expandedPenalizedDualGradient]
  congr 1
  exact (finiteMomentEnvironmentalRisk_eq_expandedEnvironmentalRisk Sigma c q
    sigmaYSq v betaStar (b omega) hCross hOutcome hSymm j).symm

/-- Both conditional-unbiasedness statements for one actual coupled trajectory round. No
independence between the primal and dual sample oracles is used. -/
theorem concreteTrajectory_condUnbiased_expanded
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (hCommon : FreshConcreteCommonAssumptions mu mCond C P bInit betaStar Sigma
      gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat)
    (hCross : HasNegDROCrossMomentRelation Sigma c v betaStar)
    (hOutcome : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar)
    (hSymm : ∀ e, (Sigma e).IsSymm) (t : ℕ) (ht : t < T)
    (hPop : HasFreshFiniteEnvironmentPopulationMoments (mCond := mCond t)
      mu (eHat t) (xHat t) (yHat t) Sigma c q) :
    (∀ i,
      (fun omega ↦ expandedPrimalCoefficient Sigma gamma v
        (concreteNegDROState P bInit gamma penalty etaB etaW
          eHat xHat yHat t omega).1 betaStar
        (concreteNegDROState P bInit gamma penalty etaB etaW
          eHat xHat yHat t omega).2 i) =ᵐ[mu]
      mu[(fun omega ↦ concreteTrajectoryPrimalOracle P bInit gamma penalty
        etaB etaW eHat xHat yHat t omega i) | mCond t]) ∧
    (∀ j,
      (fun omega ↦ expandedPenalizedDualGradient Sigma sigmaYSq v
        (concreteNegDROState P bInit gamma penalty etaB etaW
          eHat xHat yHat t omega).1 betaStar
        (concreteNegDROState P bInit gamma penalty etaB etaW
          eHat xHat yHat t omega).2 penalty j) =ᵐ[mu]
      mu[(fun omega ↦ concreteTrajectoryDualOracle P bInit gamma penalty
        etaB etaW eHat xHat yHat t omega j) | mCond t]) := by
  let gB := concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW
    eHat xHat yHat
  let gW := concreteTrajectoryDualOracle P bInit gamma penalty etaB etaW
    eHat xHat yHat
  let b : Omega → Fin p → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega).1
  let w : Omega → Fin m → ℝ := fun omega ↦
    (concreteNegDROState P bInit gamma penalty etaB etaW
      eHat xHat yHat t omega).2
  have hbMeas : ∀ i, AEStronglyMeasurable[mCond t]
      (fun omega ↦ b omega i) mu := by
    intro i
    have hTrajectory := randomPrimalTrajectory_coordinate_aestronglyMeasurable
      (mu := mu) mCond P bInit etaB gB hCommon.hMono hCommon.hPMeas
      hCommon.hPrimalMeas t i
    refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
    dsimp [b, gB]
    rw [concreteNegDROState_primal_eq_randomPrimalTrajectory]
  have hwMeas : ∀ e, AEStronglyMeasurable[mCond t]
      (fun omega ↦ w omega e) mu := by
    intro e
    have hTrajectory := randomEGTrajectory_coordinate_aestronglyMeasurable
      (mu := mu) mCond gW etaW hCommon.hMono hCommon.hDualMeas t e
    refine hTrajectory.congr (ae_of_all mu (fun omega ↦ ?_))
    dsimp [w, gW]
    rw [concreteNegDROState_dual_eq_randomEGTrajectory]
  have hb : ∀ omega, sqNorm (b omega) ≤ B ^ 2 := fun omega ↦ hCommon.hCBall _
    (concreteNegDROState_primal_mem C P bInit gamma penalty etaB etaW eHat xHat yHat
      hCommon.hInit hCommon.hPFeas t omega)
  have hw : ∀ omega, IsSimplex (w omega) := fun omega ↦
    concreteNegDROState_dual_isSimplex P bInit gamma penalty etaB etaW eHat xHat yHat
      hCommon.hm t omega
  constructor
  · intro i
    simpa only [b, w, gB, concreteTrajectoryPrimalOracle] using
      samplePrimalOracle_condUnbiased_expanded (eHat t) (xHat t) (yHat t)
        Sigma c q gamma v betaStar b w B hCommon.hm hCommon.hB hb hbMeas hwMeas hw
        (hCommon.hmCond t) hPop hCross i
  · intro j
    simpa only [b, w, gW, concreteTrajectoryDualOracle] using
      samplePenalizedDualOracle_condUnbiased_expanded (hCommon.hmCond t)
        (eHat t) (xHat t) (yHat t) Sigma c q sigmaYSq penalty v betaStar b w B
        hCommon.hm hCommon.hB hb hbMeas hwMeas hw hPop hCross hOutcome hSymm j

/-- Stage-2 unpenalized assumptions: raw selected moments and population monomials replace both
the adaptive raw-moment and conditional-unbiasedness interfaces. -/
structure FreshSamplingConcreteUnpenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
  common : FreshConcreteCommonAssumptions mu mCond C P bInit betaStar Sigma
    gamma lam 0 w0 etaB etaW B KX KY T eHat xHat yHat
  population : ∀ t < T, HasFreshFiniteEnvironmentPopulationMoments
    (mCond := mCond t) mu (eHat t) (xHat t) (yHat t) Sigma c q
  crossRelation : HasNegDROCrossMomentRelation Sigma c v betaStar
  outcomeRelation : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar
  sigmaSymm : ∀ e, (Sigma e).IsSymm

/-- Stage-2 penalized assumptions with the same primitive population-moment realization. -/
structure FreshSamplingConcretePenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} (mu : Measure Omega)
    {m p : ℕ} (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ) : Prop where
  common : FreshConcreteCommonAssumptions mu mCond C P bInit betaStar Sigma
    gamma lam penalty w0 etaB etaW B KX KY T eHat xHat yHat
  hpenalty : 0 ≤ penalty
  population : ∀ t < T, HasFreshFiniteEnvironmentPopulationMoments
    (mCond := mCond t) mu (eHat t) (xHat t) (yHat t) Sigma c q
  crossRelation : HasNegDROCrossMomentRelation Sigma c v betaStar
  outcomeRelation : HasNegDROOutcomeMomentRelation Sigma q sigmaYSq v betaStar
  sigmaSymm : ∀ e, (Sigma e).IsSymm

/-- Construct the Stage-1 unpenalized interface, deriving both unbiasedness fields. -/
theorem FreshSamplingConcreteUnpenalizedAssumptions.toFreshConcreteUnpenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    FreshConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat := by
  refine { common := h.common, hPrimalCondUnbiased := ?_, hDualCondUnbiased := ?_ }
  · intro t ht i
    have hRound := concreteTrajectory_condUnbiased_expanded mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam 0 v w0 etaB etaW B KX KY T eHat xHat yHat
      h.common h.crossRelation h.outcomeRelation h.sigmaSymm t ht (h.population t ht)
    simpa only [stochasticExpandedPrimalCoefficient,
      concreteNegDROState_primal_eq_randomPrimalTrajectory,
      concreteNegDROState_dual_eq_randomEGTrajectory] using hRound.1 i
  · intro t ht j
    have hRound := concreteTrajectory_condUnbiased_expanded mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam 0 v w0 etaB etaW B KX KY T eHat xHat yHat
      h.common h.crossRelation h.outcomeRelation h.sigmaSymm t ht (h.population t ht)
    simpa only [expandedPenalizedDualGradient, expandedDualGradient, zero_mul, mul_zero, sub_zero,
      concreteNegDROState_primal_eq_randomPrimalTrajectory,
      concreteNegDROState_dual_eq_randomEGTrajectory] using hRound.2 j

/-- Construct the Stage-1 penalized interface, deriving both unbiasedness fields. -/
theorem FreshSamplingConcretePenalizedAssumptions.toFreshConcretePenalizedAssumptions
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ)
    (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcretePenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
      eHat xHat yHat) :
    FreshConcretePenalizedAssumptions mu mCond C P bInit betaStar Sigma
      gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat := by
  refine {
    common := h.common
    hpenalty := h.hpenalty
    hPrimalCondUnbiased := ?_
    hDualCondUnbiased := ?_ }
  · intro t ht i
    have hRound := concreteTrajectory_condUnbiased_expanded mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
      eHat xHat yHat h.common h.crossRelation h.outcomeRelation h.sigmaSymm
      t ht (h.population t ht)
    simpa only [stochasticExpandedPenalizedPrimalCoefficient,
      expandedPenalizedPrimalCoefficient,
      concreteNegDROState_primal_eq_randomPrimalTrajectory,
      concreteNegDROState_dual_eq_randomEGTrajectory] using hRound.1 i
  · intro t ht j
    have hRound := concreteTrajectory_condUnbiased_expanded mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
      eHat xHat yHat h.common h.crossRelation h.outcomeRelation h.sigmaSymm
      t ht (h.population t ht)
    simpa only [concreteNegDROState_primal_eq_randomPrimalTrajectory,
      concreteNegDROState_dual_eq_randomEGTrajectory] using hRound.2 j

/-- Finite-time unpenalized convergence from weight-independent raw moments and fresh finite
population monomials; conditional unbiasedness is no longer an assumption. -/
theorem stochasticNegDRO_sampling_unpenalized_convergence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) :=
  stochasticNegDRO_fresh_unpenalized_convergence mCond C P bInit betaStar Sigma
    gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat
    (h.toFreshConcreteUnpenalizedAssumptions mCond C P bInit betaStar Sigma c q
      gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat)

/-- Unpenalized averaged-iterate convergence under the Stage-2 sampling interface. -/
theorem stochasticNegDRO_sampling_unpenalized_averaged_convergence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma 0 etaB etaW eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitUnpenalizedDualGradSqBound m B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  apply stochasticNegDRO_concrete_unpenalized_averaged_convergence
  exact (h.toFreshConcreteUnpenalizedAssumptions mCond C P bInit betaStar Sigma c q
    gamma sigmaYSq lam v w0 etaB etaW B KX KY T eHat xHat yHat).toConcreteUnpenalizedAssumptions
      mCond C P bInit betaStar Sigma gamma sigmaYSq lam v w0 etaB etaW B KX KY T
      eHat xHat yHat

/-- Unpenalized inverse-square-root rate under the Stage-2 sampling interface. -/
theorem stochasticNegDRO_sampling_unpenalized_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcreteUnpenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam v w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma 0
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam v +
        explicitUnpenalizedRateConstant m bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) :=
  stochasticNegDRO_fresh_unpenalized_invSqrt_rate mCond C P bInit betaStar Sigma
    gamma sigmaYSq lam v w0 B KX KY T eHat xHat yHat
    (h.toFreshConcreteUnpenalizedAssumptions mCond C P bInit betaStar Sigma c q
      gamma sigmaYSq lam v w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)

/-- Finite-time penalized convergence under the Stage-2 sampling interface. -/
theorem stochasticNegDRO_sampling_penalized_convergence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcretePenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
      eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit etaB
          (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
          betaStar t ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) :=
  stochasticNegDRO_fresh_penalized_convergence mCond C P bInit betaStar Sigma
    gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat
    (h.toFreshConcretePenalizedAssumptions mCond C P bInit betaStar Sigma c q
      gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat)

/-- Penalized averaged-iterate convergence under the Stage-2 sampling interface. -/
theorem stochasticNegDRO_sampling_penalized_averaged_convergence
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (etaB etaW B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcretePenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T
      eHat xHat yHat) :
    (∫ omega, sqDist
      (randomPrimalAverage T (fun t omega ↦ randomPrimalTrajectory P bInit etaB
        (concreteTrajectoryPrimalOracle P bInit gamma penalty etaB etaW eHat xHat yHat)
        t omega) omega) betaStar ∂mu) ≤
      sqDist bInit betaStar / (2 * lam * etaB * (T : ℝ)) +
      (sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2)) / lam +
      2 * penalty / lam +
      2 * Real.log (m : ℝ) / (lam * etaW * (T : ℝ)) +
      etaW / lam * explicitPenalizedDualGradSqBound m penalty B KX KY +
      etaB * explicitPrimalGradSqBound m B KX KY / (2 * lam) := by
  apply stochasticNegDRO_concrete_penalized_averaged_convergence
  exact (h.toFreshConcretePenalizedAssumptions mCond C P bInit betaStar Sigma c q
    gamma sigmaYSq lam penalty v w0 etaB etaW B KX KY T eHat xHat yHat).toConcretePenalizedAssumptions
      mCond C P bInit betaStar Sigma gamma sigmaYSq lam penalty v w0 etaB etaW
      B KX KY T eHat xHat yHat

/-- Penalized inverse-square-root rate under the Stage-2 sampling interface. -/
theorem stochasticNegDRO_sampling_penalized_invSqrt_rate
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] {m p : ℕ}
    (mCond : ℕ → MeasurableSpace Omega)
    (C : Set (Fin p → ℝ)) (P : (Fin p → ℝ) → Fin p → ℝ)
    (bInit betaStar : Fin p → ℝ) (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (c : Fin m → Fin p → ℝ) (q : Fin m → ℝ)
    (gamma sigmaYSq lam penalty : ℝ) (v : Fin p → ℝ) (w0 : Fin m → ℝ)
    (B KX KY : ℝ) (T : ℕ)
    (eHat : ℕ → Omega → Fin m) (xHat : ℕ → Omega → Fin p → ℝ)
    (yHat : ℕ → Omega → ℝ)
    (h : FreshSamplingConcretePenalizedAssumptions mu mCond C P bInit betaStar
      Sigma c q gamma sigmaYSq lam penalty v w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        expectedPrimalTrajectoryDistSq (mu := mu) P bInit
          (1 / Real.sqrt (T : ℝ))
          (concreteTrajectoryPrimalOracle P bInit gamma penalty
            (1 / Real.sqrt (T : ℝ)) (1 / Real.sqrt (T : ℝ)) eHat xHat yHat)
          betaStar t ≤
      explicitIdentificationBias m gamma lam v + 2 * penalty / lam +
        explicitPenalizedRateConstant m penalty bInit betaStar lam B KX KY /
          Real.sqrt (T : ℝ) :=
  stochasticNegDRO_fresh_penalized_invSqrt_rate mCond C P bInit betaStar Sigma
    gamma sigmaYSq lam penalty v w0 B KX KY T eHat xHat yHat
    (h.toFreshConcretePenalizedAssumptions mCond C P bInit betaStar Sigma c q
      gamma sigmaYSq lam penalty v w0 (1 / Real.sqrt (T : ℝ))
      (1 / Real.sqrt (T : ℝ)) B KX KY T eHat xHat yHat)

end NegDRO
