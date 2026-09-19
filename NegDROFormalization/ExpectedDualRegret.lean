import NegDROFormalization.DualObjectiveLinearization
import NegDROFormalization.PredictableVectorPairing

/-!
# One-round expected dual regret

This module connects actual expanded-objective comparator regret to a sampled dual-gradient
pairing for one fixed round and one conditioning sigma-algebra. The logical chain is

`E[regret] <= E[<population coefficient, comparator - current>]`
`             = E[<sampled gradient, comparator - current>]`.

The first relation is deterministic objective linearization (an equality in the unpenalized
case and concavity in the penalized case). The second is coordinatewise conditional
unbiasedness plus predictability and boundedness of the displacement. No conditional
independence between primal and dual stochastic gradients is required. No filtration,
trajectory, cumulative regret, moment bound, or convergence theorem is defined here.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace NegDRO

/-- Generic expectation bridge from population linearization to a sampled-gradient pairing.
The comparison with the population pairing and the conditional-unbiasedness identity are kept
as separate inputs and proof steps. -/
theorem expected_regret_le_sampled_pairing
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {q : ℕ} (hm : mCond ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (regret : Omega → ℝ) (gHat F d : Omega → Fin q → ℝ)
    (hRegretInt : Integrable regret mu)
    (hPopulationLinearization :
      regret ≤ᵐ[mu] fun omega => vectorDot (F omega) (d omega))
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hdMeas : ∀ i,
      AEStronglyMeasurable[mCond] (fun omega => d omega i) mu)
    (displacementBound : ℝ)
    (hdBound : ∀ i, ∀ᵐ omega ∂mu, ‖d omega i‖ ≤ displacementBound)
    (hCondUnbiased : ∀ i,
      (fun omega => F omega i) =ᵐ[mu]
        mu[(fun omega => gHat omega i) | mCond]) :
    (∫ omega, regret omega ∂mu) ≤
      ∫ omega, vectorDot (gHat omega) (d omega) ∂mu := by
  have hFInt : ∀ i, Integrable (fun omega => F omega i) mu := by
    intro i
    have hCondInt :
        Integrable (mu[(fun omega => gHat omega i) | mCond]) mu :=
      integrable_condExp
    exact hCondInt.congr (hCondUnbiased i).symm
  have hPopulationPairInt :
      Integrable (fun omega => vectorDot (F omega) (d omega)) mu := by
    simp only [vectorDot]
    apply integrable_finsetSum Finset.univ
    intro i _hi
    have hdAmbient :
        AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
      (hdMeas i).mono hm
    exact (hFInt i).mul_bdd hdAmbient (hdBound i)
  have hObjectiveStep :
      (∫ omega, regret omega ∂mu) ≤
        ∫ omega, vectorDot (F omega) (d omega) ∂mu :=
    integral_mono_ae hRegretInt hPopulationPairInt hPopulationLinearization
  have hUnbiasedStep :
      (∫ omega, vectorDot (gHat omega) (d omega) ∂mu) =
        ∫ omega, vectorDot (F omega) (d omega) ∂mu :=
    integral_vectorDot_eq_of_coordinatewise_condExp_ae_eq
      hm gHat F d hgHatInt hdMeas displacementBound hdBound hCondUnbiased
  calc
    (∫ omega, regret omega ∂mu) ≤
        ∫ omega, vectorDot (F omega) (d omega) ∂mu := hObjectiveStep
    _ = ∫ omega, vectorDot (gHat omega) (d omega) ∂mu := hUnbiasedStep.symm

/-- The actual random unpenalized comparator regret: expanded objective at the fixed comparator
minus expanded objective at the current dual point, both at the same random primal point. -/
noncomputable def randomExpandedUnpenalizedRegret
    {Omega : Type*} {mEnv p : ℕ}
    (Sigma : Fin mEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin mEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin mEnv → ℝ) : Omega → ℝ :=
  fun omega =>
    expandedUnpenalizedRegret Sigma gamma sigmaYSq v (b omega) betaStar u (w omega)

/-- The actual random penalized comparator regret, with the same penalty at comparator and
current dual point. -/
noncomputable def randomExpandedPenalizedRegret
    {Omega : Type*} {mEnv p : ℕ}
    (Sigma : Fin mEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin mEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w : Omega → Fin mEnv → ℝ) (penalty : ℝ) : Omega → ℝ :=
  fun omega =>
    expandedPenalizedRegret Sigma gamma sigmaYSq v (b omega) betaStar
      u (w omega) penalty

/-- Expected unpenalized objective regret equals the sampled dual-gradient pairing. Regret
integrability is derived from the exact deterministic objective identity and integrability of
the population pairing. -/
theorem integral_randomExpandedUnpenalizedRegret_eq_sampled_pairing
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {mEnv p : ℕ} (hm : mCond ≤ mOmega) [SigmaFinite (mu.trim hm)]
    (Sigma : Fin mEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin mEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w gHat : Omega → Fin mEnv → ℝ)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => primalDisplacement u (w omega) i) mu)
    (displacementBound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement u (w omega) i‖ ≤ displacementBound)
    (hCondUnbiased : ∀ i,
      (fun omega =>
        expandedDualGradient Sigma sigmaYSq v (b omega) betaStar i) =ᵐ[mu]
      mu[(fun omega => gHat omega i) | mCond]) :
    (∫ omega,
        randomExpandedUnpenalizedRegret Sigma gamma sigmaYSq v betaStar u b w omega ∂mu) =
      ∫ omega, vectorDot (gHat omega) (primalDisplacement u (w omega)) ∂mu := by
  let F : Omega → Fin mEnv → ℝ :=
    fun omega => expandedDualGradient Sigma sigmaYSq v (b omega) betaStar
  let d : Omega → Fin mEnv → ℝ :=
    fun omega => primalDisplacement u (w omega)
  have hFInt : ∀ i, Integrable (fun omega => F omega i) mu := by
    intro i
    have hCondInt :
        Integrable (mu[(fun omega => gHat omega i) | mCond]) mu :=
      integrable_condExp
    exact hCondInt.congr (by simpa [F] using (hCondUnbiased i).symm)
  have hPopulationPairInt :
      Integrable (fun omega => vectorDot (F omega) (d omega)) mu := by
    simp only [vectorDot]
    apply integrable_finsetSum Finset.univ
    intro i _hi
    have hdAmbient :
        AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
      (hDisplacementMeas i).mono hm
    exact (hFInt i).mul_bdd hdAmbient (hDisplacementBound i)
  have hObjectiveIdentity :
      (fun omega =>
        randomExpandedUnpenalizedRegret Sigma gamma sigmaYSq v betaStar u b w omega) =
      (fun omega => vectorDot (F omega) (d omega)) := by
    funext omega
    exact expandedUnpenalizedRegret_eq_linearization
      Sigma gamma sigmaYSq v (b omega) betaStar u (w omega)
  have _hRegretInt :
      Integrable
        (randomExpandedUnpenalizedRegret Sigma gamma sigmaYSq v betaStar u b w) mu :=
    hPopulationPairInt.congr (Eventually.of_forall (fun omega => by
      exact congrFun hObjectiveIdentity omega |>.symm))
  have hPairing :
      (∫ omega, vectorDot (gHat omega) (d omega) ∂mu) =
        ∫ omega, vectorDot (F omega) (d omega) ∂mu :=
    integral_vectorDot_eq_of_coordinatewise_condExp_ae_eq
      hm gHat F d hgHatInt hDisplacementMeas displacementBound
      hDisplacementBound (by simpa [F] using hCondUnbiased)
  calc
    (∫ omega,
        randomExpandedUnpenalizedRegret Sigma gamma sigmaYSq v betaStar u b w omega ∂mu) =
        ∫ omega, vectorDot (F omega) (d omega) ∂mu := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun omega => congrFun hObjectiveIdentity omega)
    _ = ∫ omega, vectorDot (gHat omega) (d omega) ∂mu := hPairing.symm
    _ = ∫ omega, vectorDot (gHat omega) (primalDisplacement u (w omega)) ∂mu := by
      rfl

/-- Under a finite measure, finite coordinatewise a.e. measurability and a common coordinate
bound imply integrability of the explicit squared norm. -/
theorem integrable_sqNorm_of_coordinatewise_aestronglyMeasurable_of_bound
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {q : ℕ} [IsFiniteMeasure mu] (x : Omega → Fin q → ℝ)
    (hxMeas : ∀ i,
      AEStronglyMeasurable[mOmega] (fun omega => x omega i) mu)
    (bound : ℝ) (hxBound : ∀ i, ∀ᵐ omega ∂mu, ‖x omega i‖ ≤ bound) :
    Integrable (fun omega => sqNorm (x omega)) mu := by
  simp only [sqNorm]
  apply integrable_finsetSum Finset.univ
  intro i _hi
  apply Integrable.of_bound ((hxMeas i).pow 2) (bound ^ 2)
  filter_upwards [hxBound i] with omega homega
  change ‖(x omega i) ^ 2‖ ≤ bound ^ 2
  rw [norm_pow]
  nlinarith [norm_nonneg (x omega i)]

/-- Expected penalized objective regret is at most the sampled dual-gradient pairing. The
population penalized coefficient is evaluated at the current point `w omega`, and regret
integrability is derived using the exact remainder
`-penalty * sqNorm (u - w omega)`. -/
theorem integral_randomExpandedPenalizedRegret_le_sampled_pairing
    {Omega : Type*} {mCond mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {mEnv p : ℕ} [IsFiniteMeasure mu] (hm : mCond ≤ mOmega)
    (Sigma : Fin mEnv → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq penalty : ℝ) (v betaStar : Fin p → ℝ)
    (u : Fin mEnv → ℝ) (b : Omega → Fin p → ℝ)
    (w gHat : Omega → Fin mEnv → ℝ) (hPenalty : 0 ≤ penalty)
    (hgHatInt : ∀ i, Integrable (fun omega => gHat omega i) mu)
    (hDisplacementMeas : ∀ i,
      AEStronglyMeasurable[mCond]
        (fun omega => primalDisplacement u (w omega) i) mu)
    (displacementBound : ℝ)
    (hDisplacementBound : ∀ i, ∀ᵐ omega ∂mu,
      ‖primalDisplacement u (w omega) i‖ ≤ displacementBound)
    (hCondUnbiased : ∀ i,
      (fun omega =>
        expandedPenalizedDualGradient Sigma sigmaYSq v (b omega) betaStar
          (w omega) penalty i) =ᵐ[mu]
      mu[(fun omega => gHat omega i) | mCond]) :
    (∫ omega,
        randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar
          u b w penalty omega ∂mu) ≤
      ∫ omega, vectorDot (gHat omega) (primalDisplacement u (w omega)) ∂mu := by
  let F : Omega → Fin mEnv → ℝ := fun omega =>
    expandedPenalizedDualGradient Sigma sigmaYSq v (b omega) betaStar
      (w omega) penalty
  let d : Omega → Fin mEnv → ℝ :=
    fun omega => primalDisplacement u (w omega)
  have hFInt : ∀ i, Integrable (fun omega => F omega i) mu := by
    intro i
    have hCondInt :
        Integrable (mu[(fun omega => gHat omega i) | mCond]) mu :=
      integrable_condExp
    exact hCondInt.congr (by simpa [F] using (hCondUnbiased i).symm)
  have hPopulationPairInt :
      Integrable (fun omega => vectorDot (F omega) (d omega)) mu := by
    simp only [vectorDot]
    apply integrable_finsetSum Finset.univ
    intro i _hi
    have hdAmbient :
        AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
      (hDisplacementMeas i).mono hm
    exact (hFInt i).mul_bdd hdAmbient (hDisplacementBound i)
  have hdMeasAmbient : ∀ i,
      AEStronglyMeasurable[mOmega] (fun omega => d omega i) mu :=
    fun i => (hDisplacementMeas i).mono hm
  have hSqDisplacementInt :
      Integrable (fun omega => sqNorm (d omega)) mu :=
    integrable_sqNorm_of_coordinatewise_aestronglyMeasurable_of_bound
      d hdMeasAmbient displacementBound hDisplacementBound
  have hPenaltyRemainderInt :
      Integrable (fun omega => penalty * sqNorm (d omega)) mu :=
    hSqDisplacementInt.const_mul penalty
  have hExactRemainder :
      (fun omega =>
        randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar
          u b w penalty omega) =
      (fun omega =>
        vectorDot (F omega) (d omega) - penalty * sqNorm (d omega)) := by
    funext omega
    exact expandedPenalizedObjective_sub_eq_linearization_sub_remainder
      Sigma gamma sigmaYSq v (b omega) betaStar u (w omega) penalty
  have hRegretInt :
      Integrable
        (randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar
          u b w penalty) mu :=
    (hPopulationPairInt.sub hPenaltyRemainderInt).congr
      (Eventually.of_forall (fun omega => congrFun hExactRemainder omega |>.symm))
  have hObjectiveLinearization :
      (randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar
        u b w penalty) ≤ᵐ[mu]
      fun omega => vectorDot (F omega) (d omega) :=
    Eventually.of_forall (fun omega =>
      expandedPenalizedRegret_le_linearization
        Sigma gamma sigmaYSq v (b omega) betaStar u (w omega) penalty hPenalty)
  exact expected_regret_le_sampled_pairing hm
    (randomExpandedPenalizedRegret Sigma gamma sigmaYSq v betaStar
      u b w penalty)
    gHat F d hRegretInt hObjectiveLinearization hgHatInt
    hDisplacementMeas displacementBound hDisplacementBound
    (by simpa [F] using hCondUnbiased)

/-- Simplex membership gives the coordinatewise bound later used for the predictable dual
displacement. The comparator may lie on the simplex boundary. -/
theorem abs_simplex_displacement_le_one
    {q : ℕ} {u w : Fin q → ℝ} (hu : IsSimplex u) (hw : IsSimplex w)
    (i : Fin q) :
    |primalDisplacement u w i| ≤ 1 := by
  have hui := simplex_coordinate_bounds hu i
  have hwi := simplex_coordinate_bounds hw i
  rw [primalDisplacement]
  rw [abs_le]
  constructor <;> linarith

end NegDRO
