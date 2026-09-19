import NegDROFormalization.PopulationExpansion

/-!
# Concrete comparator reductions for the expanded NegDRO objective

This module instantiates the scalar comparator identities with the actual finite-dimensional
expanded objectives. Regret is defined as a signed objective difference; it is never assumed
to be nonnegative. Curvature is required only at the fixed comparator `w₀`.
-/

set_option autoImplicit false

namespace NegDRO

/-- Signed unpenalized comparator regret at a common primal point `b`. -/
noncomputable def expandedUnpenalizedRegret
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ) : ℝ :=
  expandedObjective Sigma gamma sigmaYSq v b betaStar w₀ -
    expandedObjective Sigma gamma sigmaYSq v b betaStar wₜ

/-- Signed penalized comparator regret at a common primal point `b`. -/
noncomputable def expandedPenalizedRegret
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ) (mu : ℝ) : ℝ :=
  expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar w₀ mu -
    expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar wₜ mu

/-- Concrete Appendix Eq. (66). It applies Eq. (64) to `w₀` and `wₜ` at the same primal
point, so both decompositions contain exactly the same `expandedCommonTerm`. -/
theorem expandedUnpenalizedComparatorIdentity
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma)
    (hw₀ : IsSimplex w₀) (hwₜ : IsSimplex wₜ) :
    fixedWitnessDirectionalForm Sigma gamma wₜ v (primalDisplacement b betaStar) =
      fixedWitnessDirectionalForm Sigma gamma w₀ v (primalDisplacement b betaStar) -
        2 * expandedUnpenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ := by
  have hL₀ := expandedObjective_eq_directionalForm_add_common
    Sigma gamma sigmaYSq v b betaStar w₀ hm hgamma hw₀
  have hLₜ := expandedObjective_eq_directionalForm_add_common
    Sigma gamma sigmaYSq v b betaStar wₜ hm hgamma hwₜ
  exact unpenalized_comparator_identity
    (expandedObjective Sigma gamma sigmaYSq v b betaStar w₀)
    (expandedObjective Sigma gamma sigmaYSq v b betaStar wₜ)
    (fixedWitnessDirectionalForm Sigma gamma w₀ v (primalDisplacement b betaStar))
    (fixedWitnessDirectionalForm Sigma gamma wₜ v (primalDisplacement b betaStar))
    (expandedCommonTerm m gamma sigmaYSq v b betaStar)
    (expandedUnpenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ)
    hL₀ hLₜ rfl

/-- Concrete Appendix Eq. (67), derived from the actual expanded penalized objective and its
Eq. (65) decomposition. No sign condition on this regret or on `mu` is needed for the identity. -/
theorem expandedPenalizedComparatorIdentity
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ) (mu : ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma)
    (hw₀ : IsSimplex w₀) (hwₜ : IsSimplex wₜ) :
    penalizedFixedWitnessDirectionalForm Sigma gamma wₜ v
        (primalDisplacement b betaStar) mu =
      penalizedFixedWitnessDirectionalForm Sigma gamma w₀ v
          (primalDisplacement b betaStar) mu -
        2 * expandedPenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu -
        2 * mu * (sqNorm w₀ - sqNorm wₜ) := by
  have hL₀ := expandedPenalizedObjective_eq_directionalForm_add_common
    Sigma gamma sigmaYSq v b betaStar w₀ mu hm hgamma hw₀
  have hLₜ := expandedPenalizedObjective_eq_directionalForm_add_common
    Sigma gamma sigmaYSq v b betaStar wₜ mu hm hgamma hwₜ
  exact penalized_comparator_identity
    (expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar w₀ mu)
    (expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar wₜ mu)
    (penalizedFixedWitnessDirectionalForm Sigma gamma w₀ v
      (primalDisplacement b betaStar) mu)
    (penalizedFixedWitnessDirectionalForm Sigma gamma wₜ v
      (primalDisplacement b betaStar) mu)
    (expandedCommonTerm m gamma sigmaYSq v b betaStar)
    mu (sqNorm w₀) (sqNorm wₜ)
    (expandedPenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu)
    hL₀ hLₜ rfl

/-- Concrete finite-dimensional comparator-to-primal bound corresponding to Lemma 4.2.
The fixed-witness direction theorem is used only at `w₀`, then concrete Eq. (66) transfers
the bound to `wₜ`. -/
theorem expandedUnpenalizedComparatorToPrimal
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hw₀ : IsSimplex w₀) (hwₜ : IsSimplex wₜ)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w₀) lam) :
    fixedWitnessDirectionalForm Sigma gamma wₜ v (primalDisplacement b betaStar) ≥
      lam * sqNorm (primalDisplacement b betaStar) -
        fixedWitnessIdentificationError m gamma lam v -
        2 * expandedUnpenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ := by
  have hbase := fixedWitness_direction_identificationError
    Sigma gamma lam w₀ v (primalDisplacement b betaStar)
    hm hgamma hlam hw₀ hSigma hcurvature
  have hcompare := expandedUnpenalizedComparatorIdentity
    Sigma gamma sigmaYSq v b betaStar w₀ wₜ hm hgamma hw₀ hwₜ
  exact unpenalized_comparator_to_primal
    (fixedWitnessDirectionalForm Sigma gamma w₀ v (primalDisplacement b betaStar))
    (fixedWitnessDirectionalForm Sigma gamma wₜ v (primalDisplacement b betaStar))
    lam (sqNorm (primalDisplacement b betaStar))
    (fixedWitnessIdentificationError m gamma lam v)
    (expandedUnpenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ)
    hbase hcompare

/-- Concrete finite-dimensional comparator-to-primal bound corresponding to Lemma 3.3.
The `2 * mu` loss comes only from concrete Eq. (67) and the simplex squared-norm difference,
not from the fixed-witness direction theorem at `w₀`. -/
theorem expandedPenalizedComparatorToPrimal
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam mu : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hw₀ : IsSimplex w₀) (hwₜ : IsSimplex wₜ)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w₀) lam) :
    penalizedFixedWitnessDirectionalForm Sigma gamma wₜ v
        (primalDisplacement b betaStar) mu ≥
      lam * sqNorm (primalDisplacement b betaStar) -
        fixedWitnessIdentificationError m gamma lam v -
        2 * expandedPenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu -
        2 * mu := by
  have hbase := penalized_fixedWitness_direction_identificationError
    Sigma gamma lam mu w₀ v (primalDisplacement b betaStar)
    hm hgamma hlam hw₀ hSigma hcurvature
  have hcompare := expandedPenalizedComparatorIdentity
    Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu hm hgamma hw₀ hwₜ
  have hdiff : sqNorm w₀ - sqNorm wₜ ≤ 1 :=
    simplex_sqNorm_difference_le_one hw₀ hwₜ
  exact penalized_comparator_to_primal
    (penalizedFixedWitnessDirectionalForm Sigma gamma w₀ v
      (primalDisplacement b betaStar) mu)
    (penalizedFixedWitnessDirectionalForm Sigma gamma wₜ v
      (primalDisplacement b betaStar) mu)
    lam (sqNorm (primalDisplacement b betaStar))
    (fixedWitnessIdentificationError m gamma lam v)
    (expandedPenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu)
    mu (sqNorm w₀) (sqNorm wₜ) hbase hcompare hmu hdiff

end NegDRO
