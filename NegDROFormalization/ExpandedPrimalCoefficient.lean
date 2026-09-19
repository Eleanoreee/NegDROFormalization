import NegDROFormalization.ConcreteComparator
import NegDROFormalization.FixedWitness
import NegDROFormalization.PopulationExpansion

/-!
# Expanded primal coefficient and radial-derivative bridge

This deterministic module defines the finite-coordinate primal coefficient used by the
stochastic primal recursion and identifies its pairing with the existing fixed-witness
directional form. It proves only the radial derivative in direction `b - betaStar`.

For second-moment matrices, symmetry is mathematically available. A future symmetry bridge may
use it to establish a full Frechet-gradient interpretation. No symmetry is needed for the
pairing or radial derivative used in the present convergence argument, so this module does not
claim that the coefficient is a fully verified gradient for arbitrary nonsymmetric matrices.
-/

set_option autoImplicit false

namespace NegDRO

/-- The aggregate scalar `s(w) = sum_e (w_e - a_gamma)`. The existing
`negDROGammaCoefficient` supplies `a_gamma`; it is not duplicated here. -/
noncomputable def negDROAlpha
    {m : ℕ} (gamma : ℝ) (w : Fin m → ℝ) : ℝ :=
  ∑ e, (w e - negDROGammaCoefficient m gamma)

/-- The concrete finite-dimensional primal coefficient
`2 * s(w) * v + 2 * Q(w) * (b - betaStar)`. The constant `sigmaYSq` does not occur because it
is independent of `b`. -/
noncomputable def expandedPrimalCoefficient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) : Fin p → ℝ :=
  fun i =>
    2 * negDROAlpha gamma w * v i +
      2 * Matrix.mulVec (negDROQ Sigma gamma w) (primalDisplacement b betaStar) i

/-- The weight penalty `-mu * sqNorm w` is independent of `b`, so the penalized primal
coefficient is the same finite vector. Its connection to the actual penalized radial derivative
is proved below, rather than justified only by this definitional alias. -/
noncomputable def expandedPenalizedPrimalCoefficient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (_mu : ℝ) : Fin p → ℝ :=
  expandedPrimalCoefficient Sigma gamma v b betaStar w

/-- Algebraic expansion of the concrete coefficient pairing. The second term reverses the
real scalar factors coordinatewise to match `matrixQuad`; no matrix symmetry is used. -/
theorem expandedPrimalCoefficient_pairing_expansion
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) :
    vectorDot (expandedPrimalCoefficient Sigma gamma v b betaStar w)
        (primalDisplacement b betaStar) =
      2 * negDROAlpha gamma w * vectorDot v (primalDisplacement b betaStar) +
        2 * matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar) := by
  simp only [expandedPrimalCoefficient, vectorDot, matrixQuad]
  calc
    ∑ i, (2 * negDROAlpha gamma w * v i +
          2 * Matrix.mulVec (negDROQ Sigma gamma w)
            (primalDisplacement b betaStar) i) * primalDisplacement b betaStar i =
        ∑ i, (2 * negDROAlpha gamma w *
            (v i * primalDisplacement b betaStar i) +
          2 * (primalDisplacement b betaStar i *
            Matrix.mulVec (negDROQ Sigma gamma w)
              (primalDisplacement b betaStar) i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, 2 * negDROAlpha gamma w *
          (v i * primalDisplacement b betaStar i)) +
        ∑ i, 2 * (primalDisplacement b betaStar i *
          Matrix.mulVec (negDROQ Sigma gamma w)
            (primalDisplacement b betaStar) i) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * negDROAlpha gamma w *
          (∑ i, v i * primalDisplacement b betaStar i) +
        2 * (∑ i, primalDisplacement b betaStar i *
          Matrix.mulVec (negDROQ Sigma gamma w)
            (primalDisplacement b betaStar) i) := by
      rw [Finset.mul_sum, Finset.mul_sum]

/-- The concrete coefficient pairing is exactly the fixed-witness/current-weight directional
form, without simplex, sign, curvature, or symmetry assumptions. -/
theorem expandedPrimalCoefficient_pairing_eq_fixedWitnessDirectionalForm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) :
    vectorDot (expandedPrimalCoefficient Sigma gamma v b betaStar w)
        (primalDisplacement b betaStar) =
      fixedWitnessDirectionalForm Sigma gamma w v (primalDisplacement b betaStar) := by
  rw [expandedPrimalCoefficient_pairing_expansion]
  simp only [negDROAlpha, fixedWitnessDirectionalForm]

/-- Penalized coefficient pairing identified with the existing penalized directional form. -/
theorem expandedPenalizedPrimalCoefficient_pairing_eq_directionalForm
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) (mu : ℝ) :
    vectorDot (expandedPenalizedPrimalCoefficient Sigma gamma v b betaStar w mu)
        (primalDisplacement b betaStar) =
      penalizedFixedWitnessDirectionalForm Sigma gamma w v
        (primalDisplacement b betaStar) mu := by
  rw [expandedPenalizedPrimalCoefficient, penalizedFixedWitnessDirectionalForm_eq]
  exact expandedPrimalCoefficient_pairing_eq_fixedWitnessDirectionalForm
    Sigma gamma v b betaStar w

/-- The actual expanded objective along the radial path has derivative at `t = 1` equal to the
concrete coefficient pairing. This is a one-dimensional `HasDerivAt` statement, not a full
Frechet-gradient theorem. -/
theorem hasDerivAt_expandedRadialObjective_primalCoefficient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    HasDerivAt
      (expandedRadialObjective Sigma gamma sigmaYSq v b betaStar w)
      (vectorDot (expandedPrimalCoefficient Sigma gamma v b betaStar w)
        (primalDisplacement b betaStar)) 1 := by
  rw [expandedPrimalCoefficient_pairing_eq_fixedWitnessDirectionalForm]
  exact hasDerivAt_expandedRadialObjective
    Sigma gamma sigmaYSq v b betaStar w hm hgamma hw

/-- The actual penalized objective has the same primal radial derivative. The weight-only
penalty is constant along the primal radial path and therefore contributes derivative zero. -/
theorem hasDerivAt_expandedPenalizedRadialObjective_primalCoefficient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) (mu : ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    HasDerivAt
      (expandedPenalizedRadialObjective Sigma gamma sigmaYSq v b betaStar w mu)
      (vectorDot (expandedPenalizedPrimalCoefficient Sigma gamma v b betaStar w mu)
        (primalDisplacement b betaStar)) 1 := by
  rw [expandedPenalizedPrimalCoefficient_pairing_eq_directionalForm]
  exact hasDerivAt_expandedPenalizedRadialObjective
    Sigma gamma sigmaYSq v b betaStar w mu hm hgamma hw

/-- Concrete unpenalized current-weight coefficient lower bound. Curvature is assumed only at
the witness `w0`; the signed regret is comparator minus current objective. -/
theorem expandedPrimalCoefficient_unpenalized_lower_bound
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam : ℝ) (v b betaStar : Fin p → ℝ)
    (w0 w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hlam : 0 < lam)
    (hw0 : IsSimplex w0) (hw : IsSimplex w)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam) :
    vectorDot (expandedPrimalCoefficient Sigma gamma v b betaStar w)
        (primalDisplacement b betaStar) ≥
      lam * sqNorm (primalDisplacement b betaStar) -
        sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2) -
        2 * expandedUnpenalizedRegret
          Sigma gamma sigmaYSq v b betaStar w0 w := by
  rw [expandedPrimalCoefficient_pairing_eq_fixedWitnessDirectionalForm]
  simpa only [fixedWitnessIdentificationError] using
    expandedUnpenalizedComparatorToPrimal
      Sigma gamma sigmaYSq lam v b betaStar w0 w
      hm hgamma hlam hw0 hw hSigma hcurvature

/-- Concrete penalized current-weight coefficient lower bound. The only new penalized loss is
exactly `-2 * mu`, inherited from the existing comparator reduction. -/
theorem expandedPrimalCoefficient_penalized_lower_bound
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq lam mu : ℝ) (v b betaStar : Fin p → ℝ)
    (w0 w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hw0 : IsSimplex w0) (hw : IsSimplex w)
    (hSigma : ∀ e, QuadNonneg (Sigma e))
    (hcurvature : CurvatureAtLeast (negDROHeterogeneityMatrix Sigma w0) lam) :
    vectorDot (expandedPenalizedPrimalCoefficient Sigma gamma v b betaStar w mu)
        (primalDisplacement b betaStar) ≥
      lam * sqNorm (primalDisplacement b betaStar) -
        sqNorm v / (lam * (1 + gamma * (m : ℝ)) ^ 2) -
        2 * expandedPenalizedRegret
          Sigma gamma sigmaYSq v b betaStar w0 w mu -
        2 * mu := by
  rw [expandedPenalizedPrimalCoefficient_pairing_eq_directionalForm]
  simpa only [fixedWitnessIdentificationError] using
    expandedPenalizedComparatorToPrimal
      Sigma gamma sigmaYSq lam mu v b betaStar w0 w
      hm hgamma hlam hmu hw0 hw hSigma hcurvature

end NegDRO
