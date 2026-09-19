import NegDROFormalization.Comparator
import NegDROFormalization.FixedWitness

/-!
# Population-risk expansion bridge for NegDRO

This module takes the expanded environmental-risk identity from Appendix Lemma 1 as an explicit
algebraic input. Official v3 Eq. (13) is the minimax identification formulation, not this
quadratic expansion. This module does not construct probability spaces, expectations, or the
underlying structural causal model.

Vectors remain plain functions on `Fin`, so every Euclidean squared norm is the explicit
`sqNorm` from `Simplex.lean`, never Mathlib's default norm on a function type.
-/

set_option autoImplicit false

namespace NegDRO

/-- The primal displacement `d = b - betaStar`, defined coordinatewise. -/
def primalDisplacement {p : ℕ} (b betaStar : Fin p → ℝ) : Fin p → ℝ :=
  fun i => b i - betaStar i

/-- The finite-dimensional environmental-risk expansion used in Appendix Lemma 1:
`sigmaYSq + 2 * vectorDot v d + matrixQuad SigmaE d`, where `d = b - betaStar`.

This is a starting definition supplied by the additive-intervention model, not a derivation
of that model or of an expectation identity. The scalar `sigmaYSq` is algebraically arbitrary. -/
noncomputable def expandedEnvironmentalRisk
    {p : ℕ} (sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (SigmaE : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar) +
    matrixQuad SigmaE (primalDisplacement b betaStar)

/-- The expanded unpenalized population objective, constructed as the actual finite weighted
sum of the environmental risks rather than from its later closed form. -/
noncomputable def expandedObjective
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) : ℝ :=
  ∑ e, (w e - negDROGammaCoefficient m gamma) *
    expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e)

/-- The part of the expanded objective that depends on `b` but is common across all simplex
weights `w` evaluated at that same primal point. -/
noncomputable def expandedCommonTerm
    (m : ℕ) {p : ℕ} (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) : ℝ :=
  (sigmaYSq + vectorDot v (primalDisplacement b betaStar)) /
    (1 + gamma * (m : ℝ))

/-- Linearity of `matrixQuad` identifies the quadratic part of the environmental weighted
sum with the quadratic form of `negDROQ`. -/
theorem weighted_environment_matrixQuad
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma : ℝ) (w : Fin m → ℝ) (d : Fin p → ℝ) :
    (∑ e, (w e - negDROGammaCoefficient m gamma) * matrixQuad (Sigma e) d) =
      matrixQuad (negDROQ Sigma gamma w) d := by
  rw [negDROQ, matrixQuad_sum]
  simp only [matrixQuad_smul]

/-- The weighted-objective expansion obtained from the Appendix Lemma 1 identity. Its proof uses
the simplex coefficient identity, the definition of `negDROQ`, and linearity of `matrixQuad`
over the finite matrix sum. -/
theorem expandedObjective_eq
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    expandedObjective Sigma gamma sigmaYSq v b betaStar w =
      (sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar)) /
          (1 + gamma * (m : ℝ)) +
        matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar) := by
  have hcoeff := negDRO_coefficient_sum gamma hm hgamma hw
  have hquad := weighted_environment_matrixQuad Sigma gamma w
    (primalDisplacement b betaStar)
  rw [expandedObjective]
  simp only [expandedEnvironmentalRisk]
  calc
    (∑ e, (w e - negDROGammaCoefficient m gamma) *
        (sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar) +
          matrixQuad (Sigma e) (primalDisplacement b betaStar))) =
        (∑ e, (w e - negDROGammaCoefficient m gamma)) *
            (sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar)) +
          ∑ e, (w e - negDROGammaCoefficient m gamma) *
            matrixQuad (Sigma e) (primalDisplacement b betaStar) := by
      calc
        _ = ∑ e, ((w e - negDROGammaCoefficient m gamma) *
              (sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar)) +
            (w e - negDROGammaCoefficient m gamma) *
              matrixQuad (Sigma e) (primalDisplacement b betaStar)) := by
          apply Fintype.sum_congr
          intro e
          ring
        _ = (∑ e, (w e - negDROGammaCoefficient m gamma) *
              (sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar))) +
            ∑ e, (w e - negDROGammaCoefficient m gamma) *
              matrixQuad (Sigma e) (primalDisplacement b betaStar) := by
          exact Finset.sum_add_distrib
        _ = _ := by
          congr 1
          exact (Finset.sum_mul Finset.univ
            (fun e => w e - negDROGammaCoefficient m gamma)
            (sigmaYSq + 2 * vectorDot v (primalDisplacement b betaStar))).symm
    _ = _ := by
      rw [hcoeff, hquad]
      ring

/-- Concrete Appendix Eq. (64) for the expanded population objective. -/
theorem expandedObjective_eq_directionalForm_add_common
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    expandedObjective Sigma gamma sigmaYSq v b betaStar w =
      (1 / 2 : ℝ) * fixedWitnessDirectionalForm Sigma gamma w v
          (primalDisplacement b betaStar) +
        expandedCommonTerm m gamma sigmaYSq v b betaStar := by
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  have hden : 1 + gamma * (m : ℝ) ≠ 0 := ne_of_gt hdenPos
  have hL := expandedObjective_eq Sigma gamma sigmaYSq v b betaStar w hm hgamma hw
  have hcoeff := negDRO_coefficient_sum gamma hm hgamma hw
  have hg :
      fixedWitnessDirectionalForm Sigma gamma w v (primalDisplacement b betaStar) =
        (2 * vectorDot v (primalDisplacement b betaStar)) /
            (1 + gamma * (m : ℝ)) +
          2 * matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar) := by
    rw [fixedWitnessDirectionalForm, hcoeff]
    field_simp [hden]
  simpa only [expandedCommonTerm] using
    common_unpenalized_identity
      sigmaYSq (vectorDot v (primalDisplacement b betaStar))
      (matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar))
      (1 + gamma * (m : ℝ))
      (expandedObjective Sigma gamma sigmaYSq v b betaStar w)
      (fixedWitnessDirectionalForm Sigma gamma w v (primalDisplacement b betaStar))
      hden hL hg

/-- The actual expanded penalized population objective. The penalty is explicitly
`-mu * sqNorm w`; it is not an alias for an unpenalized closed form. -/
noncomputable def expandedPenalizedObjective
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) (mu : ℝ) : ℝ :=
  expandedObjective Sigma gamma sigmaYSq v b betaStar w - mu * sqNorm w

/-- Concrete Appendix Eq. (65) for the actual expanded penalized objective. -/
theorem expandedPenalizedObjective_eq_directionalForm_add_common
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) (mu : ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar w mu =
      (1 / 2 : ℝ) * penalizedFixedWitnessDirectionalForm Sigma gamma w v
          (primalDisplacement b betaStar) mu +
        expandedCommonTerm m gamma sigmaYSq v b betaStar - mu * sqNorm w := by
  rw [expandedPenalizedObjective]
  rw [expandedObjective_eq_directionalForm_add_common Sigma gamma sigmaYSq v b betaStar w
    hm hgamma hw]
  rw [penalizedFixedWitnessDirectionalForm_eq]

/-- The radial path `betaStar + t d`, defined coordinatewise. -/
def radialPrimalPoint {p : ℕ} (betaStar d : Fin p → ℝ) (t : ℝ) : Fin p → ℝ :=
  fun i => betaStar i + t * d i

/-- Along the radial path, displacement from `betaStar` is exactly `t d`. -/
theorem primalDisplacement_radialPrimalPoint
    {p : ℕ} (betaStar d : Fin p → ℝ) (t : ℝ) :
    primalDisplacement (radialPrimalPoint betaStar d t) betaStar = fun i => t * d i := by
  funext i
  simp [primalDisplacement, radialPrimalPoint]

/-- `vectorDot` is homogeneous in its second vector argument. -/
theorem vectorDot_scale_right
    {p : ℕ} (v d : Fin p → ℝ) (t : ℝ) :
    vectorDot v (fun i => t * d i) = t * vectorDot v d := by
  rw [vectorDot, vectorDot]
  rw [Finset.mul_sum Finset.univ (fun i => v i * d i) t]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `vectorDot` is homogeneous in its first vector argument. -/
theorem vectorDot_scale_left
    {p : ℕ} (v d : Fin p → ℝ) (t : ℝ) :
    vectorDot (fun i => t * v i) d = t * vectorDot v d := by
  rw [vectorDot, vectorDot]
  rw [Finset.mul_sum Finset.univ (fun i => v i * d i) t]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Matrix-vector multiplication is homogeneous in the vector argument. -/
theorem matrixMulVec_scale
    {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (d : Fin p → ℝ) (t : ℝ) :
    Matrix.mulVec M (fun i => t * d i) = fun i => t * Matrix.mulVec M d i := by
  funext i
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  change Finset.univ.sum (fun j => M i j * (t * d j)) =
    t * Finset.univ.sum (fun j => M i j * d j)
  rw [Finset.mul_sum Finset.univ (fun j => M i j * d j) t]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A quadratic form scales quadratically when its vector argument is scaled. No matrix
symmetry assumption is required. -/
theorem matrixQuad_scale_vector
    {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (d : Fin p → ℝ) (t : ℝ) :
    matrixQuad M (fun i => t * d i) = t ^ 2 * matrixQuad M d := by
  rw [matrixQuad, matrixMulVec_scale]
  rw [vectorDot_scale_right, vectorDot_scale_left]
  rw [matrixQuad]
  ring

/-- The expanded unpenalized objective restricted to the radial path. -/
noncomputable def expandedRadialObjective
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) (t : ℝ) : ℝ :=
  expandedObjective Sigma gamma sigmaYSq v
    (radialPrimalPoint betaStar (primalDisplacement b betaStar) t) betaStar w

/-- Closed form of the expanded objective along the radial path. -/
theorem expandedRadialObjective_eq
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) (t : ℝ) :
    expandedRadialObjective Sigma gamma sigmaYSq v b betaStar w t =
      (sigmaYSq + 2 * t * vectorDot v (primalDisplacement b betaStar)) /
          (1 + gamma * (m : ℝ)) +
        t ^ 2 * matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar) := by
  rw [expandedRadialObjective]
  rw [expandedObjective_eq Sigma gamma sigmaYSq v
    (radialPrimalPoint betaStar (primalDisplacement b betaStar) t)
    betaStar w hm hgamma hw]
  rw [primalDisplacement_radialPrimalPoint]
  rw [vectorDot_scale_right, matrixQuad_scale_vector]
  ring

/-- The fixed-witness directional form is the one-dimensional radial derivative at `t = 1`
of the actual expanded objective. This is not a full Frechet-gradient statement. -/
theorem hasDerivAt_expandedRadialObjective
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    HasDerivAt
      (expandedRadialObjective Sigma gamma sigmaYSq v b betaStar w)
      (fixedWitnessDirectionalForm Sigma gamma w v (primalDisplacement b betaStar)) 1 := by
  have hdenPos := negDRO_denominator_pos gamma hm hgamma
  have hden : 1 + gamma * (m : ℝ) ≠ 0 := ne_of_gt hdenPos
  have hcoeff := negDRO_coefficient_sum gamma hm hgamma hw
  have hfun :
      expandedRadialObjective Sigma gamma sigmaYSq v b betaStar w =
        fun t => (sigmaYSq + (2 * vectorDot v (primalDisplacement b betaStar)) * t) /
            (1 + gamma * (m : ℝ)) +
          t ^ 2 * matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar) := by
    funext t
    rw [expandedRadialObjective_eq Sigma gamma sigmaYSq v b betaStar w hm hgamma hw t]
    ring
  rw [hfun]
  have hpoly :
      HasDerivAt
        (fun t : ℝ =>
          (sigmaYSq + (2 * vectorDot v (primalDisplacement b betaStar)) * t) /
            (1 + gamma * (m : ℝ)) +
          t ^ 2 * matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar))
        ((2 * vectorDot v (primalDisplacement b betaStar)) /
            (1 + gamma * (m : ℝ)) +
          2 * matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar)) 1 := by
    have hlinear :=
      ((hasDerivAt_const (x := (1 : ℝ)) sigmaYSq).add
        ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).const_mul
          (2 * vectorDot v (primalDisplacement b betaStar)))).div_const
            (1 + gamma * (m : ℝ))
    have hquadratic :=
      ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).pow 2).mul_const
        (matrixQuad (negDROQ Sigma gamma w) (primalDisplacement b betaStar))
    convert! hlinear.add hquadratic using 1
    all_goals norm_num
  convert hpoly using 1
  rw [fixedWitnessDirectionalForm, hcoeff]
  field_simp [hden]

/-- The expanded penalized objective restricted to the same radial path, with `w` fixed. -/
noncomputable def expandedPenalizedRadialObjective
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ)
    (mu t : ℝ) : ℝ :=
  expandedPenalizedObjective Sigma gamma sigmaYSq v
    (radialPrimalPoint betaStar (primalDisplacement b betaStar) t) betaStar w mu

/-- The weight-only penalty is constant on the radial path, so the radial derivative of the
actual penalized objective is the same fixed-witness directional form. -/
theorem hasDerivAt_expandedPenalizedRadialObjective
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) (w : Fin m → ℝ) (mu : ℝ)
    (hm : 0 < m) (hgamma : 0 ≤ gamma) (hw : IsSimplex w) :
    HasDerivAt
      (expandedPenalizedRadialObjective Sigma gamma sigmaYSq v b betaStar w mu)
      (penalizedFixedWitnessDirectionalForm Sigma gamma w v
        (primalDisplacement b betaStar) mu) 1 := by
  have hunpen := hasDerivAt_expandedRadialObjective Sigma gamma sigmaYSq v b betaStar w
    hm hgamma hw
  rw [penalizedFixedWitnessDirectionalForm_eq]
  change HasDerivAt
    (fun t => expandedObjective Sigma gamma sigmaYSq v
      (radialPrimalPoint betaStar (primalDisplacement b betaStar) t) betaStar w -
        mu * sqNorm w)
    (fixedWitnessDirectionalForm Sigma gamma w v (primalDisplacement b betaStar)) 1
  exact hunpen.sub_const (mu * sqNorm w)

end NegDRO
