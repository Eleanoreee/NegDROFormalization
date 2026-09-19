import NegDROFormalization.ConcreteComparator
import NegDROFormalization.DualRegretTelescoping

/-!
# Deterministic dual-objective linearization

This module identifies the actual finite-dimensional dual first-order coefficients of the
expanded NegDRO objectives. It proves directly from finite coordinate sums that unpenalized
comparator regret equals its linearization and penalized comparator regret is at most its
linearization when `mu ≥ 0`.

No simplex, denominator, probability, stochastic-oracle, entropy, or exponentiated-gradient
interface is used. All squared norms are the explicit coordinate sum `sqNorm`.
-/

set_option autoImplicit false

namespace NegDRO

/-- The unpenalized dual coefficient vector at the fixed primal point `b`: its coordinate at
environment `e` is the actual expanded environmental risk. -/
noncomputable def expandedDualGradient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ) : Fin m → ℝ :=
  fun e => expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e)

/-- The penalized dual first-order coefficient at `w`, obtained by adding the derivative of
the coordinate penalty `-mu * sqNorm w`. -/
noncomputable def expandedPenalizedDualGradient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w : Fin m → ℝ) (mu : ℝ) : Fin m → ℝ :=
  fun e => expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e) - 2 * mu * w e

/-- Nonnegativity of the explicit finite-coordinate squared norm. -/
theorem sqNorm_nonneg
    {m : ℕ} (w : Fin m → ℝ) :
    0 ≤ sqNorm w := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (w i))

/-- Exact finite-coordinate squared-norm difference identity:
`sqNorm u - sqNorm w = 2 * vectorDot w (u - w) + sqNorm (u - w)`. -/
theorem sqNorm_sub_eq_two_vectorDot_add_sqNorm
    {m : ℕ} (u w : Fin m → ℝ) :
    sqNorm u - sqNorm w =
      2 * vectorDot w (primalDisplacement u w) + sqNorm (primalDisplacement u w) := by
  simp only [sqNorm, vectorDot, primalDisplacement]
  calc
    (∑ i, (u i) ^ 2) - ∑ i, (w i) ^ 2 =
        ∑ i, ((u i) ^ 2 - (w i) ^ 2) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ i, (2 * (w i * (u i - w i)) + (u i - w i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, 2 * (w i * (u i - w i))) + ∑ i, (u i - w i) ^ 2 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (∑ i, w i * (u i - w i)) + ∑ i, (u i - w i) ^ 2 := by
      rw [Finset.mul_sum]

/-- The penalized coefficient paired with a displacement equals the unpenalized coefficient
pairing minus the derivative contribution from the quadratic penalty. -/
theorem expandedPenalizedDualGradient_vectorDot
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (u w : Fin m → ℝ) (mu : ℝ) :
    vectorDot (expandedPenalizedDualGradient Sigma sigmaYSq v b betaStar w mu)
        (primalDisplacement u w) =
      vectorDot (expandedDualGradient Sigma sigmaYSq v b betaStar)
          (primalDisplacement u w) -
        2 * mu * vectorDot w (primalDisplacement u w) := by
  simp only [vectorDot, expandedPenalizedDualGradient, expandedDualGradient,
    primalDisplacement]
  calc
    (∑ i, (expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma i) -
        2 * mu * w i) * (u i - w i)) =
        ∑ i, (expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma i) *
          (u i - w i) - 2 * mu * (w i * (u i - w i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma i) *
          (u i - w i)) -
        ∑ i, 2 * mu * (w i * (u i - w i)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma i) *
          (u i - w i)) -
        2 * mu * ∑ i, w i * (u i - w i) := by
      rw [Finset.mul_sum]

/-- Exact unpenalized objective difference for arbitrary finite real weight vectors. The
offset `negDROGammaCoefficient` cancels directly inside the finite sum, so no simplex or
denominator assumptions are needed. -/
theorem expandedObjective_sub_eq_vectorDot_dualGradient
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (u w : Fin m → ℝ) :
    expandedObjective Sigma gamma sigmaYSq v b betaStar u -
        expandedObjective Sigma gamma sigmaYSq v b betaStar w =
      vectorDot (expandedDualGradient Sigma sigmaYSq v b betaStar)
        (primalDisplacement u w) := by
  simp only [expandedObjective, expandedDualGradient, vectorDot, primalDisplacement]
  calc
    (∑ e, (u e - negDROGammaCoefficient m gamma) *
        expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e)) -
        ∑ e, (w e - negDROGammaCoefficient m gamma) *
          expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e) =
      ∑ e, ((u e - negDROGammaCoefficient m gamma) *
          expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e) -
        (w e - negDROGammaCoefficient m gamma) *
          expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ e, expandedEnvironmentalRisk sigmaYSq v b betaStar (Sigma e) *
        (u e - w e) := by
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- Exact penalized first-order expansion. The objective difference is the coefficient
pairing minus the remainder `mu * sqNorm (u - w)`, with the displayed negative sign. -/
theorem expandedPenalizedObjective_sub_eq_linearization_sub_remainder
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (u w : Fin m → ℝ) (mu : ℝ) :
    expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar u mu -
        expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar w mu =
      vectorDot (expandedPenalizedDualGradient Sigma sigmaYSq v b betaStar w mu)
          (primalDisplacement u w) -
        mu * sqNorm (primalDisplacement u w) := by
  have hobjective := expandedObjective_sub_eq_vectorDot_dualGradient
    Sigma gamma sigmaYSq v b betaStar u w
  have hnorm := sqNorm_sub_eq_two_vectorDot_add_sqNorm u w
  have hgradient := expandedPenalizedDualGradient_vectorDot
    Sigma sigmaYSq v b betaStar u w mu
  rw [expandedPenalizedObjective]
  calc
    (expandedObjective Sigma gamma sigmaYSq v b betaStar u - mu * sqNorm u) -
        (expandedObjective Sigma gamma sigmaYSq v b betaStar w - mu * sqNorm w) =
      (expandedObjective Sigma gamma sigmaYSq v b betaStar u -
          expandedObjective Sigma gamma sigmaYSq v b betaStar w) -
        mu * (sqNorm u - sqNorm w) := by ring
    _ = vectorDot (expandedDualGradient Sigma sigmaYSq v b betaStar)
          (primalDisplacement u w) - mu * (sqNorm u - sqNorm w) := by
      rw [hobjective]
    _ = vectorDot (expandedPenalizedDualGradient Sigma sigmaYSq v b betaStar w mu)
          (primalDisplacement u w) - mu * sqNorm (primalDisplacement u w) := by
      rw [hgradient, hnorm]
      ring

/-- Concavity inequality for the expanded objective penalized by `-mu * sqNorm w`.
It holds for arbitrary finite real weight vectors and does not require either side to be
nonnegative. -/
theorem expandedPenalizedObjective_sub_le_linearization
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (u w : Fin m → ℝ) (mu : ℝ) (hmu : 0 ≤ mu) :
    expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar u mu -
        expandedPenalizedObjective Sigma gamma sigmaYSq v b betaStar w mu ≤
      vectorDot (expandedPenalizedDualGradient Sigma sigmaYSq v b betaStar w mu)
        (primalDisplacement u w) := by
  rw [expandedPenalizedObjective_sub_eq_linearization_sub_remainder
    Sigma gamma sigmaYSq v b betaStar u w mu]
  have hnonneg : 0 ≤ mu * sqNorm (primalDisplacement u w) :=
    mul_nonneg hmu (sqNorm_nonneg _)
  linarith

/-- Concrete unpenalized regret is exactly its actual dual linearization. -/
theorem expandedUnpenalizedRegret_eq_linearization
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ) :
    expandedUnpenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ =
      vectorDot (expandedDualGradient Sigma sigmaYSq v b betaStar)
        (primalDisplacement w₀ wₜ) := by
  exact expandedObjective_sub_eq_vectorDot_dualGradient
    Sigma gamma sigmaYSq v b betaStar w₀ wₜ

/-- Concrete penalized regret is at most the actual dual linearization evaluated at the
current point `wₜ`. -/
theorem expandedPenalizedRegret_le_linearization
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v b betaStar : Fin p → ℝ)
    (w₀ wₜ : Fin m → ℝ) (mu : ℝ) (hmu : 0 ≤ mu) :
    expandedPenalizedRegret Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu ≤
      vectorDot (expandedPenalizedDualGradient Sigma sigmaYSq v b betaStar wₜ mu)
        (primalDisplacement w₀ wₜ) := by
  exact expandedPenalizedObjective_sub_le_linearization
    Sigma gamma sigmaYSq v b betaStar w₀ wₜ mu hmu

/-- Unpenalized concrete wrapper for `dual_one_step_substitution`. The abstract comparison
`regret t ≤ linearizedRegret t` is discharged by exact objective linearization. -/
theorem expandedUnpenalized_dual_one_step
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq : ℝ) (v betaStar : Fin p → ℝ)
    (b : ℕ → Fin p → ℝ) (w₀ : Fin m → ℝ) (w : ℕ → Fin m → ℝ)
    (potential dualGradSq : ℕ → ℝ) (eta : ℝ) (t : ℕ)
    (hmirror : eta *
        vectorDot (expandedDualGradient Sigma sigmaYSq v (b t) betaStar)
          (primalDisplacement w₀ (w t)) ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 ≤ eta) :
    eta * expandedUnpenalizedRegret Sigma gamma sigmaYSq v (b t) betaStar w₀ (w t) ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t := by
  exact dual_one_step_substitution potential
    (fun s => vectorDot (expandedDualGradient Sigma sigmaYSq v (b s) betaStar)
      (primalDisplacement w₀ (w s)))
    (fun s => expandedUnpenalizedRegret Sigma gamma sigmaYSq v (b s) betaStar w₀ (w s))
    dualGradSq eta t
    (expandedUnpenalizedRegret_eq_linearization
      Sigma gamma sigmaYSq v (b t) betaStar w₀ (w t)).le
    hmirror heta

/-- Penalized concrete wrapper for `dual_one_step_substitution`. The abstract comparison is
discharged by penalized concavity, with the coefficient evaluated at the current `w t`. -/
theorem expandedPenalized_dual_one_step
    {m p : ℕ} (Sigma : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (gamma sigmaYSq mu : ℝ) (v betaStar : Fin p → ℝ)
    (b : ℕ → Fin p → ℝ) (w₀ : Fin m → ℝ) (w : ℕ → Fin m → ℝ)
    (potential dualGradSq : ℕ → ℝ) (eta : ℝ) (t : ℕ)
    (hmu : 0 ≤ mu)
    (hmirror : eta *
        vectorDot (expandedPenalizedDualGradient Sigma sigmaYSq v (b t) betaStar (w t) mu)
          (primalDisplacement w₀ (w t)) ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 ≤ eta) :
    eta * expandedPenalizedRegret Sigma gamma sigmaYSq v (b t) betaStar w₀ (w t) mu ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t := by
  exact dual_one_step_substitution potential
    (fun s => vectorDot
      (expandedPenalizedDualGradient Sigma sigmaYSq v (b s) betaStar (w s) mu)
      (primalDisplacement w₀ (w s)))
    (fun s => expandedPenalizedRegret Sigma gamma sigmaYSq v (b s) betaStar w₀ (w s) mu)
    dualGradSq eta t
    (expandedPenalizedRegret_le_linearization
      Sigma gamma sigmaYSq v (b t) betaStar w₀ (w t) mu hmu)
    hmirror heta

end NegDRO
