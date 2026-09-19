import NegDROFormalization.PopulationExpansion
import NegDROFormalization.RegretToConvergence

/-!
# Deterministic projected-primal distance recursion

This module proves the coordinate Euclidean squared-distance recursion used before
Proposition A.2. Vectors remain functions `Fin p → ℝ`; all squared distances and gradient
bounds use the explicit finite sum `sqNorm`, never the default norm on the function type.

Projection is represented in this reusable recursion module by only the Fejer squared-distance
inequality required below. `EuclideanProjectionBridge.lean` separately constructs the actual
nearest-point projection and proves that it satisfies this interface.

Mathlib provides the Hilbert projection existence theorem
`exists_norm_eq_iInf_of_complete_convex` for nonempty complete convex subsets of a real inner
product space. The separate bridge moves to `EuclideanSpace ℝ (Fin p)`, chooses the unique
minimizing point, derives the Fejer inequality from its variational characterization, and
transports its norm back to `sqNorm`. The coordinate recursion below remains independent of that
construction.
-/

set_option autoImplicit false

namespace NegDRO

/-- Coordinate Euclidean squared distance, expressed through the existing explicit `sqNorm`. -/
def sqDist {p : ℕ} (x y : Fin p → ℝ) : ℝ :=
  sqNorm (fun i => x i - y i)

/-- The unprojected coordinate gradient step `b - eta * g`. -/
def gradientStep {p : ℕ} (b : Fin p → ℝ) (eta : ℝ) (g : Fin p → ℝ) : Fin p → ℝ :=
  fun i => b i - eta * g i

/-- The projected gradient step obtained by applying the supplied map after `gradientStep`. -/
def projectedGradientStep
    {p : ℕ} (P : (Fin p → ℝ) → (Fin p → ℝ))
    (b : Fin p → ℝ) (eta : ℝ) (g : Fin p → ℝ) : Fin p → ℝ :=
  P (gradientStep b eta g)

/-- The squared-distance/Fejer property needed from a projection map. This predicate records
only distance decrease toward feasible comparison points; it does not assert that `P` is an
actual metric projection or that `P x` belongs to `C`. -/
def HasProjectionDistanceBound
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ)) : Prop :=
  ∀ x z, z ∈ C → sqDist (P x) z ≤ sqDist x z

/-- Coordinate identity for the difference after an unprojected gradient step. -/
theorem primalDisplacement_gradientStep
    {p : ℕ} (b betaStar g : Fin p → ℝ) (eta : ℝ) :
    primalDisplacement (gradientStep b eta g) betaStar =
      fun i => primalDisplacement b betaStar i - eta * g i := by
  funext i
  simp only [primalDisplacement, gradientStep]
  ring

/-- Symmetry of the explicit finite-coordinate dot product. -/
theorem vectorDot_comm
    {p : ℕ} (x y : Fin p → ℝ) :
    vectorDot x y = vectorDot y x := by
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact coordinate expansion of squared distance after the unprojected gradient step.
The dot product is oriented as `vectorDot g (b - betaStar)`, matching the primal recursion
used in the PDF. No sign condition on `eta` is needed. -/
theorem sqDist_gradientStep
    {p : ℕ} (b betaStar g : Fin p → ℝ) (eta : ℝ) :
    sqDist (gradientStep b eta g) betaStar =
      sqDist b betaStar -
        2 * eta * vectorDot g (primalDisplacement b betaStar) +
        eta ^ 2 * sqNorm g := by
  simp only [sqDist, sqNorm, vectorDot, primalDisplacement, gradientStep]
  calc
    (∑ i, (b i - eta * g i - betaStar i) ^ 2) =
        ∑ i, ((b i - betaStar i) ^ 2 -
          2 * eta * (g i * (b i - betaStar i)) +
          eta ^ 2 * (g i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (b i - betaStar i) ^ 2) -
        2 * eta * (∑ i, g i * (b i - betaStar i)) +
        eta ^ 2 * (∑ i, (g i) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.mul_sum Finset.univ
        (fun i => g i * (b i - betaStar i)) (2 * eta)]
      rw [Finset.mul_sum Finset.univ (fun i => (g i) ^ 2) (eta ^ 2)]

/-- Deterministic projected-primal distance recursion. It follows from the Fejer
squared-distance property and the exact coordinate expansion, with no sign assumption on
`eta`. -/
theorem projectedGradientStep_sqDist_le
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (b betaStar g : Fin p → ℝ) (eta : ℝ)
    (hbetaStar : betaStar ∈ C)
    (hP : HasProjectionDistanceBound C P) :
    sqDist (projectedGradientStep P b eta g) betaStar ≤
      sqDist b betaStar -
        2 * eta * vectorDot g (primalDisplacement b betaStar) +
        eta ^ 2 * sqNorm g := by
  calc
    sqDist (projectedGradientStep P b eta g) betaStar ≤
        sqDist (gradientStep b eta g) betaStar :=
      hP (gradientStep b eta g) betaStar hbetaStar
    _ = sqDist b betaStar -
        2 * eta * vectorDot g (primalDisplacement b betaStar) +
        eta ^ 2 * sqNorm g := sqDist_gradientStep b betaStar g eta

/-- Bounded-gradient specialization of the deterministic projected recursion.
`gradSqBound` is already the squared-gradient bound `G_b^2` and is not squared again. -/
theorem projectedGradientStep_sqDist_le_of_sqNorm_le
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (b betaStar g : Fin p → ℝ) (eta gradSqBound : ℝ)
    (hbetaStar : betaStar ∈ C)
    (hP : HasProjectionDistanceBound C P)
    (hgrad : sqNorm g ≤ gradSqBound) :
    sqDist (projectedGradientStep P b eta g) betaStar ≤
      sqDist b betaStar -
        2 * eta * vectorDot g (primalDisplacement b betaStar) +
        eta ^ 2 * gradSqBound := by
  have hrec := projectedGradientStep_sqDist_le C P b betaStar g eta hbetaStar hP
  have hscale : eta ^ 2 * sqNorm g ≤ eta ^ 2 * gradSqBound :=
    mul_le_mul_of_nonneg_left hgrad (sq_nonneg eta)
  linarith

/-- Deterministic bridge to the scalar recurrence consumed by `RegretToConvergence.lean`.
Here `Dnext`, `D`, and `F` are definitionally the projected squared distance, current squared
distance, and coordinate gradient-direction dot product. This theorem does not take
expectations and does not establish stochastic-gradient unbiasedness. -/
theorem projectedGradientStep_scalarRecursion
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (b betaStar g : Fin p → ℝ) (eta gradSqBound : ℝ)
    (hbetaStar : betaStar ∈ C)
    (hP : HasProjectionDistanceBound C P)
    (hgrad : sqNorm g ≤ gradSqBound) :
    let Dnext := sqDist (projectedGradientStep P b eta g) betaStar
    let D := sqDist b betaStar
    let F := vectorDot g (primalDisplacement b betaStar)
    Dnext ≤ D - 2 * eta * F + eta ^ 2 * gradSqBound := by
  exact projectedGradientStep_sqDist_le_of_sqNorm_le
    C P b betaStar g eta gradSqBound hbetaStar hP hgrad

end NegDRO
