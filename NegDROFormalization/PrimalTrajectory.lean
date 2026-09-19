import NegDROFormalization.PrimalProjectionRecursion

/-!
# Deterministic projected-primal trajectory

This module constructs the concrete zero-indexed projected-gradient trajectory, proves its
feasibility and exact realized-gradient distance recursion, and supplies coordinate squared-norm
bounds from an abstract bounded feasible domain. Projection distance decrease and projection
feasibility are abstract interfaces in this reusable module; `EuclideanProjectionBridge.lean`
constructs the nearest-point projection that discharges them in the final wrappers.

Lean round `t` relates `b_t` and `b_(t+1)`. No probability, expectation, unbiasedness, or moment
bound is formalized here.
-/

set_option autoImplicit false

namespace NegDRO

/-- Abstract feasibility interface for a projection-like map: every output lies in `C`. This is
logically separate from `HasProjectionDistanceBound` and does not assert that `P` is a nearest-
point projection onto a closed convex set. -/
def MapsIntoFeasibleSet
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ)) : Prop :=
  ∀ x, P x ∈ C

/-- The projected-primal trajectory initialized at `bInit`, with fixed step size `eta` and
realized update-vector sequence `g`. -/
def primalTrajectory
    {p : ℕ} (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ) :
    ℕ → Fin p → ℝ
  | 0 => bInit
  | t + 1 => projectedGradientStep P (primalTrajectory P bInit eta g t) eta (g t)

/-- The projected-primal trajectory starts at `bInit`. -/
@[simp] theorem primalTrajectory_zero
    {p : ℕ} (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ) :
    primalTrajectory P bInit eta g 0 = bInit := rfl

/-- Exposed zero-based trajectory recurrence: Lean round `t` relates `b_t` and `b_(t+1)`. -/
@[simp] theorem primalTrajectory_succ
    {p : ℕ} (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ) (t : ℕ) :
    primalTrajectory P bInit eta g (t + 1) =
      projectedGradientStep P (primalTrajectory P bInit eta g t) eta (g t) := rfl

/-- Feasibility of every trajectory iterate. The base case uses initial feasibility, and the
induction step uses only the separate projection-feasibility interface. -/
theorem primalTrajectory_mem
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P) (t : ℕ) :
    primalTrajectory P bInit eta g t ∈ C := by
  induction t with
  | zero => simpa using hInit
  | succ t _iht =>
      rw [primalTrajectory_succ]
      exact hPFeas _

/-- Exact trajectory squared-distance recursion with the realized quantity `sqNorm (g t)`.
No sign assumption on `eta` is needed. -/
theorem primalTrajectory_sqDist_le
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit betaStar : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ)
    (hbetaStar : betaStar ∈ C) (hPDist : HasProjectionDistanceBound C P)
    (t : ℕ) :
    sqDist (primalTrajectory P bInit eta g (t + 1)) betaStar ≤
      sqDist (primalTrajectory P bInit eta g t) betaStar -
        2 * eta * vectorDot (g t)
          (primalDisplacement (primalTrajectory P bInit eta g t) betaStar) +
        eta ^ 2 * sqNorm (g t) := by
  rw [primalTrajectory_succ]
  exact projectedGradientStep_sqDist_le C P
    (primalTrajectory P bInit eta g t) betaStar (g t) eta hbetaStar hPDist

/-- Pointwise bounded-vector specialization of the exact trajectory recursion.

This theorem requires a pathwise bound. A stochastic second-moment bound such as
`E[sqNorm (gHat t) | F_(t-1)] ≤ G_b^2` must be applied only after taking conditional
expectations in the exact recursion; it is not a pointwise hypothesis of this theorem. -/
theorem primalTrajectory_sqDist_le_of_sqNorm_le
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit betaStar : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ)
    (M : ℕ → ℝ)
    (hbetaStar : betaStar ∈ C) (hPDist : HasProjectionDistanceBound C P)
    (t : ℕ) (hgSq : sqNorm (g t) ≤ M t) :
    sqDist (primalTrajectory P bInit eta g (t + 1)) betaStar ≤
      sqDist (primalTrajectory P bInit eta g t) betaStar -
        2 * eta * vectorDot (g t)
          (primalDisplacement (primalTrajectory P bInit eta g t) betaStar) +
        eta ^ 2 * M t := by
  rw [primalTrajectory_succ]
  exact projectedGradientStep_sqDist_le_of_sqNorm_le C P
    (primalTrajectory P bInit eta g t) betaStar (g t) eta (M t)
    hbetaStar hPDist hgSq

/-- Scalar squared-distance sequence associated with the concrete primal trajectory. -/
def primalTrajectoryDistSq
    {p : ℕ} (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ)
    (betaStar : Fin p → ℝ) (t : ℕ) : ℝ :=
  sqDist (primalTrajectory P bInit eta g t) betaStar

/-- Scalar realized gradient-direction sequence associated with the concrete trajectory. -/
def primalTrajectoryDirection
    {p : ℕ} (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ)
    (betaStar : Fin p → ℝ) (t : ℕ) : ℝ :=
  vectorDot (g t)
    (primalDisplacement (primalTrajectory P bInit eta g t) betaStar)

/-- Scalar realized squared-gradient sequence; no expectation is present. -/
def primalTrajectoryGradSq
    {p : ℕ} (g : ℕ → Fin p → ℝ) (t : ℕ) : ℝ :=
  sqNorm (g t)

/-- Exact scalar recurrence `D_(t+1) ≤ D_t - 2 eta F_t + eta^2 M_t`, transparently
matching the recursion shape used in `RegretToConvergence.lean`, but still pathwise and with
the realized `M_t = sqNorm (g t)`. -/
theorem primalTrajectory_scalarRecursion
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit betaStar : Fin p → ℝ) (eta : ℝ) (g : ℕ → Fin p → ℝ)
    (hbetaStar : betaStar ∈ C) (hPDist : HasProjectionDistanceBound C P)
    (t : ℕ) :
    primalTrajectoryDistSq P bInit eta g betaStar (t + 1) ≤
      primalTrajectoryDistSq P bInit eta g betaStar t -
        2 * eta * primalTrajectoryDirection P bInit eta g betaStar t +
        eta ^ 2 * primalTrajectoryGradSq g t := by
  exact primalTrajectory_sqDist_le C P bInit betaStar eta g hbetaStar hPDist t

/-- Exact `hrec` interface accepted by `scalar_proposition_A2` after supplying a genuinely
pointwise uniform squared-gradient bound. This remains deterministic and is not a conditional
second-moment argument. -/
theorem primalTrajectory_scalarRecursion_for_regretToConvergence
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit betaStar : Fin p → ℝ) (eta gradSqBound : ℝ)
    (g : ℕ → Fin p → ℝ) (T : ℕ)
    (hbetaStar : betaStar ∈ C) (hPDist : HasProjectionDistanceBound C P)
    (hgSq : ∀ t < T, sqNorm (g t) ≤ gradSqBound) :
    ∀ t < T,
      primalTrajectoryDistSq P bInit eta g betaStar (t + 1) ≤
        primalTrajectoryDistSq P bInit eta g betaStar t -
          2 * eta * primalTrajectoryDirection P bInit eta g betaStar t +
          eta ^ 2 * gradSqBound := by
  intro t ht
  exact primalTrajectory_sqDist_le_of_sqNorm_le C P bInit betaStar eta g
    (fun _ => gradSqBound) hbetaStar hPDist t (hgSq t ht)

/-- The feasible set is contained in the explicit coordinate squared ball of radius `B`.
No default function norm occurs in this interface. -/
def SetContainedInCoordinateSqBall
    {p : ℕ} (C : Set (Fin p → ℝ)) (B : ℝ) : Prop :=
  ∀ b ∈ C, sqNorm b ≤ B ^ 2

/-- A feasible trajectory inherits the coordinate squared-norm bound from its domain. -/
theorem primalTrajectory_sqNorm_le
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit : Fin p → ℝ) (eta B : ℝ) (g : ℕ → Fin p → ℝ)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (hCBall : SetContainedInCoordinateSqBall C B) (t : ℕ) :
    sqNorm (primalTrajectory P bInit eta g t) ≤ B ^ 2 := by
  exact hCBall _ (primalTrajectory_mem C P bInit eta g hInit hPFeas t)

/-- Coordinate squared-distance inequality, proved by summing
`(x_i - y_i)^2 ≤ 2 x_i^2 + 2 y_i^2`. -/
theorem sqDist_le_two_sqNorm_add
    {p : ℕ} (x y : Fin p → ℝ) :
    sqDist x y ≤ 2 * sqNorm x + 2 * sqNorm y := by
  simp only [sqDist, sqNorm]
  calc
    (∑ i, (x i - y i) ^ 2) ≤
        ∑ i, (2 * (x i) ^ 2 + 2 * (y i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg (x i + y i)]
    _ = 2 * (∑ i, (x i) ^ 2) + 2 * (∑ i, (y i) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Two feasible points in a radius-`B` coordinate squared ball are at squared distance at
most `4 * B^2`. -/
theorem sqDist_le_four_mul_sq_of_mem
    {p : ℕ} (C : Set (Fin p → ℝ)) (B : ℝ) (x y : Fin p → ℝ)
    (hCBall : SetContainedInCoordinateSqBall C B)
    (hx : x ∈ C) (hy : y ∈ C) :
    sqDist x y ≤ 4 * B ^ 2 := by
  have hdist := sqDist_le_two_sqNorm_add x y
  have hxNorm := hCBall x hx
  have hyNorm := hCBall y hy
  linarith

/-- Trajectory form of the `4 * B^2` distance bound. Iterate feasibility is obtained from the
initial point and projection-feasibility interface rather than assumed pointwise. -/
theorem primalTrajectory_sqDist_le_four_mul_sq
    {p : ℕ} (C : Set (Fin p → ℝ))
    (P : (Fin p → ℝ) → (Fin p → ℝ))
    (bInit betaStar : Fin p → ℝ) (eta B : ℝ) (g : ℕ → Fin p → ℝ)
    (hInit : bInit ∈ C) (hPFeas : MapsIntoFeasibleSet C P)
    (hbetaStar : betaStar ∈ C)
    (hCBall : SetContainedInCoordinateSqBall C B) (t : ℕ) :
    sqDist (primalTrajectory P bInit eta g t) betaStar ≤ 4 * B ^ 2 := by
  exact sqDist_le_four_mul_sq_of_mem C B
    (primalTrajectory P bInit eta g t) betaStar hCBall
    (primalTrajectory_mem C P bInit eta g hInit hPFeas t) hbetaStar

end NegDRO
