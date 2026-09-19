import Mathlib

/-!
# Finite-dimensional simplex norm bounds for NegDRO

This file realizes the squared-norm placeholders used in Appendix Eq. (67) and in
`Comparator.lean`. Vectors are functions `Fin m → ℝ`; no matrix or inner-product-space
structure is used.

Here `sqNorm w = ∑ i, (w i)²` is the squared Euclidean norm used by the PDF. On the plain
function type `Fin m → ℝ`, Mathlib's default norm is generally the supremum norm, so
`sqNorm w` must not be silently replaced by `‖w‖ ^ 2`. A future projection formalization must
either use `EuclideanSpace ℝ (Fin m)` or prove an explicit bridge to the present representation.

No hypothesis `0 < m` is needed. When `m = 0`, the normalization condition in `IsSimplex`
is impossible, since the empty sum is zero rather than one. Results quantified over a coordinate
are also vacuous in that case.
-/

set_option autoImplicit false

namespace NegDRO

/-- A finite real vector is in the probability simplex when every coordinate is nonnegative
and its coordinates sum to one. -/
def IsSimplex {m : ℕ} (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- The squared Euclidean norm of a finite real vector, written without introducing an
inner-product-space API. -/
def sqNorm {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ i, (w i) ^ 2

/-- Every coordinate of a simplex vector lies in `[0, 1]`. The upper bound is derived from
coordinatewise nonnegativity and the fact that the full coordinate sum is one. -/
theorem simplex_coordinate_bounds
    {m : ℕ} {w : Fin m → ℝ}
    (hw : IsSimplex w) (i : Fin m) :
    0 ≤ w i ∧ w i ≤ 1 := by
  constructor
  · exact hw.1 i
  · calc
      w i ≤ ∑ j, w j :=
        Finset.single_le_sum (fun j _ ↦ hw.1 j) (Finset.mem_univ i)
      _ = 1 := hw.2

/-- A simplex vector has squared norm between zero and one. For the upper bound, each
coordinate satisfies `(w i)² ≤ w i`, and these inequalities are summed before applying the
simplex normalization. This supplies the norm bounds represented by scalar placeholders in
`Comparator.lean`. -/
theorem simplex_sqNorm_bounds
    {m : ℕ} {w : Fin m → ℝ}
    (hw : IsSimplex w) :
    0 ≤ sqNorm w ∧ sqNorm w ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (w i))
  · calc
      sqNorm w = ∑ i, (w i) ^ 2 := rfl
      _ ≤ ∑ i, w i := by
        apply Finset.sum_le_sum
        intro i _
        have hi := simplex_coordinate_bounds hw i
        nlinarith
      _ = 1 := hw.2

/-- For two simplex vectors, the difference of their squared norms is at most one. This
discharges the scalar assumptions `n₀ ≤ 1` and `0 ≤ nₜ` used after Appendix Eq. (67) in
`Comparator.lean`. -/
theorem simplex_sqNorm_difference_le_one
    {m : ℕ} {w₀ wₜ : Fin m → ℝ}
    (hw₀ : IsSimplex w₀) (hwₜ : IsSimplex wₜ) :
    sqNorm w₀ - sqNorm wₜ ≤ 1 := by
  have h₀ := (simplex_sqNorm_bounds hw₀).2
  have hₜ := (simplex_sqNorm_bounds hwₜ).1
  linarith

/-- For `μ ≥ 0`, simplex membership gives the lower bound on the penalized correction in
Appendix Eq. (67). This is the vector-level discharge of
`simplex_penalty_correction_lower_bound` from `Comparator.lean`. -/
theorem simplex_sqNorm_penalty_correction_lower_bound
    {m : ℕ} {w₀ wₜ : Fin m → ℝ} (μ : ℝ)
    (hw₀ : IsSimplex w₀) (hwₜ : IsSimplex wₜ)
    (hμ : 0 ≤ μ) :
    -2 * μ * (sqNorm w₀ - sqNorm wₜ) ≥ -2 * μ := by
  have hdiff : sqNorm w₀ - sqNorm wₜ ≤ 1 :=
    simplex_sqNorm_difference_le_one hw₀ hwₜ
  have hprod : 0 ≤ μ * (1 - (sqNorm w₀ - sqNorm wₜ)) :=
    mul_nonneg hμ (sub_nonneg.mpr hdiff)
  nlinarith

end NegDRO
