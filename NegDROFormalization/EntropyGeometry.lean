import NegDROFormalization.DualObjectiveLinearization

/-!
# Finite-dimensional negative-entropy geometry

This module defines the negative-entropy Bregman divergence on finite real coordinate vectors,
proves its exact algebraic three-point identity, and establishes the uniform-simplex initial
potential bound. It does not identify this divergence with KL divergence, and it does not prove
Bregman nonnegativity, Pinsker, exponentiated-gradient optimality, or any stochastic statement.

The first argument of `entropyBregman u w` is the comparator/evaluation point and the second
is the base point. Comparator coordinates may be zero because `Real.log` is total and
`entropyScalar 0 = 0`.
-/

set_option autoImplicit false

namespace NegDRO

/-- The scalar negative-entropy summand `x * log x`. -/
noncomputable def entropyScalar (x : ℝ) : ℝ :=
  x * Real.log x

/-- Finite-dimensional negative entropy `Phi(w) = sum_i w_i * log(w_i)`. -/
noncomputable def negativeEntropy {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ i, entropyScalar (w i)

/-- The coordinate first-order coefficient `1 + log(w_i)` of negative entropy. -/
noncomputable def entropyGradient {m : ℕ} (w : Fin m → ℝ) : Fin m → ℝ :=
  fun i => 1 + Real.log (w i)

/-- Negative-entropy Bregman divergence, oriented with comparator `u` first and base point
`w` second. No nonnegativity claim is part of this definition. -/
noncomputable def entropyBregman {m : ℕ} (u w : Fin m → ℝ) : ℝ :=
  negativeEntropy u - negativeEntropy w -
    vectorDot (entropyGradient w) (primalDisplacement u w)

/-- The uniform weight vector with every coordinate equal to `1 / m`. The definition is total;
simplex membership and strict positivity require `0 < m`. -/
noncomputable def uniformWeight (m : ℕ) : Fin m → ℝ :=
  fun _ => 1 / (m : ℝ)

/-- `x * log x` evaluates to zero at the zero coordinate under Mathlib's total real logarithm. -/
theorem entropyScalar_zero :
    entropyScalar 0 = 0 := by
  simp [entropyScalar]

/-- Every vector has zero Bregman divergence from itself. This is purely algebraic. -/
theorem entropyBregman_self
    {m : ℕ} (w : Fin m → ℝ) :
    entropyBregman w w = 0 := by
  simp [entropyBregman, vectorDot, primalDisplacement]

/-- Exact negative-entropy Bregman three-point identity. It is algebraic after the gradient
coefficient is defined, so it requires no positivity or simplex assumptions. -/
theorem entropyBregman_three_point
    {m : ℕ} (z x y : Fin m → ℝ) :
    vectorDot (primalDisplacement (entropyGradient x) (entropyGradient y))
        (primalDisplacement z x) =
      entropyBregman z y - entropyBregman z x - entropyBregman x y := by
  have hvector :
      vectorDot (primalDisplacement (entropyGradient x) (entropyGradient y))
          (primalDisplacement z x) =
        -vectorDot (entropyGradient y) (primalDisplacement z y) +
          vectorDot (entropyGradient x) (primalDisplacement z x) +
          vectorDot (entropyGradient y) (primalDisplacement x y) := by
    simp only [vectorDot, primalDisplacement]
    calc
      (∑ i, (entropyGradient x i - entropyGradient y i) * (z i - x i)) =
          ∑ i, (-(entropyGradient y i * (z i - y i)) +
            entropyGradient x i * (z i - x i) +
            entropyGradient y i * (x i - y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -(∑ i, entropyGradient y i * (z i - y i)) +
          (∑ i, entropyGradient x i * (z i - x i)) +
          ∑ i, entropyGradient y i * (x i - y i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [Finset.sum_neg_distrib]
  rw [hvector]
  simp only [entropyBregman]
  ring

/-- For `m > 0`, the uniform weight vector belongs to the finite probability simplex. -/
theorem uniformWeight_isSimplex
    (m : ℕ) (hm : 0 < m) :
    IsSimplex (uniformWeight m) := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  constructor
  · intro i
    simp only [uniformWeight]
    positivity
  · simp only [uniformWeight, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Every coordinate of the uniform vector is strictly positive when `m > 0`. -/
theorem uniformWeight_pos
    (m : ℕ) (hm : 0 < m) (i : Fin m) :
    0 < uniformWeight m i := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  simp only [uniformWeight]
  positivity

/-- The scalar negative-entropy summand is nonpositive on the closed unit interval, including
the endpoint `x = 0`. -/
theorem entropyScalar_nonpos_of_mem_unitInterval
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    entropyScalar x ≤ 0 := by
  rw [entropyScalar]
  exact mul_nonpos_of_nonneg_of_nonpos hx0 (Real.log_nonpos hx0 hx1)

/-- Negative entropy is nonpositive on the simplex. Comparator coordinates are allowed to be
zero. -/
theorem negativeEntropy_nonpos_of_isSimplex
    {m : ℕ} {u : Fin m → ℝ} (hu : IsSimplex u) :
    negativeEntropy u ≤ 0 := by
  rw [negativeEntropy]
  apply Finset.sum_nonpos
  intro i _
  have hi := simplex_coordinate_bounds hu i
  exact entropyScalar_nonpos_of_mem_unitInterval (u i) hi.1 hi.2

/-- The negative entropy of the uniform weight is exactly `-log m`. -/
theorem negativeEntropy_uniformWeight
    (m : ℕ) (hm : 0 < m) :
    negativeEntropy (uniformWeight m) = -Real.log (m : ℝ) := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
  simp only [negativeEntropy, entropyScalar, uniformWeight, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [one_div, Real.log_inv]
  field_simp [hmNe]

/-- For a simplex comparator, the entropy-gradient linear term at the uniform base point
vanishes because both coordinate sums equal one. -/
theorem entropyGradient_uniformWeight_vectorDot_eq_zero
    {m : ℕ} (u : Fin m → ℝ) (hm : 0 < m) (hu : IsSimplex u) :
    vectorDot (entropyGradient (uniformWeight m))
      (primalDisplacement u (uniformWeight m)) = 0 := by
  have huniform := uniformWeight_isSimplex m hm
  have hsum : ∑ i, (u i - uniformWeight m i) = 0 := by
    rw [Finset.sum_sub_distrib, hu.2, huniform.2]
    ring
  have hsum' : ∑ i, (u i - 1 / (m : ℝ)) = 0 := by
    simpa only [uniformWeight] using hsum
  simp only [vectorDot, entropyGradient, primalDisplacement, uniformWeight]
  calc
    (∑ i, (1 + Real.log (1 / (m : ℝ))) * (u i - 1 / (m : ℝ))) =
        (1 + Real.log (1 / (m : ℝ))) * ∑ i, (u i - 1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [hsum']
      ring

/-- Exact uniform-initialization identity:
`D_Phi(u, uniformWeight m) = Phi(u) + log m`. -/
theorem entropyBregman_uniformWeight_eq
    {m : ℕ} (u : Fin m → ℝ) (hm : 0 < m) (hu : IsSimplex u) :
    entropyBregman u (uniformWeight m) =
      negativeEntropy u + Real.log (m : ℝ) := by
  rw [entropyBregman, negativeEntropy_uniformWeight m hm,
    entropyGradient_uniformWeight_vectorDot_eq_zero u hm hu]
  ring

/-- The uniform initialization satisfies the initial-potential bound required by
`DualRegretTelescoping.lean`. The future substitution is exactly
`initialPotentialBound = Real.log (m : ℝ)`. This theorem does not assert nonnegativity of
the terminal Bregman potential. -/
theorem entropyBregman_uniformWeight_le_log
    {m : ℕ} (u : Fin m → ℝ) (hm : 0 < m) (hu : IsSimplex u) :
    entropyBregman u (uniformWeight m) ≤ Real.log (m : ℝ) := by
  rw [entropyBregman_uniformWeight_eq u hm hu]
  have hPhi := negativeEntropy_nonpos_of_isSimplex hu
  linarith

end NegDRO
