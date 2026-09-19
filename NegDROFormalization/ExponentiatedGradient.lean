import NegDROFormalization.EntropyGeometry

/-!
# Explicit finite-dimensional exponentiated-gradient ascent

This module defines the normalized exponentiated-gradient ascent update with exponent
`+eta * g i`, proves that it preserves the strictly positive simplex, and derives its exact
logarithmic, entropy-optimality, and Bregman one-step identities.

No norm inequality, Pinsker inequality, final quadratic mirror bound, probability, or
stochastic-oracle statement is used here. The simplex comparator may have zero coordinates.
-/

set_option autoImplicit false

namespace NegDRO

/-- A project-local predicate asserting strict positivity of every coordinate. -/
def HasStrictlyPositiveCoordinates {m : ℕ} (w : Fin m → ℝ) : Prop :=
  ∀ i, 0 < w i

/-- The positive normalizer for the exponentiated-gradient ascent update. -/
noncomputable def egNormalizer
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ) : ℝ :=
  ∑ i, w i * Real.exp (eta * g i)

/-- The explicit exponentiated-gradient ascent update. The exponent has the ascent sign
`+eta * g i`. -/
noncomputable def egUpdate
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ) : Fin m → ℝ :=
  fun i => w i * Real.exp (eta * g i) / egNormalizer w g eta

/-- The EG normalizer is strictly positive when the dimension and all current coordinates are
strictly positive. No sign assumption on `eta` or `g` is needed. -/
theorem egNormalizer_pos
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hwpos : HasStrictlyPositiveCoordinates w) :
    0 < egNormalizer w g eta := by
  rw [egNormalizer]
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hwpos i) (Real.exp_pos _)
  · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- Every coordinate of the EG update is strictly positive. -/
theorem egUpdate_pos
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hwpos : HasStrictlyPositiveCoordinates w) :
    HasStrictlyPositiveCoordinates (egUpdate w g eta) := by
  intro i
  rw [egUpdate]
  exact div_pos (mul_pos (hwpos i) (Real.exp_pos _))
    (egNormalizer_pos w g eta hm hwpos)

/-- The normalized EG update preserves simplex membership. Normalization is proved from its
finite-sum definition rather than assumed. -/
theorem egUpdate_isSimplex
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (_hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w) :
    IsSimplex (egUpdate w g eta) := by
  have hZ := egNormalizer_pos w g eta hm hwpos
  constructor
  · intro i
    exact (egUpdate_pos w g eta hm hwpos i).le
  · simp only [egUpdate]
    rw [← Finset.sum_div]
    rw [show (∑ i, w i * Real.exp (eta * g i)) = egNormalizer w g eta from rfl]
    exact div_self (ne_of_gt hZ)

/-- The uniform initialization is a strictly positive simplex vector. -/
theorem uniformWeight_isPositiveSimplex
    (m : ℕ) (hm : 0 < m) :
    IsSimplex (uniformWeight m) ∧
      HasStrictlyPositiveCoordinates (uniformWeight m) := by
  exact ⟨uniformWeight_isSimplex m hm, fun i => uniformWeight_pos m hm i⟩

/-- One EG step maps a strictly positive simplex vector to another strictly positive simplex
vector, providing the preservation step needed for a future trajectory induction. -/
theorem egUpdate_isPositiveSimplex
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w) :
    IsSimplex (egUpdate w g eta) ∧
      HasStrictlyPositiveCoordinates (egUpdate w g eta) := by
  exact ⟨egUpdate_isSimplex w g eta hm hw hwpos, egUpdate_pos w g eta hm hwpos⟩

/-- Exact logarithmic coordinate update. Every logarithm rule is justified by strict
positivity of the current coordinate, exponential factor, and normalizer. -/
theorem log_egUpdate_sub_log
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ) (i : Fin m)
    (hm : 0 < m) (hwpos : HasStrictlyPositiveCoordinates w) :
    Real.log (egUpdate w g eta i) - Real.log (w i) =
      eta * g i - Real.log (egNormalizer w g eta) := by
  have hwi : w i ≠ 0 := ne_of_gt (hwpos i)
  have hexp : Real.exp (eta * g i) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hZ : egNormalizer w g eta ≠ 0 :=
    ne_of_gt (egNormalizer_pos w g eta hm hwpos)
  rw [egUpdate, Real.log_div (mul_ne_zero hwi hexp) hZ,
    Real.log_mul hwi hexp, Real.log_exp]
  ring

/-- Coordinate entropy-gradient difference induced by the exact logarithmic update. -/
theorem entropyGradient_egUpdate_sub
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ) (i : Fin m)
    (hm : 0 < m) (hwpos : HasStrictlyPositiveCoordinates w) :
    entropyGradient (egUpdate w g eta) i - entropyGradient w i =
      eta * g i - Real.log (egNormalizer w g eta) := by
  simpa [entropyGradient] using log_egUpdate_sub_log w g eta i hm hwpos

/-- A constant vector pairs to zero with the displacement between two simplex vectors. No
strict positivity is required for either vector. -/
theorem constant_vectorDot_simplex_displacement
    {m : ℕ} (u w : Fin m → ℝ) (c : ℝ)
    (hu : IsSimplex u) (hw : IsSimplex w) :
    vectorDot (fun _ => c) (primalDisplacement u w) = 0 := by
  simp only [vectorDot, primalDisplacement]
  calc
    (∑ i, c * (u i - w i)) = c * ∑ i, (u i - w i) := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [Finset.sum_sub_distrib, hu.2, hw.2]
      ring

/-- Exact EG entropy optimality identity. The constant `-log Z` from the coordinate update
cancels when paired with the displacement between the simplex comparator and updated weight. -/
theorem eg_entropy_optimality
    {m : ℕ} (u w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w) :
    eta * vectorDot g (primalDisplacement u (egUpdate w g eta)) =
      vectorDot
        (primalDisplacement (entropyGradient (egUpdate w g eta)) (entropyGradient w))
        (primalDisplacement u (egUpdate w g eta)) := by
  have hwplus := egUpdate_isSimplex w g eta hm hw hwpos
  have hconstant := constant_vectorDot_simplex_displacement
    u (egUpdate w g eta) (-Real.log (egNormalizer w g eta)) hu hwplus
  have hgradient :
      primalDisplacement (entropyGradient (egUpdate w g eta)) (entropyGradient w) =
        fun i => eta * g i - Real.log (egNormalizer w g eta) := by
    funext i
    exact entropyGradient_egUpdate_sub w g eta i hm hwpos
  rw [hgradient]
  simp only [vectorDot, primalDisplacement] at hconstant ⊢
  calc
    eta * ∑ i, g i * (u i - egUpdate w g eta i) =
        ∑ i, eta * (g i * (u i - egUpdate w g eta i)) := by
      rw [Finset.mul_sum]
    _ = (∑ i, (eta * g i - Real.log (egNormalizer w g eta)) *
          (u i - egUpdate w g eta i)) -
        ∑ i, (-Real.log (egNormalizer w g eta)) *
          (u i - egUpdate w g eta i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, (eta * g i - Real.log (egNormalizer w g eta)) *
          (u i - egUpdate w g eta i) := by
      rw [hconstant, sub_zero]

/-- Exact Bregman one-step identity, with orientation
`D(u,w) - D(u,wPlus) - D(wPlus,w)`. -/
theorem eg_bregman_one_step
    {m : ℕ} (u w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w) :
    eta * vectorDot g (primalDisplacement u (egUpdate w g eta)) =
      entropyBregman u w - entropyBregman u (egUpdate w g eta) -
        entropyBregman (egUpdate w g eta) w := by
  calc
    eta * vectorDot g (primalDisplacement u (egUpdate w g eta)) =
        vectorDot
          (primalDisplacement (entropyGradient (egUpdate w g eta)) (entropyGradient w))
          (primalDisplacement u (egUpdate w g eta)) :=
      eg_entropy_optimality u w g eta hm hu hw hwpos
    _ = entropyBregman u w - entropyBregman u (egUpdate w g eta) -
        entropyBregman (egUpdate w g eta) w :=
      entropyBregman_three_point u (egUpdate w g eta) w

/-- Exact decomposition around the current iterate. This is the equality immediately before
the future Pinsker/Hölder estimate; no inequality has been substituted. -/
theorem eg_bregman_decomposition_current
    {m : ℕ} (u w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w) :
    eta * vectorDot g (primalDisplacement u w) =
      entropyBregman u w - entropyBregman u (egUpdate w g eta) -
        entropyBregman (egUpdate w g eta) w +
        eta * vectorDot g (primalDisplacement (egUpdate w g eta) w) := by
  have hdot :
      vectorDot g (primalDisplacement u w) =
        vectorDot g (primalDisplacement u (egUpdate w g eta)) +
          vectorDot g (primalDisplacement (egUpdate w g eta) w) := by
    simp only [vectorDot, primalDisplacement]
    calc
      (∑ i, g i * (u i - w i)) =
          ∑ i, (g i * (u i - egUpdate w g eta i) +
            g i * (egUpdate w g eta i - w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, g i * (u i - egUpdate w g eta i)) +
          ∑ i, g i * (egUpdate w g eta i - w i) := by
        rw [Finset.sum_add_distrib]
  rw [hdot, mul_add, eg_bregman_one_step u w g eta hm hu hw hwpos]

end NegDRO
