import NegDROFormalization.ExponentiatedGradient
import NegDROFormalization.DualRegretTelescoping

/-!
# Finite-coordinate mirror remainder bound

This module proves the finite-dimensional infinity--one-norm estimate and scalar quadratic
inequality needed to bound the exact exponentiated-gradient remainder. The final mirror bound
keeps precisely one local finite-Pinsker instance as a hypothesis; Pinsker itself is not proved
here. No default norm on function spaces is used.
-/

set_option autoImplicit false

namespace NegDRO

/-- Explicit finite-coordinate one-norm quantity `sum_i |x_i|`. This is not the default
function-space norm. -/
def l1Size {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∑ i, |x i|

/-- Explicit finite-coordinate one-norm distance, defined from the project displacement. -/
def l1Dist {m : ℕ} (x y : Fin m → ℝ) : ℝ :=
  l1Size (primalDisplacement x y)

/-- `G` bounds every coordinate absolute value of `g`. This predicate is not claimed to be
definitionally equal to Mathlib's function norm. -/
def HasCoordinateAbsBound {m : ℕ} (g : Fin m → ℝ) (G : ℝ) : Prop :=
  ∀ i, |g i| ≤ G

/-- The explicit finite-coordinate one-norm quantity is nonnegative. -/
theorem l1Size_nonneg
    {m : ℕ} (x : Fin m → ℝ) :
    0 ≤ l1Size x := by
  rw [l1Size]
  exact Finset.sum_nonneg (fun i _ => abs_nonneg (x i))

/-- The explicit finite-coordinate one-norm distance is nonnegative. -/
theorem l1Dist_nonneg
    {m : ℕ} (x y : Fin m → ℝ) :
    0 ≤ l1Dist x y := by
  exact l1Size_nonneg (primalDisplacement x y)

/-- Finite-dimensional infinity--one-norm Hölder inequality, proved by bounding the
absolute value of each coordinate product and summing. -/
theorem abs_vectorDot_le_coordinateBound_mul_l1Size
    {m : ℕ} (g x : Fin m → ℝ) (G : ℝ)
    (_hG : 0 ≤ G) (hg : HasCoordinateAbsBound g G) :
    |vectorDot g x| ≤ G * l1Size x := by
  calc
    |vectorDot g x| = |∑ i, g i * x i| := rfl
    _ ≤ ∑ i, |g i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, G * |x i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hg i) (abs_nonneg (x i))
    _ = G * l1Size x := by
      rw [l1Size, Finset.mul_sum]

/-- One-sided finite-dimensional infinity--one-norm Hölder inequality. -/
theorem vectorDot_le_coordinateBound_mul_l1Size
    {m : ℕ} (g x : Fin m → ℝ) (G : ℝ)
    (hG : 0 ≤ G) (hg : HasCoordinateAbsBound g G) :
    vectorDot g x ≤ G * l1Size x := by
  exact (le_abs_self (vectorDot g x)).trans
    (abs_vectorDot_le_coordinateBound_mul_l1Size g x G hG hg)

/-- Hölder specialized to the EG displacement. It uses no simplex or positivity geometry. -/
theorem egUpdate_displacement_vectorDot_le
    {m : ℕ} (w g : Fin m → ℝ) (eta G : ℝ)
    (hG : 0 ≤ G) (hg : HasCoordinateAbsBound g G) :
    vectorDot g (primalDisplacement (egUpdate w g eta) w) ≤
      G * l1Dist (egUpdate w g eta) w := by
  exact vectorDot_le_coordinateBound_mul_l1Size
    g (primalDisplacement (egUpdate w g eta) w) G hG hg

/-- Scalar completing-the-square inequality, derived from `0 ≤ (a - b)^2`. -/
theorem completingSquare_half
    (a b : ℝ) :
    -a ^ 2 / 2 + b * a ≤ b ^ 2 / 2 := by
  have hsquare : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  nlinarith

/-- The completing-the-square inequality with `b = eta * G`; no sign assumptions are
needed. -/
theorem completingSquare_eta_mul
    (a eta G : ℝ) :
    -a ^ 2 / 2 + eta * G * a ≤ eta ^ 2 * G ^ 2 / 2 := by
  have h := completingSquare_half a (eta * G)
  nlinarith

/-- A local finite-Pinsker instance for the EG pair implies nonnegativity of the Bregman
divergence between consecutive iterates because the squared explicit one-norm distance is
nonnegative. For terminal-potential nonnegativity with a possibly boundary comparator, use
`entropyBregman_nonneg_of_isSimplex_of_pos` or its EG wrapper in `FinitePinsker.lean`. -/
theorem eg_entropyBregman_nonneg_of_pinsker
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ)
    (hPinsker : l1Dist (egUpdate w g eta) w ^ 2 / 2 ≤
      entropyBregman (egUpdate w g eta) w) :
    0 ≤ entropyBregman (egUpdate w g eta) w := by
  have hsquare : 0 ≤ l1Dist (egUpdate w g eta) w ^ 2 :=
    sq_nonneg (l1Dist (egUpdate w g eta) w)
  linarith

/-- The EG mirror remainder bound conditional only on the displayed finite-Pinsker instance.
The proof separately negates Pinsker, scales the one-sided Hölder bound by nonnegative
`eta`, and completes the square. -/
theorem eg_mirror_remainder_bound_of_pinsker
    {m : ℕ} (w g : Fin m → ℝ) (eta G : ℝ)
    (heta : 0 ≤ eta) (hG : 0 ≤ G)
    (hg : HasCoordinateAbsBound g G)
    (hPinsker : l1Dist (egUpdate w g eta) w ^ 2 / 2 ≤
      entropyBregman (egUpdate w g eta) w) :
    -entropyBregman (egUpdate w g eta) w +
        eta * vectorDot g (primalDisplacement (egUpdate w g eta) w) ≤
      eta ^ 2 * G ^ 2 / 2 := by
  let wPlus := egUpdate w g eta
  let L := l1Dist wPlus w
  have hPinsker' : L ^ 2 / 2 ≤ entropyBregman wPlus w := by
    simpa [L, wPlus] using hPinsker
  have hPinskerNeg :
      -entropyBregman wPlus w ≤ -L ^ 2 / 2 := by
    linarith
  have hHolder :
      vectorDot g (primalDisplacement wPlus w) ≤ G * L := by
    simpa [L, wPlus] using egUpdate_displacement_vectorDot_le w g eta G hG hg
  have hScaledHolder :
      eta * vectorDot g (primalDisplacement wPlus w) ≤ eta * G * L := by
    calc
      eta * vectorDot g (primalDisplacement wPlus w) ≤ eta * (G * L) :=
        mul_le_mul_of_nonneg_left hHolder heta
      _ = eta * G * L := by ring
  have hSquare :
      -L ^ 2 / 2 + eta * G * L ≤ eta ^ 2 * G ^ 2 / 2 :=
    completingSquare_eta_mul L eta G
  have hRemainder :
      -entropyBregman wPlus w +
          eta * vectorDot g (primalDisplacement wPlus w) ≤
        eta ^ 2 * G ^ 2 / 2 := by
    calc
      -entropyBregman wPlus w +
          eta * vectorDot g (primalDisplacement wPlus w) ≤
          -L ^ 2 / 2 + eta * G * L :=
        add_le_add hPinskerNeg hScaledHolder
      _ ≤ eta ^ 2 * G ^ 2 / 2 := hSquare
  simpa [wPlus] using hRemainder

/-- Final EG mirror one-step inequality, conditional on exactly one local finite-Pinsker
instance for `(egUpdate w g eta, w)`. -/
theorem eg_mirror_one_step_of_pinsker
    {m : ℕ} (u w g : Fin m → ℝ) (eta G : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w)
    (heta : 0 ≤ eta) (hG : 0 ≤ G)
    (hg : HasCoordinateAbsBound g G)
    (hPinsker : l1Dist (egUpdate w g eta) w ^ 2 / 2 ≤
      entropyBregman (egUpdate w g eta) w) :
    eta * vectorDot g (primalDisplacement u w) ≤
      entropyBregman u w - entropyBregman u (egUpdate w g eta) +
        eta ^ 2 * G ^ 2 / 2 := by
  have hDecomposition := eg_bregman_decomposition_current
    u w g eta hm hu hw hwpos
  have hRemainder := eg_mirror_remainder_bound_of_pinsker
    w g eta G heta hG hg hPinsker
  calc
    eta * vectorDot g (primalDisplacement u w) =
        entropyBregman u w - entropyBregman u (egUpdate w g eta) -
          entropyBregman (egUpdate w g eta) w +
          eta * vectorDot g (primalDisplacement (egUpdate w g eta) w) :=
      hDecomposition
    _ ≤ entropyBregman u w - entropyBregman u (egUpdate w g eta) +
        eta ^ 2 * G ^ 2 / 2 := by
      linarith

/-- Exact `hmirror` interface for `dual_one_step_substitution` and the expanded unpenalized
and penalized one-step wrappers. Take the consecutive potentials to be
`entropyBregman u w` and `entropyBregman u (egUpdate w g eta)`, and identify the already
squared input as `dualGradSq = G ^ 2` (not `(G ^ 2) ^ 2`). -/
theorem eg_mirror_hmirror_interface
    {m : ℕ} (u w g : Fin m → ℝ) (eta G : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwpos : HasStrictlyPositiveCoordinates w)
    (heta : 0 ≤ eta) (hG : 0 ≤ G)
    (hg : HasCoordinateAbsBound g G)
    (hPinsker : l1Dist (egUpdate w g eta) w ^ 2 / 2 ≤
      entropyBregman (egUpdate w g eta) w) :
    eta * vectorDot g (primalDisplacement u w) ≤
      entropyBregman u w - entropyBregman u (egUpdate w g eta) +
        eta ^ 2 / 2 * (G ^ 2) := by
  calc
    eta * vectorDot g (primalDisplacement u w) ≤
        entropyBregman u w - entropyBregman u (egUpdate w g eta) +
          eta ^ 2 * G ^ 2 / 2 :=
      eg_mirror_one_step_of_pinsker u w g eta G hm hu hw hwpos heta hG hg hPinsker
    _ = entropyBregman u w - entropyBregman u (egUpdate w g eta) +
        eta ^ 2 / 2 * (G ^ 2) := by ring

end NegDRO
