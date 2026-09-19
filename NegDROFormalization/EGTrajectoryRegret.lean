import NegDROFormalization.FinitePinsker
import NegDROFormalization.DualRegretTelescoping

/-!
# Deterministic regret of the uniform-initialized EG trajectory

This module constructs the concrete exponentiated-gradient trajectory and derives its
pathwise online linearized-regret bounds from the finite Pinsker and entropy geometry already
proved in the project. It contains no stochastic or objective-regret statements.

The trajectory is zero-indexed: Lean's `w_0` is the PDF's uniform initialization `w_1`.
Consequently Lean rounds `t = 0, ..., T - 1` correspond to PDF rounds `1, ..., T`.
-/

set_option autoImplicit false

namespace NegDRO

/-- The uniform-initialized exponentiated-gradient trajectory with fixed step size `eta` and
gradient sequence `g`. -/
noncomputable def egTrajectory {m : ℕ}
    (g : ℕ → Fin m → ℝ) (eta : ℝ) : ℕ → Fin m → ℝ
  | 0 => uniformWeight m
  | t + 1 => egUpdate (egTrajectory g eta t) (g t) eta

/-- The EG trajectory starts at the uniform simplex weight. -/
@[simp] theorem egTrajectory_zero
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ) :
    egTrajectory g eta 0 = uniformWeight m := rfl

/-- The exposed one-step recurrence of the EG trajectory. -/
@[simp] theorem egTrajectory_succ
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ) (t : ℕ) :
    egTrajectory g eta (t + 1) =
      egUpdate (egTrajectory g eta t) (g t) eta := rfl

/-- At every time, the concrete EG trajectory is a strictly positive simplex vector. The
claim needs no sign condition on the step size and no coordinate bound on the gradients. -/
theorem egTrajectory_isPositiveSimplex
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (t : ℕ) :
    IsSimplex (egTrajectory g eta t) ∧
      HasStrictlyPositiveCoordinates (egTrajectory g eta t) := by
  induction t with
  | zero =>
      simpa using uniformWeight_isPositiveSimplex m hm
  | succ t iht =>
      rw [egTrajectory_succ]
      exact egUpdate_isPositiveSimplex
        (egTrajectory g eta t) (g t) eta hm iht.1 iht.2

/-- Simplex-membership projection of the combined trajectory invariant. -/
theorem egTrajectory_isSimplex
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (t : ℕ) :
    IsSimplex (egTrajectory g eta t) :=
  (egTrajectory_isPositiveSimplex g eta hm t).1

/-- Strict-coordinate-positivity projection of the combined trajectory invariant. -/
theorem egTrajectory_pos
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (t : ℕ) :
    HasStrictlyPositiveCoordinates (egTrajectory g eta t) :=
  (egTrajectory_isPositiveSimplex g eta hm t).2

/-- Entropy potential of comparator `u` against the concrete EG trajectory. -/
noncomputable def egPotential {m : ℕ}
    (g : ℕ → Fin m → ℝ) (eta : ℝ) (u : Fin m → ℝ) (t : ℕ) : ℝ :=
  entropyBregman u (egTrajectory g eta t)

/-- Pathwise online linearized regret at round `t`. This is not objective regret. -/
noncomputable def egLinearizedRegret {m : ℕ}
    (g : ℕ → Fin m → ℝ) (eta : ℝ) (u : Fin m → ℝ) (t : ℕ) : ℝ :=
  vectorDot (g t) (primalDisplacement u (egTrajectory g eta t))

/-- Concrete per-round mirror inequality along the actual EG recurrence. Pinsker and all
trajectory invariants are discharged by the existing deterministic modules. -/
theorem egTrajectory_mirror_one_step
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ)
    (G : ℕ → ℝ) (u : Fin m → ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (heta : 0 ≤ eta)
    (t : ℕ) (hG : 0 ≤ G t)
    (hg : HasCoordinateAbsBound (g t) (G t)) :
    eta * egLinearizedRegret g eta u t ≤
      egPotential g eta u t - egPotential g eta u (t + 1) +
        eta ^ 2 / 2 * (G t) ^ 2 := by
  have hwt := egTrajectory_isPositiveSimplex g eta hm t
  simpa [egLinearizedRegret, egPotential] using
    (eg_mirror_hmirror u (egTrajectory g eta t) (g t) eta (G t)
      hm hu hwt.1 hwt.2 heta hG hg)

/-- The actual uniform initialization supplies the initial entropy-potential bound. -/
theorem egTrajectory_initialPotential_le_log
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ) (u : Fin m → ℝ)
    (hm : 0 < m) (hu : IsSimplex u) :
    egPotential g eta u 0 ≤ Real.log (m : ℝ) := by
  simpa [egPotential] using entropyBregman_uniformWeight_le_log u hm hu

/-- Every terminal trajectory potential is nonnegative, including when comparator `u` has
zero coordinates. This uses positivity of the trajectory base, not interiority of `u`. -/
theorem egTrajectory_terminalPotential_nonneg
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ) (u : Fin m → ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (T : ℕ) :
    0 ≤ egPotential g eta u T := by
  exact entropyBregman_nonneg_of_isSimplex_of_pos
    u (egTrajectory g eta T) hu (egTrajectory_pos g eta hm T)

/-- Complete deterministic varying-coordinate-bound regret theorem for the concrete EG path.
The squared-gradient input to telescoping is exactly `dualGradSq t = (G t)^2`. -/
theorem egTrajectory_cumulative_linearizedRegret
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta : ℝ)
    (G : ℕ → ℝ) (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (hG : ∀ t < T, 0 ≤ G t)
    (hg : ∀ t < T, HasCoordinateAbsBound (g t) (G t)) :
    ∑ t ∈ Finset.range T, egLinearizedRegret g eta u t ≤
      Real.log (m : ℝ) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, (G t) ^ 2 := by
  exact dual_cumulative_regret_of_initialPotentialBound
    T (egPotential g eta u) (egLinearizedRegret g eta u)
      (egLinearizedRegret g eta u) (fun t => (G t) ^ 2)
      eta (Real.log (m : ℝ))
      (fun _ _ => le_rfl)
      (fun t ht => egTrajectory_mirror_one_step
        g eta G u hm hu heta.le t (hG t ht) (hg t ht))
      heta
      (egTrajectory_terminalPotential_nonneg g eta u hm hu T)
      (egTrajectory_initialPotential_le_log g eta u hm hu)

/-- Uniform-coordinate-bound specialization of the concrete cumulative regret theorem. The
quantity `G^2` is passed once as the already-squared dual-gradient bound. -/
theorem egTrajectory_cumulative_linearizedRegret_uniform
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta G : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (hG : 0 ≤ G)
    (hg : ∀ t < T, HasCoordinateAbsBound (g t) G) :
    ∑ t ∈ Finset.range T, egLinearizedRegret g eta u t ≤
      Real.log (m : ℝ) / eta + eta * (T : ℝ) / 2 * G ^ 2 := by
  calc
    ∑ t ∈ Finset.range T, egLinearizedRegret g eta u t ≤
        Real.log (m : ℝ) / eta +
          eta / 2 * ∑ _t ∈ Finset.range T, G ^ 2 :=
      egTrajectory_cumulative_linearizedRegret
        g eta (fun _ => G) u T hm heta hu
        (fun _ _ => hG) hg
    _ = Real.log (m : ℝ) / eta + eta * (T : ℝ) / 2 * G ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Average pathwise linearized-regret bound for a positive number of rounds. Every division
is in `ℝ`; positivity of the coerced round count follows from `hT`. -/
theorem egTrajectory_average_linearizedRegret_uniform
    {m : ℕ} (g : ℕ → Fin m → ℝ) (eta G : ℝ)
    (u : Fin m → ℝ) (T : ℕ)
    (hm : 0 < m) (heta : 0 < eta) (hu : IsSimplex u)
    (hT : 0 < T) (hG : 0 ≤ G)
    (hg : ∀ t < T, HasCoordinateAbsBound (g t) G) :
    (1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T, egLinearizedRegret g eta u t ≤
      Real.log (m : ℝ) / (eta * (T : ℝ)) + eta / 2 * G ^ 2 := by
  have hcum := egTrajectory_cumulative_linearizedRegret_uniform
    g eta G u T hm heta hu hG hg
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hscaled := mul_le_mul_of_nonneg_left hcum
    (by positivity : 0 ≤ 1 / (T : ℝ))
  calc
    (1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T, egLinearizedRegret g eta u t ≤
      (1 / (T : ℝ)) *
        (Real.log (m : ℝ) / eta + eta * (T : ℝ) / 2 * G ^ 2) := hscaled
    _ = Real.log (m : ℝ) / (eta * (T : ℝ)) + eta / 2 * G ^ 2 := by
      field_simp

end NegDRO
