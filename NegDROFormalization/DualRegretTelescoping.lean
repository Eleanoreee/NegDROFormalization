import NegDROFormalization.RegretToConvergence

/-!
# Deterministic dual-regret telescoping

This module verifies the deterministic telescoping consequence of the mirror-ascent one-step
inequality. It does not yet prove that exponentiated-gradient updates satisfy that inequality,
nor that the stochastic oracle converts actual objective regret into the linearized regret term.

All sequences are scalar and zero-indexed over `Finset.range T`, consistently with
`RegretToConvergence.lean`. The input `dualGradSq t` and uniform parameter
`dualGradSqBound` are already squared dual-gradient quantities and are never squared again.
-/

set_option autoImplicit false

namespace NegDRO

/-- Pointwise substitution of actual regret below linearized regret into the mirror one-step
inequality. Neither regret quantity nor the squared-gradient input needs to be nonnegative. -/
theorem dual_one_step_substitution
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta : ℝ) (t : ℕ)
    (hregret : regret t ≤ linearizedRegret t)
    (hmirror : eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 ≤ eta) :
    eta * regret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t := by
  have hscaled : eta * regret t ≤ eta * linearizedRegret t :=
    mul_le_mul_of_nonneg_left hregret heta
  exact hscaled.trans hmirror

/-- Cumulative dual regret with the terminal potential retained. The proof sums the
pointwise mirror inequalities and invokes the existing exact identity
`sum_range_sub_succ potential T`. No sign assumptions are made on regret, linearized regret,
or `dualGradSq`. -/
theorem dual_cumulative_regret_with_terminal
    (T : ℕ)
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta : ℝ)
    (hregret : ∀ t < T, regret t ≤ linearizedRegret t)
    (hmirror : ∀ t < T, eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 < eta) :
    ∑ t ∈ Finset.range T, regret t ≤
      (potential 0 - potential T) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, dualGradSq t := by
  have hpoint : ∀ t ∈ Finset.range T,
      eta * regret t ≤
        potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t := by
    intro t ht
    have htT := Finset.mem_range.mp ht
    exact dual_one_step_substitution potential linearizedRegret regret dualGradSq eta t
      (hregret t htT) (hmirror t htT) heta.le
  have hsum :
      ∑ t ∈ Finset.range T, eta * regret t ≤
        ∑ t ∈ Finset.range T,
          (potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t) := by
    apply Finset.sum_le_sum
    intro t ht
    exact hpoint t ht
  have hscaled :
      eta * (∑ t ∈ Finset.range T, regret t) ≤
        potential 0 - potential T +
          eta ^ 2 / 2 * ∑ t ∈ Finset.range T, dualGradSq t := by
    calc
      eta * (∑ t ∈ Finset.range T, regret t) =
          ∑ t ∈ Finset.range T, eta * regret t := by
        rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.range T,
          (potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t) := hsum
      _ = potential 0 - potential T +
          eta ^ 2 / 2 * ∑ t ∈ Finset.range T, dualGradSq t := by
        rw [Finset.sum_add_distrib, sum_range_sub_succ]
        rw [← Finset.mul_sum]
  calc
    (∑ t ∈ Finset.range T, regret t) =
        (eta * ∑ t ∈ Finset.range T, regret t) / eta := by
      field_simp
    _ ≤ (potential 0 - potential T +
          eta ^ 2 / 2 * ∑ t ∈ Finset.range T, dualGradSq t) / eta :=
      (div_le_div_iff_of_pos_right heta).2 hscaled
    _ = (potential 0 - potential T) / eta +
        eta / 2 * ∑ t ∈ Finset.range T, dualGradSq t := by
      field_simp

/-- Cumulative dual regret after dropping only the nonnegative terminal potential. No
nonnegativity assumption is imposed on earlier potential values. -/
theorem dual_cumulative_regret
    (T : ℕ)
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta : ℝ)
    (hregret : ∀ t < T, regret t ≤ linearizedRegret t)
    (hmirror : ∀ t < T, eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 < eta)
    (hterminal : 0 ≤ potential T) :
    ∑ t ∈ Finset.range T, regret t ≤
      potential 0 / eta + eta / 2 * ∑ t ∈ Finset.range T, dualGradSq t := by
  have hretained := dual_cumulative_regret_with_terminal
    T potential linearizedRegret regret dualGradSq eta hregret hmirror heta
  have hdrop : (potential 0 - potential T) / eta ≤ potential 0 / eta :=
    (div_le_div_iff_of_pos_right heta).2 (by linarith)
  linarith

/-- Cumulative regret with the initial potential replaced by a generic upper bound. -/
theorem dual_cumulative_regret_of_initialPotentialBound
    (T : ℕ)
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta initialPotentialBound : ℝ)
    (hregret : ∀ t < T, regret t ≤ linearizedRegret t)
    (hmirror : ∀ t < T, eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 < eta)
    (hterminal : 0 ≤ potential T)
    (hinitial : potential 0 ≤ initialPotentialBound) :
    ∑ t ∈ Finset.range T, regret t ≤
      initialPotentialBound / eta +
        eta / 2 * ∑ t ∈ Finset.range T, dualGradSq t := by
  have hbase := dual_cumulative_regret T potential linearizedRegret regret dualGradSq
    eta hregret hmirror heta hterminal
  have hinitialDiv : potential 0 / eta ≤ initialPotentialBound / eta :=
    (div_le_div_iff_of_pos_right heta).2 hinitial
  linarith

/-- Uniform squared-dual-gradient specialization. The parameter `dualGradSqBound` already
denotes `G_w^2`; the result contains it linearly. -/
theorem dual_cumulative_regret_of_uniform_gradSq
    (T : ℕ)
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta initialPotentialBound dualGradSqBound : ℝ)
    (hregret : ∀ t < T, regret t ≤ linearizedRegret t)
    (hmirror : ∀ t < T, eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 < eta)
    (hterminal : 0 ≤ potential T)
    (hinitial : potential 0 ≤ initialPotentialBound)
    (hdualGrad : ∀ t < T, dualGradSq t ≤ dualGradSqBound) :
    ∑ t ∈ Finset.range T, regret t ≤
      initialPotentialBound / eta + eta * (T : ℝ) / 2 * dualGradSqBound := by
  have hbase := dual_cumulative_regret_of_initialPotentialBound
    T potential linearizedRegret regret dualGradSq eta initialPotentialBound
    hregret hmirror heta hterminal hinitial
  have hsumGrad :
      (∑ t ∈ Finset.range T, dualGradSq t) ≤ (T : ℝ) * dualGradSqBound := by
    calc
      (∑ t ∈ Finset.range T, dualGradSq t) ≤
          ∑ t ∈ Finset.range T, dualGradSqBound := by
        apply Finset.sum_le_sum
        intro t ht
        exact hdualGrad t (Finset.mem_range.mp ht)
      _ = (T : ℝ) * dualGradSqBound := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hscaledGrad :
      eta / 2 * (∑ t ∈ Finset.range T, dualGradSq t) ≤
        eta / 2 * ((T : ℝ) * dualGradSqBound) :=
    mul_le_mul_of_nonneg_left hsumGrad (by positivity)
  nlinarith

/-- Average-regret form of the uniform squared-gradient bound. -/
theorem dual_average_regret_of_uniform_gradSq
    (T : ℕ)
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta initialPotentialBound dualGradSqBound : ℝ)
    (hT : 0 < T)
    (hregret : ∀ t < T, regret t ≤ linearizedRegret t)
    (hmirror : ∀ t < T, eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 < eta)
    (hterminal : 0 ≤ potential T)
    (hinitial : potential 0 ≤ initialPotentialBound)
    (hdualGrad : ∀ t < T, dualGradSq t ≤ dualGradSqBound) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, regret t ≤
      initialPotentialBound / (eta * (T : ℝ)) + eta / 2 * dualGradSqBound := by
  have hcum := dual_cumulative_regret_of_uniform_gradSq
    T potential linearizedRegret regret dualGradSq eta initialPotentialBound dualGradSqBound
    hregret hmirror heta hterminal hinitial hdualGrad
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hscaled := mul_le_mul_of_nonneg_left hcum (by positivity : 0 ≤ 1 / (T : ℝ))
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, regret t ≤
        (1 / (T : ℝ)) *
          (initialPotentialBound / eta + eta * (T : ℝ) / 2 * dualGradSqBound) := hscaled
    _ = initialPotentialBound / (eta * (T : ℝ)) +
        eta / 2 * dualGradSqBound := by
      field_simp

/-- Exact admissible substitution for the cumulative regret parameter `R_T` in
`telescoping_average_bound`, `scalar_proposition_A2`, and its theorem-level specializations in
`RegretToConvergence.lean`: choose
`R_T = initialPotentialBound / eta + eta * T / 2 * dualGradSqBound`.
This bridge supplies only the required scalar sum bound and does not repeat the convergence
proof. -/
theorem dual_totalRegretBound_for_scalar_convergence
    (T : ℕ)
    (potential linearizedRegret regret dualGradSq : ℕ → ℝ)
    (eta initialPotentialBound dualGradSqBound : ℝ)
    (hregret : ∀ t < T, regret t ≤ linearizedRegret t)
    (hmirror : ∀ t < T, eta * linearizedRegret t ≤
      potential t - potential (t + 1) + eta ^ 2 / 2 * dualGradSq t)
    (heta : 0 < eta)
    (hterminal : 0 ≤ potential T)
    (hinitial : potential 0 ≤ initialPotentialBound)
    (hdualGrad : ∀ t < T, dualGradSq t ≤ dualGradSqBound) :
    let R_T := initialPotentialBound / eta + eta * (T : ℝ) / 2 * dualGradSqBound
    ∑ t ∈ Finset.range T, regret t ≤ R_T := by
  exact dual_cumulative_regret_of_uniform_gradSq
    T potential linearizedRegret regret dualGradSq eta initialPotentialBound dualGradSqBound
    hregret hmirror heta hterminal hinitial hdualGrad

end NegDRO
