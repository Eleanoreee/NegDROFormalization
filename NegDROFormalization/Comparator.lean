import Mathlib

/-!
# Scalar comparator identities for NegDRO

This file isolates the real-number algebra underlying Appendix equations (64)--(67). The
variables `q`, `n₀`, `nₜ`, and `D` are scalar placeholders; no matrix, norm, simplex, or
probability structure is introduced here.
-/

set_option autoImplicit false

namespace NegDRO

/--
Appendix Eq. (64), in scalar form. If
`L = (s + 2 * x) / c + q` and `g = (2 * x) / c + 2 * q`, then the displayed decomposition
of `L` follows algebraically. The hypothesis `c ≠ 0` records the nonzero denominator in the
PDF model, where `c = 1 + gamma m > 0`; Lean's real-number division itself is total at zero.
-/
theorem common_unpenalized_identity
    (s x q c L g : ℝ)
    (hc : c ≠ 0)
    (hL : L = (s + 2 * x) / c + q)
    (hg : g = (2 * x) / c + 2 * q) :
    L = (1 / 2 : ℝ) * g + (s + x) / c := by
  rw [hL, hg]
  field_simp [hc]
  ring

/--
Appendix Eq. (65), in scalar form. Starting from Eq. (64), this records the result of
subtracting the arbitrary penalty `μ * n`; no sign assumption on `μ` or `n` is needed.
-/
theorem common_penalized_identity
    (s x q c L g μ n Lμ : ℝ)
    (hc : c ≠ 0)
    (hL : L = (s + 2 * x) / c + q)
    (hg : g = (2 * x) / c + 2 * q)
    (hLμ : Lμ = L - μ * n) :
    Lμ = (1 / 2 : ℝ) * g + (s + x) / c - μ * n := by
  rw [hLμ, common_unpenalized_identity s x q c L g hc hL hg]

/--
Appendix Eq. (66). The same scalar `C` occurs in both loss decompositions, representing
the term that is independent of the comparator `w`.
-/
theorem unpenalized_comparator_identity
    (L₀ Lₜ g₀ gₜ C r : ℝ)
    (hL₀ : L₀ = (1 / 2 : ℝ) * g₀ + C)
    (hLₜ : Lₜ = (1 / 2 : ℝ) * gₜ + C)
    (hr : r = L₀ - Lₜ) :
    gₜ = g₀ - 2 * r := by
  linarith

/--
Appendix Eq. (67). The scalars `n₀` and `nₜ` stand for the two squared norms in the
penalized comparator calculation.
-/
theorem penalized_comparator_identity
    (L₀ Lₜ g₀ gₜ C μ n₀ nₜ r : ℝ)
    (hL₀ : L₀ = (1 / 2 : ℝ) * g₀ + C - μ * n₀)
    (hLₜ : Lₜ = (1 / 2 : ℝ) * gₜ + C - μ * nₜ)
    (hr : r = L₀ - Lₜ) :
    gₜ = g₀ - 2 * r - 2 * μ * (n₀ - nₜ) := by
  nlinarith

/--
Scalar consequence of the simplex norm bounds. For actual simplex vectors, the hypotheses
`n₀ ≤ 1` and `0 ≤ nₜ` are supplied by `simplex_sqNorm_bounds`, and the resulting difference
bound is packaged as `simplex_sqNorm_difference_le_one` in `Simplex.lean`.
-/
theorem simplex_norm_difference_le_one
    (n₀ nₜ : ℝ)
    (hn₀ : n₀ ≤ 1)
    (hnₜ : 0 ≤ nₜ) :
    n₀ - nₜ ≤ 1 := by
  linarith

/--
Lower bound on the scalar penalty correction. For actual simplex vectors, these scalar
hypotheses and this conclusion are discharged by `simplex_sqNorm_bounds` and
`simplex_sqNorm_penalty_correction_lower_bound` in `Simplex.lean`.
-/
theorem simplex_penalty_correction_lower_bound
    (μ n₀ nₜ : ℝ)
    (hμ : 0 ≤ μ)
    (hn₀ : n₀ ≤ 1)
    (hnₜ : 0 ≤ nₜ) :
    -2 * μ * (n₀ - nₜ) ≥ -2 * μ := by
  have hdiff : n₀ - nₜ ≤ 1 := simplex_norm_difference_le_one n₀ nₜ hn₀ hnₜ
  have hprod : 0 ≤ μ * (1 - (n₀ - nₜ)) :=
    mul_nonneg hμ (sub_nonneg.mpr hdiff)
  nlinarith

/--
Abstract unpenalized comparator-to-primal reduction obtained by combining the lower bound
at the reference comparator with the scalar relation from Eq. (66).
-/
theorem unpenalized_comparator_to_primal
    (g₀ gₜ lam D ε r : ℝ)
    (hg₀ : g₀ ≥ lam * D - ε)
    (hcompare : gₜ = g₀ - 2 * r) :
    gₜ ≥ lam * D - ε - 2 * r := by
  linarith

/--
Abstract penalized comparator-to-primal reduction obtained from Eq. (67). The scalar `D`
stands for the future squared primal error. Only `0 ≤ μ` and `n₀ - nₜ ≤ 1` are needed to
control the penalty correction.
-/
theorem penalized_comparator_to_primal
    (g₀ gₜ lam D ε r μ n₀ nₜ : ℝ)
    (hg₀ : g₀ ≥ lam * D - ε)
    (hcompare : gₜ = g₀ - 2 * r - 2 * μ * (n₀ - nₜ))
    (hμ : 0 ≤ μ)
    (hdiff : n₀ - nₜ ≤ 1) :
    gₜ ≥ lam * D - ε - 2 * r - 2 * μ := by
  have hprod : 0 ≤ μ * (1 - (n₀ - nₜ)) :=
    mul_nonneg hμ (sub_nonneg.mpr hdiff)
  nlinarith

end NegDRO
