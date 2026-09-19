import Mathlib

/-!
# Deterministic scalar core of Proposition A.2

This file treats `distSq`, `direction`, and `regret` as ordinary real-valued sequences.
They represent the corresponding quantities *after* expectations have been taken. Probability,
conditional expectation, and the origin of the regret bound are deliberately not formalized here.

Lean uses zero-based rounds `t ∈ Finset.range T`, namely `t = 0, ..., T - 1`. These correspond
to rounds `1, ..., T` in the PDF.

The parameter `gradSqBound` is already the squared-gradient-moment bound. Its intended future
stochastic instantiation is exactly `gradSqBound = G_b² = 4m M_{rX}` from the PDF; no square root
is introduced. Although that future value is nonnegative, the scalar algebra below does not need
a nonnegativity assumption on `gradSqBound`.
-/

set_option autoImplicit false

namespace NegDRO

/-- Substituting the comparator lower bound into one step of the distance recursion. The
hypothesis `0 ≤ η` ensures that multiplying the lower bound on `F` by `-2η` reverses it in
the required direction. -/
theorem one_step_substitution
    (Dnext D F η lam ε δ r gradSqBound : ℝ)
    (hrec : Dnext ≤ D - 2 * η * F + η ^ 2 * gradSqBound)
    (hdirection : F ≥ lam * D - ε - δ - 2 * r)
    (hη : 0 ≤ η) :
    Dnext ≤ D - 2 * η * (lam * D - ε - δ - 2 * r) + η ^ 2 * gradSqBound := by
  have hscale : 0 ≤ 2 * η := by positivity
  have hscaled :
      2 * η * (lam * D - ε - δ - 2 * r) ≤ 2 * η * F :=
    mul_le_mul_of_nonneg_left hdirection hscale
  nlinarith

/-- The finite adjacent differences over zero-based rounds telescope to the initial value
minus the terminal value. This is the finite-sum identity used in Proposition A.2. -/
theorem sum_range_sub_succ
    (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (f t - f (t + 1)) = f 0 - f T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Pure telescoping form of the deterministic scalar argument in Proposition A.2. The proof
sums all one-step inequalities over `Finset.range T`, telescopes the distance differences,
uses terminal nonnegativity and the cumulative regret bound, and finally divides by the positive
quantity `2 * lam * η * T`. -/
theorem telescoping_average_bound
    (T : ℕ)
    (distSq regret : ℕ → ℝ)
    (η lam ε δ gradSqBound R_T : ℝ)
    (hT : 0 < T)
    (hstep : ∀ t < T,
      distSq (t + 1) ≤
        distSq t - 2 * η * (lam * distSq t - ε - δ - 2 * regret t) +
          η ^ 2 * gradSqBound)
    (hterminal : 0 ≤ distSq T)
    (hregret : ∑ t ∈ Finset.range T, regret t ≤ R_T)
    (hη : 0 < η)
    (hlam : 0 < lam) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, distSq t ≤
      distSq 0 / (2 * lam * η * (T : ℝ)) +
      (ε + δ) / lam +
      2 * R_T / (lam * (T : ℝ)) +
      η * gradSqBound / (2 * lam) := by
  have hrearranged : ∀ t < T,
      2 * η * lam * distSq t ≤
        (distSq t - distSq (t + 1)) +
        2 * η * (ε + δ) +
        4 * η * regret t +
        η ^ 2 * gradSqBound := by
    intro t ht
    have htstep := hstep t ht
    nlinarith
  have hsum :
      (∑ t ∈ Finset.range T, 2 * η * lam * distSq t) ≤
        ∑ t ∈ Finset.range T,
          ((distSq t - distSq (t + 1)) +
          2 * η * (ε + δ) +
          4 * η * regret t +
          η ^ 2 * gradSqBound) := by
    apply Finset.sum_le_sum
    intro t ht
    exact hrearranged t (Finset.mem_range.mp ht)
  have hcum :
      2 * lam * η * (∑ t ∈ Finset.range T, distSq t) ≤
        distSq 0 - distSq T +
        2 * η * (T : ℝ) * (ε + δ) +
        4 * η * (∑ t ∈ Finset.range T, regret t) +
        (T : ℝ) * η ^ 2 * gradSqBound := by
    calc
      2 * lam * η * (∑ t ∈ Finset.range T, distSq t) =
          ∑ t ∈ Finset.range T, 2 * η * lam * distSq t := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ ≤ ∑ t ∈ Finset.range T,
          ((distSq t - distSq (t + 1)) +
          2 * η * (ε + δ) +
          4 * η * regret t +
          η ^ 2 * gradSqBound) := hsum
      _ = distSq 0 - distSq T +
          2 * η * (T : ℝ) * (ε + δ) +
          4 * η * (∑ t ∈ Finset.range T, regret t) +
          (T : ℝ) * η ^ 2 * gradSqBound := by
            simp_rw [Finset.sum_add_distrib]
            rw [sum_range_sub_succ]
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [← Finset.mul_sum]
            ring
  have hregret_scaled :
      4 * η * (∑ t ∈ Finset.range T, regret t) ≤ 4 * η * R_T := by
    exact mul_le_mul_of_nonneg_left hregret (by positivity)
  have hcum_bound :
      2 * lam * η * (∑ t ∈ Finset.range T, distSq t) ≤
        distSq 0 +
        2 * η * (T : ℝ) * (ε + δ) +
        4 * η * R_T +
        (T : ℝ) * η ^ 2 * gradSqBound := by
    linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < 2 * lam * η * (T : ℝ) := by positivity
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, distSq t =
        (2 * lam * η * (∑ t ∈ Finset.range T, distSq t)) /
          (2 * lam * η * (T : ℝ)) := by
            field_simp
    _ ≤ (distSq 0 +
          2 * η * (T : ℝ) * (ε + δ) +
          4 * η * R_T +
          (T : ℝ) * η ^ 2 * gradSqBound) /
          (2 * lam * η * (T : ℝ)) :=
      (div_le_div_iff_of_pos_right hden).2 hcum_bound
    _ = distSq 0 / (2 * lam * η * (T : ℝ)) +
        (ε + δ) / lam +
        2 * R_T / (lam * (T : ℝ)) +
        η * gradSqBound / (2 * lam) := by
          field_simp
          ring

/-- Scalar deterministic core of Proposition A.2. The distance recursion and comparator
lower bound are kept as separate assumptions. The wrapper combines them with
`one_step_substitution` and then invokes `telescoping_average_bound`. -/
theorem scalar_proposition_A2
    (T : ℕ)
    (distSq direction regret : ℕ → ℝ)
    (η lam ε δ gradSqBound R_T : ℝ)
    (hT : 0 < T)
    (hrec : ∀ t < T,
      distSq (t + 1) ≤ distSq t - 2 * η * direction t + η ^ 2 * gradSqBound)
    (hdirection : ∀ t < T,
      direction t ≥ lam * distSq t - ε - δ - 2 * regret t)
    (hterminal : 0 ≤ distSq T)
    (hregret : ∑ t ∈ Finset.range T, regret t ≤ R_T)
    (hη : 0 < η)
    (hlam : 0 < lam) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, distSq t ≤
      distSq 0 / (2 * lam * η * (T : ℝ)) +
      (ε + δ) / lam +
      2 * R_T / (lam * (T : ℝ)) +
      η * gradSqBound / (2 * lam) := by
  apply telescoping_average_bound T distSq regret η lam ε δ gradSqBound R_T hT
  · intro t ht
    exact one_step_substitution
      (distSq (t + 1)) (distSq t) (direction t) η lam ε δ (regret t) gradSqBound
      (hrec t ht) (hdirection t ht) hη.le
  · exact hterminal
  · exact hregret
  · exact hη
  · exact hlam

/-- Unpenalized specialization of the scalar Proposition A.2 core, corresponding to Theorem 4.3
with `ε = ε_id`, `δ = 0`, and `regret t = Reg_t⁰`. -/
theorem scalar_theorem_4_3_unpenalized
    (T : ℕ)
    (distSq direction regret : ℕ → ℝ)
    (η lam ε gradSqBound R_T : ℝ)
    (hT : 0 < T)
    (hrec : ∀ t < T,
      distSq (t + 1) ≤ distSq t - 2 * η * direction t + η ^ 2 * gradSqBound)
    (hdirection : ∀ t < T,
      direction t ≥ lam * distSq t - ε - 2 * regret t)
    (hterminal : 0 ≤ distSq T)
    (hregret : ∑ t ∈ Finset.range T, regret t ≤ R_T)
    (hη : 0 < η)
    (hlam : 0 < lam) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, distSq t ≤
      distSq 0 / (2 * lam * η * (T : ℝ)) +
      ε / lam +
      2 * R_T / (lam * (T : ℝ)) +
      η * gradSqBound / (2 * lam) := by
  have hdirection_zero : ∀ t < T,
      direction t ≥ lam * distSq t - ε - 0 - 2 * regret t := by
    intro t ht
    simpa using hdirection t ht
  have hcore := scalar_proposition_A2
    T distSq direction regret η lam ε 0 gradSqBound R_T hT hrec hdirection_zero
    hterminal hregret hη hlam
  simpa using hcore

/-- Penalized specialization of the scalar Proposition A.2 core, corresponding to Theorem 3.4
with `ε = ε_id`, `δ = 2μ`, and `regret t = Reg_{t,μ}⁰`. The hypothesis `0 ≤ μ` is required
upstream to derive the `-2 * μ` direction correction from the simplex penalty. Once that direction
inequality is supplied below, the final scalar telescoping algebra itself does not use the sign of
`μ`; `_hμ` is retained to record the intended penalized regime. -/
theorem scalar_theorem_3_4_penalized
    (T : ℕ)
    (distSq direction regret : ℕ → ℝ)
    (η lam ε μ gradSqBound R_T : ℝ)
    (hT : 0 < T)
    (hrec : ∀ t < T,
      distSq (t + 1) ≤ distSq t - 2 * η * direction t + η ^ 2 * gradSqBound)
    (hdirection : ∀ t < T,
      direction t ≥ lam * distSq t - ε - 2 * μ - 2 * regret t)
    (hterminal : 0 ≤ distSq T)
    (hregret : ∑ t ∈ Finset.range T, regret t ≤ R_T)
    (hη : 0 < η)
    (hlam : 0 < lam)
    (_hμ : 0 ≤ μ) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, distSq t ≤
      distSq 0 / (2 * lam * η * (T : ℝ)) +
      ε / lam +
      2 * μ / lam +
      2 * R_T / (lam * (T : ℝ)) +
      η * gradSqBound / (2 * lam) := by
  have hcore := scalar_proposition_A2
    T distSq direction regret η lam ε (2 * μ) gradSqBound R_T hT hrec
    (by
      intro t ht
      simpa only [sub_sub] using hdirection t ht)
    hterminal hregret hη hlam
  convert hcore using 1
  ring

end NegDRO
