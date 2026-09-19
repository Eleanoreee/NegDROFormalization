import NegDROFormalization.QuadraticStructure

/-!
# Finite-vector Young inequality with the NegDRO constants

This file proves the completing-the-square estimate needed after Appendix Eq. (63). It uses
finite vectors directly and derives the inequality from a sum of coordinatewise squares; no
Cauchy--Schwarz or prepackaged final Young inequality is assumed.
-/

set_option autoImplicit false

namespace NegDRO

/-- The exact finite-vector Young inequality used by the fixed-witness argument:

`2 dot(v,d) / c ≥ -lam * sqNorm(d) - sqNorm(v) / (lam * c²)`.

The proof expands the nonnegative sum `∑ i, (v i + lam * c * d i)²` and divides by the
strictly positive quantity `lam * c²`. -/
theorem vector_young_exact
    {p : ℕ} (v d : Fin p → ℝ) (lam c : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) :
    2 * vectorDot v d / c ≥
      -lam * sqNorm d - sqNorm v / (lam * c ^ 2) := by
  have hsquares : 0 ≤ ∑ i, (v i + lam * c * d i) ^ 2 :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i + lam * c * d i))
  have hexpand :
      (∑ i, (v i + lam * c * d i) ^ 2) =
        sqNorm v +
        (2 * lam * c) * vectorDot v d +
        (lam * c) ^ 2 * sqNorm d := by
    simp only [sqNorm, vectorDot]
    calc
      (∑ i, (v i + lam * c * d i) ^ 2) =
          ∑ i, ((v i) ^ 2 +
            (2 * lam * c) * (v i * d i) +
            (lam * c) ^ 2 * (d i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (v i) ^ 2) +
          (2 * lam * c) * (∑ i, v i * d i) +
          (lam * c) ^ 2 * (∑ i, (d i) ^ 2) := by
        simp_rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.mul_sum]
  rw [hexpand] at hsquares
  have hden : 0 < lam * c ^ 2 := by positivity
  have hnormalized :
      0 ≤ (sqNorm v +
        (2 * lam * c) * vectorDot v d +
        (lam * c) ^ 2 * sqNorm d) / (lam * c ^ 2) :=
    div_nonneg hsquares hden.le
  have hidentity :
      (sqNorm v +
        (2 * lam * c) * vectorDot v d +
        (lam * c) ^ 2 * sqNorm d) / (lam * c ^ 2) =
        2 * vectorDot v d / c +
        lam * sqNorm d +
        sqNorm v / (lam * c ^ 2) := by
    field_simp [ne_of_gt hlam, ne_of_gt hc]
    ring
  rw [hidentity] at hnormalized
  linarith

end NegDRO
