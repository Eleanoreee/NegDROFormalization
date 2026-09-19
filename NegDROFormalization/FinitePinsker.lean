import NegDROFormalization.MirrorRemainderBound

/-!
# Exact finite Pinsker inequality

This module proves the exact natural-logarithm Pinsker inequality for strictly positive finite
simplex vectors. The proof is finite-dimensional: a finite log-sum inequality reduces to binary
Pinsker, whose constant is proved by convexity of the binary entropy gap.

The project distance is the unnormalized quantity `sum_i |p_i - q_i|`; consequently the final
coefficient is exactly one half. A separate coordinatewise entropy-tangent argument proves
Bregman nonnegativity when the first vector may have zero coordinates.
-/

set_option autoImplicit false

namespace NegDRO

/-- Explicit finite relative entropy with natural logarithms. -/
noncomputable def finiteKL {m : ℕ} (p q : Fin m → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- The scalar KL summand with its affine correction is nonnegative. The first input may be
zero; the second is strictly positive. -/
theorem scalarKL_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.log (a / b) - a + b := by
  by_cases ha0 : a = 0
  · subst a
    simp [hb.le]
  · have hab : 0 ≤ a / b := div_nonneg ha hb.le
    have hbase := Real.self_sub_one_le_mul_log hab
    have hscaled := mul_le_mul_of_nonneg_left hbase hb.le
    have hbne : b ≠ 0 := ne_of_gt hb
    field_simp [hbne] at hscaled
    nlinarith

/-- Scalar negative-entropy tangent inequality. The case `a = 0` is handled separately, so
the theorem permits a boundary coordinate. -/
theorem entropyScalar_tangent_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ entropyScalar a - entropyScalar b -
      (1 + Real.log b) * (a - b) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [entropyScalar, zero_mul, Real.log_zero]
    nlinarith [hb.le]
  · have hkl := scalarKL_nonneg ha hb
    rw [Real.log_div ha0 (ne_of_gt hb)] at hkl
    simp only [entropyScalar]
    nlinarith

/-- The entropy Bregman divergence equals explicit finite KL for strictly positive simplex
vectors. The affine Bregman contribution vanishes because both coordinate sums are one. -/
theorem entropyBregman_eq_finiteKL
    {m : ℕ} (p q : Fin m → ℝ)
    (hp : IsSimplex p) (hq : IsSimplex q)
    (hpPos : HasStrictlyPositiveCoordinates p)
    (hqPos : HasStrictlyPositiveCoordinates q) :
    entropyBregman p q = finiteKL p q := by
  simp only [entropyBregman, negativeEntropy, vectorDot, entropyGradient,
    primalDisplacement]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  calc
    (∑ i, (entropyScalar (p i) - entropyScalar (q i) -
        (1 + Real.log (q i)) * (p i - q i))) =
        ∑ i, (p i * Real.log (p i / q i) - p i + q i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [entropyScalar, entropyScalar,
        Real.log_div (ne_of_gt (hpPos i)) (ne_of_gt (hqPos i))]
      ring
    _ = finiteKL p q := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.2, hq.2]
      simp only [finiteKL]
      ring

/-- Entropy Bregman nonnegativity with a possibly boundary first vector. Simplex membership of
the positive base vector is not needed: coordinatewise tangent nonnegativity suffices. -/
theorem entropyBregman_nonneg_of_isSimplex_of_pos
    {m : ℕ} (p q : Fin m → ℝ)
    (hp : IsSimplex p) (hqPos : HasStrictlyPositiveCoordinates q) :
    0 ≤ entropyBregman p q := by
  simp only [entropyBregman, negativeEntropy, vectorDot, entropyGradient,
    primalDisplacement]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_nonneg (fun i _ =>
    entropyScalar_tangent_nonneg (hp.1 i) (hqPos i))

/-- Finite log-sum inequality. The numerator coordinates may vanish, while denominator
coordinates and both aggregate masses are strictly positive. -/
theorem finite_log_sum
    {α : Type*} (s : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hA : 0 < ∑ i ∈ s, a i) (hB : 0 < ∑ i ∈ s, b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  let A : ℝ := ∑ i ∈ s, a i
  let B : ℝ := ∑ i ∈ s, b i
  have hA' : 0 < A := by simpa [A] using hA
  have hB' : 0 < B := by simpa [B] using hB
  have hcoord : ∀ i ∈ s,
      0 ≤ (a i * B) * Real.log ((a i * B) / (b i * A)) - a i * B + b i * A := by
    intro i hi
    exact scalarKL_nonneg (mul_nonneg (ha i hi) hB'.le) (mul_pos (hb i hi) hA')
  have hsum : 0 ≤ ∑ i ∈ s,
      ((a i * B) * Real.log ((a i * B) / (b i * A)) - a i * B + b i * A) :=
    Finset.sum_nonneg hcoord
  have hterm : ∀ i ∈ s,
      (a i * B) * Real.log ((a i * B) / (b i * A)) - a i * B + b i * A =
        B * (a i * Real.log (a i / b i) - a i * Real.log (A / B)) -
          a i * B + b i * A := by
    intro i hi
    by_cases hai : a i = 0
    · rw [hai]
      ring
    · have hbi := hb i hi
      have hlog :
          Real.log ((a i * B) / (b i * A)) =
            Real.log (a i / b i) - Real.log (A / B) := by
        rw [Real.log_div (mul_ne_zero hai (ne_of_gt hB'))
          (mul_ne_zero (ne_of_gt hbi) (ne_of_gt hA')),
          Real.log_mul hai (ne_of_gt hB'),
          Real.log_mul (ne_of_gt hbi) (ne_of_gt hA'),
          Real.log_div hai (ne_of_gt hbi),
          Real.log_div (ne_of_gt hA') (ne_of_gt hB')]
        ring
      rw [hlog]
      ring
  have heq :
      (∑ i ∈ s,
        ((a i * B) * Real.log ((a i * B) / (b i * A)) - a i * B + b i * A)) =
        B * ((∑ i ∈ s, a i * Real.log (a i / b i)) - A * Real.log (A / B)) := by
    calc
      _ = ∑ i ∈ s,
          (B * (a i * Real.log (a i / b i) - a i * Real.log (A / B)) -
            a i * B + b i * A) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i hi
      _ = B * ((∑ i ∈ s, a i * Real.log (a i / b i)) - A * Real.log (A / B)) := by
        calc
          _ = ∑ i ∈ s,
              (B * (a i * Real.log (a i / b i)) -
                B * a i * Real.log (A / B) - B * a i + A * b i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = B * ((∑ i ∈ s, a i * Real.log (a i / b i)) -
              A * Real.log (A / B)) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib]
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
            dsimp [A, B]
            ring
  rw [heq] at hsum
  have hdiff :
      0 ≤ (∑ i ∈ s, a i * Real.log (a i / b i)) - A * Real.log (A / B) :=
    (mul_nonneg_iff_of_pos_left hB').mp hsum
  simpa [A, B] using hdiff

/-! ## Binary Pinsker -/

/-- Binary entropy gap: binary KL in Bregman form minus `2 * (p - q)^2`. -/
noncomputable def binaryPinskerGap (p q : ℝ) : ℝ :=
  entropyScalar p + entropyScalar (1 - p) -
    entropyScalar q - entropyScalar (1 - q) -
    (Real.log q - Real.log (1 - q)) * (p - q) - 2 * (p - q) ^ 2

/-- First derivative of `binaryPinskerGap` in its first argument. -/
noncomputable def binaryPinskerGapDeriv (p q : ℝ) : ℝ :=
  Real.log p - Real.log (1 - p) -
    (Real.log q - Real.log (1 - q)) - 4 * (p - q)

/-- Second derivative of the binary Pinsker gap in its first argument. -/
noncomputable def binaryPinskerGapDeriv2 (p : ℝ) : ℝ :=
  1 / p + 1 / (1 - p) - 4

/-- Explicit first derivative calculation for the binary Pinsker gap. -/
theorem hasDerivAt_binaryPinskerGap
    (p q : ℝ) (hp : p ≠ 0) (hp1 : 1 - p ≠ 0) :
    HasDerivAt (fun x => binaryPinskerGap x q) (binaryPinskerGapDeriv p q) p := by
  have hfirst : HasDerivAt entropyScalar (Real.log p + 1) p := by
    change HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log p + 1) p
    exact Real.hasDerivAt_mul_log hp
  have hsecond : HasDerivAt (fun x => entropyScalar (1 - x))
      (-(Real.log (1 - p) + 1)) p := by
    change HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      (-(Real.log (1 - p) + 1)) p
    have hcomp := (Real.hasDerivAt_mul_log hp1).comp p
      ((hasDerivAt_id p).const_sub 1)
    have hcomp' : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
        ((Real.log (1 - p) + 1) * (-1)) p := by
      convert hcomp using 1 <;> rfl
    exact hcomp'.congr_deriv (by ring)
  have hlinear : HasDerivAt
      (fun x : ℝ => (Real.log q - Real.log (1 - q)) * (x - q))
      (Real.log q - Real.log (1 - q)) p := by
    simpa using ((hasDerivAt_id p).sub_const q).const_mul
      (Real.log q - Real.log (1 - q))
  have hquad : HasDerivAt (fun x : ℝ => 2 * (x - q) ^ 2) (4 * (p - q)) p := by
    have hpow := (((hasDerivAt_id p).sub_const q).pow 2).const_mul 2
    convert hpow using 1 <;> try rfl
    norm_num
    ring
  have hcombo := (((hfirst.add hsecond).sub_const (entropyScalar q)).sub_const
    (entropyScalar (1 - q))).sub hlinear |>.sub hquad
  have hcombo' : HasDerivAt (fun x => binaryPinskerGap x q)
      (Real.log p + 1 + -(Real.log (1 - p) + 1) -
        (Real.log q - Real.log (1 - q)) - 4 * (p - q)) p := by
    convert hcombo using 1 <;> rfl
  exact hcombo'.congr_deriv (by dsimp [binaryPinskerGapDeriv]; ring)

/-- Explicit second derivative calculation for the binary Pinsker gap. -/
theorem hasDerivAt_binaryPinskerGapDeriv
    (p q : ℝ) (hp : p ≠ 0) (hp1 : 1 - p ≠ 0) :
    HasDerivAt (fun x => binaryPinskerGapDeriv x q) (binaryPinskerGapDeriv2 p) p := by
  have hlogp := Real.hasDerivAt_log hp
  have hlogone : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 - p)⁻¹) p := by
    have hcomp := (Real.hasDerivAt_log hp1).comp p ((hasDerivAt_id p).const_sub 1)
    have hcomp' : HasDerivAt (fun x : ℝ => Real.log (1 - x))
        ((1 - p)⁻¹ * (-1)) p := by
      convert hcomp using 1 <;> rfl
    exact hcomp'.congr_deriv (by ring)
  have hlinear : HasDerivAt (fun x : ℝ => 4 * (x - q)) 4 p := by
    simpa using ((hasDerivAt_id p).sub_const q).const_mul 4
  have hcombo := ((hlogp.sub hlogone).sub_const
    (Real.log q - Real.log (1 - q))).sub hlinear
  have hcombo' : HasDerivAt (fun x => binaryPinskerGapDeriv x q)
      (p⁻¹ - -(1 - p)⁻¹ - 4) p := by
    convert hcombo using 1 <;> rfl
  exact hcombo'.congr_deriv (by
    dsimp [binaryPinskerGapDeriv2]
    simp only [div_eq_mul_inv]
    ring)

/-- The binary Pinsker gap is continuous, including at the endpoints. -/
theorem continuous_binaryPinskerGap (q : ℝ) :
    Continuous (fun p => binaryPinskerGap p q) := by
  have hentropy : Continuous entropyScalar := by
    change Continuous (fun x : ℝ => x * Real.log x)
    exact Real.continuous_mul_log
  unfold binaryPinskerGap
  fun_prop

/-- The second derivative of the binary Pinsker gap is nonnegative on `(0,1)`. -/
theorem binaryPinskerGapDeriv2_nonneg
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ binaryPinskerGapDeriv2 p := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hone : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  have hid : 1 / p + 1 / (1 - p) - 4 = (2 * p - 1) ^ 2 / (p * (1 - p)) := by
    field_simp [hpne, hone]
    ring
  rw [binaryPinskerGapDeriv2, hid]
  positivity

/-- Convexity of the binary Pinsker gap on the closed unit interval. -/
theorem binaryPinskerGap_convexOn (q : ℝ) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun p => binaryPinskerGap p q) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
  · exact (continuous_binaryPinskerGap q).continuousOn
  · intro p hp
    have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hp
    exact (hasDerivAt_binaryPinskerGap p q (ne_of_gt hp'.1)
      (ne_of_gt (sub_pos.mpr hp'.2))).hasDerivWithinAt
  · intro p hp
    have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hp
    exact (hasDerivAt_binaryPinskerGapDeriv p q (ne_of_gt hp'.1)
      (ne_of_gt (sub_pos.mpr hp'.2))).hasDerivWithinAt
  · intro p hp
    have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hp
    exact binaryPinskerGapDeriv2_nonneg hp'.1 hp'.2

/-- Nonnegativity of the binary Pinsker gap, obtained from convexity and its zero derivative
at the base point. -/
theorem binaryPinskerGap_nonneg
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ binaryPinskerGap p q := by
  have hconv := binaryPinskerGap_convexOn q
  have hpMem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp0.le, hp1.le⟩
  have hqMem : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq0.le, hq1.le⟩
  have hderq : HasDerivAt (fun x => binaryPinskerGap x q) 0 q := by
    have hbase := hasDerivAt_binaryPinskerGap q q (ne_of_gt hq0)
      (ne_of_gt (sub_pos.mpr hq1))
    exact hbase.congr_deriv (by simp [binaryPinskerGapDeriv])
  have hgapq : binaryPinskerGap q q = 0 := by simp [binaryPinskerGap]
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · have hslope := hconv.slope_le_of_hasDerivAt hpMem hqMem hpq hderq
    rw [slope_def_field] at hslope
    have hden : 0 < q - p := sub_pos.mpr hpq
    have hnum : binaryPinskerGap q q - binaryPinskerGap p q ≤ 0 := by
      rcases (div_nonpos_iff.mp hslope) with hbad | hgood
      · exact False.elim ((not_le_of_gt hden) hbad.2)
      · exact hgood.1
    rw [hgapq] at hnum
    linarith
  · simp [hpq, hgapq]
  · have hslope := hconv.le_slope_of_hasDerivAt hqMem hpMem hqp hderq
    rw [slope_def_field] at hslope
    have hden : 0 < p - q := sub_pos.mpr hqp
    have hnum : 0 ≤ binaryPinskerGap p q - binaryPinskerGap q q := by
      rcases (div_nonneg_iff.mp hslope) with hgood | hbad
      · exact hgood.1
      · exact False.elim ((not_le_of_gt hden) hbad.2)
    rw [hgapq] at hnum
    simpa using hnum

/-- Natural-logarithm binary relative entropy. -/
noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Binary KL is the entropy Bregman form used in `binaryPinskerGap`. -/
theorem binaryKL_eq_entropyBregmanForm
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKL p q =
      entropyScalar p + entropyScalar (1 - p) -
        entropyScalar q - entropyScalar (1 - q) -
        (Real.log q - Real.log (1 - q)) * (p - q) := by
  rw [binaryKL, Real.log_div (ne_of_gt hp0) (ne_of_gt hq0),
    Real.log_div (ne_of_gt (sub_pos.mpr hp1)) (ne_of_gt (sub_pos.mpr hq1))]
  simp only [entropyScalar]
  ring

/-- Exact binary Pinsker inequality with natural logarithms. -/
theorem binaryPinsker
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ binaryKL p q := by
  have hgap := binaryPinskerGap_nonneg hp0 hp1 hq0 hq1
  rw [binaryPinskerGap, ← binaryKL_eq_entropyBregmanForm hp0 hp1 hq0 hq1] at hgap
  linarith

/-- Finite KL is nonnegative when the numerator is a simplex vector and the denominator is
strictly positive with coordinate sum one. -/
theorem finiteKL_nonneg
    {m : ℕ} (p q : Fin m → ℝ)
    (hp : IsSimplex p) (hq : IsSimplex q)
    (hqPos : HasStrictlyPositiveCoordinates q) :
    0 ≤ finiteKL p q := by
  have hsum : 0 ≤ ∑ i, (p i * Real.log (p i / q i) - p i + q i) :=
    Finset.sum_nonneg (fun i _ => scalarKL_nonneg (hp.1 i) (hqPos i))
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.2, hq.2] at hsum
  simpa [finiteKL] using hsum

/-- Exact finite Pinsker inequality for strictly positive finite simplex vectors. The project
distance is the unnormalized `sum_i |p_i - q_i|`, hence the coefficient is exactly `1/2`. -/
theorem finitePinsker
    {m : ℕ} (p q : Fin m → ℝ) (_hm : 0 < m)
    (hp : IsSimplex p) (hq : IsSimplex q)
    (hpPos : HasStrictlyPositiveCoordinates p)
    (hqPos : HasStrictlyPositiveCoordinates q) :
    l1Dist p q ^ 2 / 2 ≤ entropyBregman p q := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i => q i < p i)
  let T : Finset (Fin m) := Finset.univ.filter (fun i => ¬ q i < p i)
  let P : ℝ := ∑ i ∈ S, p i
  let Q : ℝ := ∑ i ∈ S, q i
  have hpartition (f : Fin m → ℝ) :
      (∑ i ∈ S, f i) + (∑ i ∈ T, f i) = ∑ i, f i := by
    simpa [S, T] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i < p i) f)
  have hpParts : P + (∑ i ∈ T, p i) = 1 := by
    simpa [P, hp.2] using hpartition p
  have hqParts : Q + (∑ i ∈ T, q i) = 1 := by
    simpa [Q, hq.2] using hpartition q
  have hPQ_nonneg : 0 ≤ P - Q := by
    change 0 ≤ (∑ i ∈ S, p i) - ∑ i ∈ S, q i
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun i hi => by
      have hi' : q i < p i := by simpa [S] using hi
      linarith)
  have hL1 : l1Dist p q = 2 * (P - Q) := by
    have habsParts := hpartition (fun i => |p i - q i|)
    rw [l1Dist, l1Size]
    calc
      (∑ i, |primalDisplacement p q i|) =
          (∑ i ∈ S, |p i - q i|) + (∑ i ∈ T, |p i - q i|) := by
        simpa [primalDisplacement] using habsParts.symm
      _ = (∑ i ∈ S, (p i - q i)) + (∑ i ∈ T, (q i - p i)) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          have hi' : q i < p i := by simpa [S] using hi
          rw [abs_of_nonneg (sub_nonneg.mpr hi'.le)]
        · apply Finset.sum_congr rfl
          intro i hi
          have hi' : p i ≤ q i := by simpa [T] using hi
          rw [abs_of_nonpos (sub_nonpos.mpr hi')]
          ring
      _ = 2 * (P - Q) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        change ((∑ i ∈ S, p i) - ∑ i ∈ S, q i) +
            ((∑ i ∈ T, q i) - ∑ i ∈ T, p i) =
          2 * ((∑ i ∈ S, p i) - ∑ i ∈ S, q i)
        linarith
  have hKLPinsker : l1Dist p q ^ 2 / 2 ≤ finiteKL p q := by
    by_cases hPQzero : P - Q = 0
    · have hKL := finiteKL_nonneg p q hp hq hqPos
      rw [hL1, hPQzero]
      simpa using hKL
    · have hPQpos : 0 < P - Q := lt_of_le_of_ne hPQ_nonneg (Ne.symm hPQzero)
      have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
        intro hS
        simp [P, Q, hS] at hPQpos)
      have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
        intro hT
        rw [hT] at hpParts hqParts
        simp at hpParts hqParts
        linarith)
      have hPpos : 0 < P := by
        dsimp only [P]
        exact Finset.sum_pos (fun i _ => hpPos i) hSne
      have hQpos : 0 < Q := by
        dsimp only [Q]
        exact Finset.sum_pos (fun i _ => hqPos i) hSne
      have hpTpos : 0 < ∑ i ∈ T, p i :=
        Finset.sum_pos (fun i _ => hpPos i) hTne
      have hqTpos : 0 < ∑ i ∈ T, q i :=
        Finset.sum_pos (fun i _ => hqPos i) hTne
      have hPone : P < 1 := by linarith
      have hQone : Q < 1 := by linarith
      have hlogS := finite_log_sum S p q
        (fun i _ => hp.1 i) (fun i _ => hqPos i) hPpos hQpos
      have hlogT := finite_log_sum T p q
        (fun i _ => hp.1 i) (fun i _ => hqPos i) hpTpos hqTpos
      have hpT : (∑ i ∈ T, p i) = 1 - P := by linarith
      have hqT : (∑ i ∈ T, q i) = 1 - Q := by linarith
      rw [hpT, hqT] at hlogT
      have hKLParts := hpartition (fun i => p i * Real.log (p i / q i))
      have hbinaryLe : binaryKL P Q ≤ finiteKL p q := by
        rw [binaryKL, finiteKL]
        linarith
      have hbinary := binaryPinsker hPpos hPone hQpos hQone
      rw [hL1]
      nlinarith
  rwa [entropyBregman_eq_finiteKL p q hp hq hpPos hqPos]

/-- Exact Pinsker instance for the actual exponentiated-gradient pair. The external comparator
does not occur here. -/
theorem egUpdate_finitePinsker
    {m : ℕ} (w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hw : IsSimplex w)
    (hwPos : HasStrictlyPositiveCoordinates w) :
    l1Dist (egUpdate w g eta) w ^ 2 / 2 ≤
      entropyBregman (egUpdate w g eta) w := by
  exact finitePinsker (egUpdate w g eta) w hm
    (egUpdate_isSimplex w g eta hm hw hwPos) hw
    (egUpdate_pos w g eta hm hwPos) hwPos

/-- EG mirror remainder bound with finite Pinsker discharged. -/
theorem eg_mirror_remainder_bound
    {m : ℕ} (w g : Fin m → ℝ) (eta G : ℝ)
    (hm : 0 < m) (hw : IsSimplex w)
    (hwPos : HasStrictlyPositiveCoordinates w)
    (heta : 0 ≤ eta) (hG : 0 ≤ G)
    (hg : HasCoordinateAbsBound g G) :
    -entropyBregman (egUpdate w g eta) w +
        eta * vectorDot g (primalDisplacement (egUpdate w g eta) w) ≤
      eta ^ 2 * G ^ 2 / 2 := by
  exact eg_mirror_remainder_bound_of_pinsker w g eta G heta hG hg
    (egUpdate_finitePinsker w g eta hm hw hwPos)

/-- Final deterministic EG mirror one-step inequality, with no Pinsker hypothesis and without
strict positivity of the comparator. -/
theorem eg_mirror_one_step
    {m : ℕ} (u w g : Fin m → ℝ) (eta G : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwPos : HasStrictlyPositiveCoordinates w)
    (heta : 0 ≤ eta) (hG : 0 ≤ G)
    (hg : HasCoordinateAbsBound g G) :
    eta * vectorDot g (primalDisplacement u w) ≤
      entropyBregman u w - entropyBregman u (egUpdate w g eta) +
        eta ^ 2 * G ^ 2 / 2 := by
  exact eg_mirror_one_step_of_pinsker u w g eta G hm hu hw hwPos heta hG hg
    (egUpdate_finitePinsker w g eta hm hw hwPos)

/-- Exact `hmirror` interface with the already-squared identification `dualGradSq = G ^ 2`.
It is directly suitable for `dual_one_step_substitution`, `expandedUnpenalized_dual_one_step`,
and `expandedPenalized_dual_one_step`. -/
theorem eg_mirror_hmirror
    {m : ℕ} (u w g : Fin m → ℝ) (eta G : ℝ)
    (hm : 0 < m) (hu : IsSimplex u) (hw : IsSimplex w)
    (hwPos : HasStrictlyPositiveCoordinates w)
    (heta : 0 ≤ eta) (hG : 0 ≤ G)
    (hg : HasCoordinateAbsBound g G) :
    eta * vectorDot g (primalDisplacement u w) ≤
      entropyBregman u w - entropyBregman u (egUpdate w g eta) +
        eta ^ 2 / 2 * (G ^ 2) := by
  exact eg_mirror_hmirror_interface u w g eta G hm hu hw hwPos heta hG hg
    (egUpdate_finitePinsker w g eta hm hw hwPos)

/-- Terminal-potential bridge for an arbitrary simplex comparator, including boundary points.
The updated base is strictly positive, so the coordinatewise tangent theorem supplies the
nonnegativity premise used by `dual_cumulative_regret`. -/
theorem eg_terminal_entropyBregman_nonneg
    {m : ℕ} (u w g : Fin m → ℝ) (eta : ℝ)
    (hm : 0 < m) (hu : IsSimplex u)
    (hwPos : HasStrictlyPositiveCoordinates w) :
    0 ≤ entropyBregman u (egUpdate w g eta) := by
  exact entropyBregman_nonneg_of_isSimplex_of_pos u (egUpdate w g eta) hu
    (egUpdate_pos w g eta hm hwPos)

end NegDRO
