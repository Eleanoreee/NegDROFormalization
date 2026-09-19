import NegDROFormalization.PrimalTrajectory
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology

/-!
# Actual Euclidean projection onto a nonempty closed convex coordinate set

The project coordinate type `Fin p → ℝ` carries a default supremum norm, so projection is not
constructed there.  We transport coordinates through `WithLp.toLp 2` into
`EuclideanSpace ℝ (Fin p)`, use Mathlib's Hilbert projection existence theorem
`exists_norm_eq_iInf_of_complete_convex`, and transport the unique minimizer back.

The nearest point is selected with `Classical.choose`; uniqueness follows from the variational
characterization `norm_eq_iInf_iff_real_inner_le_zero`.  The same characterization yields Fejér
monotonicity and nonexpansiveness, hence continuity and measurability.
-/

set_option autoImplicit false

open Real InnerProductSpace

namespace NegDRO

/-- Continuous linear coordinate representation in Euclidean `L²` geometry.  This is not an
isometry from the coordinate type's default supremum norm. -/
def coordinateToEuclidean {p : ℕ} :
    (Fin p → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin p) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p ↦ ℝ)).symm

/-- Inverse coordinate representation. -/
def coordinateFromEuclidean {p : ℕ} :
    EuclideanSpace ℝ (Fin p) ≃L[ℝ] (Fin p → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p ↦ ℝ)

@[simp] theorem coordinateFromEuclidean_toEuclidean
    {p : ℕ} (x : Fin p → ℝ) :
    coordinateFromEuclidean (coordinateToEuclidean x) = x := by
  rfl

@[simp] theorem coordinateToEuclidean_fromEuclidean
    {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) :
    coordinateToEuclidean (coordinateFromEuclidean x) = x := by
  rfl

/-- The Euclidean inner product is the project's explicit coordinate dot product. -/
theorem real_inner_toEuclidean
    {p : ℕ} (x y : Fin p → ℝ) :
    inner ℝ (coordinateToEuclidean x) (coordinateToEuclidean y) = vectorDot x y := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [coordinateToEuclidean, PiLp.continuousLinearEquiv_symm_apply,
    RCLike.star_def, vectorDot, dotProduct]
  exact Finset.sum_congr rfl (fun i _hi ↦ mul_comm _ _)

/-- Squared Euclidean norm equals the explicit finite sum `sqNorm`. -/
theorem norm_sq_toEuclidean
    {p : ℕ} (x : Fin p → ℝ) :
    ‖coordinateToEuclidean x‖ ^ 2 = sqNorm x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Squared Euclidean distance equals `sqDist`, including in dimension zero. -/
theorem dist_sq_toEuclidean
    {p : ℕ} (x y : Fin p → ℝ) :
    dist (coordinateToEuclidean x) (coordinateToEuclidean y) ^ 2 = sqDist x y := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [coordinateToEuclidean, PiLp.continuousLinearEquiv_symm_apply,
    Real.dist_eq, sqDist, sqNorm, sq_abs]

theorem sqNorm_fromEuclidean
    {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) :
    sqNorm (coordinateFromEuclidean x) = ‖x‖ ^ 2 := by
  rw [← norm_sq_toEuclidean (coordinateFromEuclidean x)]
  simp

theorem sqDist_fromEuclidean
    {p : ℕ} (x y : EuclideanSpace ℝ (Fin p)) :
    sqDist (coordinateFromEuclidean x) (coordinateFromEuclidean y) = dist x y ^ 2 := by
  rw [← dist_sq_toEuclidean (coordinateFromEuclidean x) (coordinateFromEuclidean y)]
  simp

theorem measurable_toEuclidean {p : ℕ} :
    Measurable (@coordinateToEuclidean p) :=
  coordinateToEuclidean.continuous.measurable

theorem measurable_fromEuclidean {p : ℕ} :
    Measurable (@coordinateFromEuclidean p) :=
  coordinateFromEuclidean.continuous.measurable

/-- The selected nearest point in a nonempty closed convex Euclidean set. -/
noncomputable def euclideanProjection
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K) :
    EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
  fun x ↦ Classical.choose
    (exists_norm_eq_iInf_of_complete_convex hKNonempty hKClosed.isComplete hKConvex x)

theorem euclideanProjection_mem
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x : EuclideanSpace ℝ (Fin p)) :
    euclideanProjection K hKNonempty hKClosed hKConvex x ∈ K :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hKNonempty hKClosed.isComplete hKConvex x)).1

theorem euclideanProjection_norm_eq_iInf
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x : EuclideanSpace ℝ (Fin p)) :
    ‖x - euclideanProjection K hKNonempty hKClosed hKConvex x‖ =
      ⨅ z : K, ‖x - z‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hKNonempty hKClosed.isComplete hKConvex x)).2

/-- The selected point minimizes distance against every feasible comparison point. -/
theorem euclideanProjection_norm_le
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x z : EuclideanSpace ℝ (Fin p)) (hz : z ∈ K) :
    ‖x - euclideanProjection K hKNonempty hKClosed hKConvex x‖ ≤ ‖x - z‖ := by
  rw [euclideanProjection_norm_eq_iInf K hKNonempty hKClosed hKConvex x]
  exact ciInf_le
    ⟨0, Set.forall_mem_range.mpr fun w : K ↦ norm_nonneg (x - w)⟩ ⟨z, hz⟩

/-- Variational characterization with the sign forced by `x - P` and `z - P`. -/
theorem euclideanProjection_variational
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x z : EuclideanSpace ℝ (Fin p)) (hz : z ∈ K) :
    inner ℝ (x - euclideanProjection K hKNonempty hKClosed hKConvex x)
      (z - euclideanProjection K hKNonempty hKClosed hKConvex x) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hKConvex
    (euclideanProjection_mem K hKNonempty hKClosed hKConvex x)).1
      (euclideanProjection_norm_eq_iInf K hKNonempty hKClosed hKConvex x) z hz

/-- Any feasible point attaining the same distance infimum is the selected projection.  Thus the
`Classical.choose` construction has canonical mathematical meaning. -/
theorem euclideanProjection_unique
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x v : EuclideanSpace ℝ (Fin p)) (hv : v ∈ K)
    (hvMin : ‖x - v‖ = ⨅ z : K, ‖x - z‖) :
    v = euclideanProjection K hKNonempty hKClosed hKConvex x := by
  let P := euclideanProjection K hKNonempty hKClosed hKConvex x
  have hPvar : inner ℝ (x - P) (v - P) ≤ 0 :=
    euclideanProjection_variational K hKNonempty hKClosed hKConvex x v hv
  have hvVar : inner ℝ (x - v) (P - v) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hKConvex hv).1 hvMin P
      (euclideanProjection_mem K hKNonempty hKClosed hKConvex x)
  have hPvar' : 0 ≤ inner ℝ (x - P) (P - v) := by
    rw [show v - P = -(P - v) by abel, inner_neg_right] at hPvar
    linarith
  have hxv : x - v = (x - P) + (P - v) := by abel
  rw [hxv, inner_add_left] at hvVar
  have hinner : inner ℝ (P - v) (P - v) ≤ 0 := by linarith
  have hnorm : ‖P - v‖ ^ 2 = inner ℝ (P - v) (P - v) := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℝ) (P - v))
  have hzero : ‖P - v‖ = 0 := by
    rw [← hnorm] at hinner
    nlinarith [norm_nonneg (P - v)]
  have : P = v := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact this.symm

/-- A feasible input is fixed by projection.  This also gives immediate whole-space and
closed-ball sanity checks whenever the input belongs to the relevant set. -/
theorem euclideanProjection_eq_self_of_mem
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x : EuclideanSpace ℝ (Fin p)) (hx : x ∈ K) :
    euclideanProjection K hKNonempty hKClosed hKConvex x = x := by
  have hle := euclideanProjection_norm_le K hKNonempty hKClosed hKConvex x x hx
  have hzero : ‖x - euclideanProjection K hKNonempty hKClosed hKConvex x‖ = 0 := by
    simpa using hle
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

/-- Sanity check: projection onto the whole Euclidean space is the identity. -/
@[simp] theorem euclideanProjection_univ
    {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) :
    euclideanProjection Set.univ Set.univ_nonempty isClosed_univ convex_univ x = x :=
  euclideanProjection_eq_self_of_mem Set.univ Set.univ_nonempty isClosed_univ convex_univ x
    (Set.mem_univ x)

/-- Sanity check: projection onto a singleton is its unique point. -/
@[simp] theorem euclideanProjection_singleton
    {p : ℕ} (c x : EuclideanSpace ℝ (Fin p)) :
    euclideanProjection {c} ⟨c, rfl⟩ isClosed_singleton (convex_singleton c) x = c := by
  simpa using
    (euclideanProjection_mem {c} ⟨c, rfl⟩ isClosed_singleton (convex_singleton c) x)

/-- Sanity check: a point already in a closed ball is fixed by projection onto that ball. -/
theorem euclideanProjection_closedBall_eq_self
    {p : ℕ} (c x : EuclideanSpace ℝ (Fin p)) (r : ℝ) (hr : 0 ≤ r)
    (hx : x ∈ Metric.closedBall c r) :
    euclideanProjection (Metric.closedBall c r) ⟨c, Metric.mem_closedBall_self hr⟩
      Metric.isClosed_closedBall (convex_closedBall c r) x = x :=
  euclideanProjection_eq_self_of_mem (Metric.closedBall c r)
    ⟨c, Metric.mem_closedBall_self hr⟩ Metric.isClosed_closedBall
    (convex_closedBall c r) x hx

/-- Strong Pythagorean/Fejér inequality. -/
theorem euclideanProjection_pythagorean
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x z : EuclideanSpace ℝ (Fin p)) (hz : z ∈ K) :
    ‖euclideanProjection K hKNonempty hKClosed hKConvex x - z‖ ^ 2 +
        ‖x - euclideanProjection K hKNonempty hKClosed hKConvex x‖ ^ 2 ≤
      ‖x - z‖ ^ 2 := by
  let P := euclideanProjection K hKNonempty hKClosed hKConvex x
  have hvar : inner ℝ (x - P) (z - P) ≤ 0 :=
    euclideanProjection_variational K hKNonempty hKClosed hKConvex x z hz
  have hinner : 0 ≤ inner ℝ (x - P) (P - z) := by
    rw [show P - z = -(z - P) by abel, inner_neg_right]
    linarith
  have hdecomp : x - z = (x - P) + (P - z) := by abel
  rw [hdecomp, norm_add_sq_real]
  rw [norm_sub_rev P z]
  linarith

theorem euclideanProjection_dist_le
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x z : EuclideanSpace ℝ (Fin p)) (hz : z ∈ K) :
    dist (euclideanProjection K hKNonempty hKClosed hKConvex x) z ≤ dist x z := by
  have hsquare :
      ‖euclideanProjection K hKNonempty hKClosed hKConvex x - z‖ ^ 2 ≤
        ‖x - z‖ ^ 2 :=
    le_trans (le_add_of_nonneg_right (sq_nonneg
      ‖x - euclideanProjection K hKNonempty hKClosed hKConvex x‖))
      (euclideanProjection_pythagorean K hKNonempty hKClosed hKConvex x z hz)
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg
    (euclideanProjection K hKNonempty hKClosed hKConvex x - z), norm_nonneg (x - z)]

/-- Firm nonexpansiveness in inner-product form. -/
theorem euclideanProjection_inner_le
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x y : EuclideanSpace ℝ (Fin p)) :
    ‖euclideanProjection K hKNonempty hKClosed hKConvex x -
        euclideanProjection K hKNonempty hKClosed hKConvex y‖ ^ 2 ≤
      inner ℝ
        (euclideanProjection K hKNonempty hKClosed hKConvex x -
          euclideanProjection K hKNonempty hKClosed hKConvex y) (x - y) := by
  let Px := euclideanProjection K hKNonempty hKClosed hKConvex x
  let Py := euclideanProjection K hKNonempty hKClosed hKConvex y
  have hx := euclideanProjection_variational K hKNonempty hKClosed hKConvex x Py
    (euclideanProjection_mem K hKNonempty hKClosed hKConvex y)
  have hy := euclideanProjection_variational K hKNonempty hKClosed hKConvex y Px
    (euclideanProjection_mem K hKNonempty hKClosed hKConvex x)
  change inner ℝ (x - Px) (Py - Px) ≤ 0 at hx
  change inner ℝ (y - Py) (Px - Py) ≤ 0 at hy
  have hx' : 0 ≤ inner ℝ (x - Px) (Px - Py) := by
    rw [show Py - Px = -(Px - Py) by abel, inner_neg_right] at hx
    linarith
  have hnonneg :
      0 ≤ inner ℝ ((x - Px) - (y - Py)) (Px - Py) := by
    rw [inner_sub_left]
    linarith
  have hrearrange : (x - Px) - (y - Py) = (x - y) - (Px - Py) := by abel
  rw [hrearrange, inner_sub_left] at hnonneg
  have hnorm : ‖Px - Py‖ ^ 2 = inner ℝ (Px - Py) (Px - Py) := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℝ) (Px - Py))
  have hcomm : inner ℝ (x - y) (Px - Py) = inner ℝ (Px - Py) (x - y) :=
    real_inner_comm _ _
  change ‖Px - Py‖ ^ 2 ≤ inner ℝ (Px - Py) (x - y)
  rw [hnorm]
  linarith

/-- Metric nonexpansiveness, with an explicit zero-distance branch. -/
theorem euclideanProjection_nonexpansive
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (x y : EuclideanSpace ℝ (Fin p)) :
    dist (euclideanProjection K hKNonempty hKClosed hKConvex x)
        (euclideanProjection K hKNonempty hKClosed hKConvex y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  let d := euclideanProjection K hKNonempty hKClosed hKConvex x -
    euclideanProjection K hKNonempty hKClosed hKConvex y
  have hfirm := euclideanProjection_inner_le K hKNonempty hKClosed hKConvex x y
  have hcs := real_inner_le_norm d (x - y)
  change ‖d‖ ^ 2 ≤ inner ℝ d (x - y) at hfirm
  change ‖d‖ ≤ ‖x - y‖
  by_cases hd : ‖d‖ = 0
  · simp [hd]
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hmul : ‖d‖ ^ 2 ≤ ‖d‖ * ‖x - y‖ := hfirm.trans hcs
    nlinarith

theorem euclideanProjection_lipschitz
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K) :
    LipschitzWith 1 (euclideanProjection K hKNonempty hKClosed hKConvex) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using euclideanProjection_nonexpansive K hKNonempty hKClosed hKConvex x y

theorem euclideanProjection_continuous
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K) :
    Continuous (euclideanProjection K hKNonempty hKClosed hKConvex) :=
  (euclideanProjection_lipschitz K hKNonempty hKClosed hKConvex).continuous

theorem euclideanProjection_measurable
    {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hKNonempty : K.Nonempty) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K) :
    Measurable (euclideanProjection K hKNonempty hKClosed hKConvex) :=
  (euclideanProjection_continuous K hKNonempty hKClosed hKConvex).measurable

/-- Image of a coordinate set in actual Euclidean geometry. -/
def euclideanImage {p : ℕ} (C : Set (Fin p → ℝ)) :
    Set (EuclideanSpace ℝ (Fin p)) := coordinateToEuclidean '' C

theorem euclideanImage_nonempty {p : ℕ} {C : Set (Fin p → ℝ)}
    (hC : C.Nonempty) : (euclideanImage C).Nonempty :=
  hC.image coordinateToEuclidean

theorem euclideanImage_isClosed {p : ℕ} {C : Set (Fin p → ℝ)}
    (hC : IsClosed C) : IsClosed (euclideanImage C) := by
  change IsClosed ((PiLp.homeomorph 2 (fun _ : Fin p ↦ ℝ)).symm '' C)
  exact ((PiLp.homeomorph 2 (fun _ : Fin p ↦ ℝ)).symm.isClosed_image).2 hC

theorem euclideanImage_convex {p : ℕ} {C : Set (Fin p → ℝ)}
    (hC : Convex ℝ C) : Convex ℝ (euclideanImage C) :=
  hC.linear_image coordinateToEuclidean.toLinearMap

/-- Actual nearest-point projection, transported back to project coordinates. -/
noncomputable def coordinateEuclideanProjection
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C) :
    (Fin p → ℝ) → (Fin p → ℝ) :=
  fun x ↦ coordinateFromEuclidean
    (euclideanProjection (euclideanImage C) (euclideanImage_nonempty hCNonempty)
      (euclideanImage_isClosed hCClosed) (euclideanImage_convex hCConvex)
      (coordinateToEuclidean x))

theorem coordinateEuclideanProjection_mem
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C)
    (x : Fin p → ℝ) :
    coordinateEuclideanProjection C hCNonempty hCClosed hCConvex x ∈ C := by
  have hm := euclideanProjection_mem (euclideanImage C) (euclideanImage_nonempty hCNonempty)
    (euclideanImage_isClosed hCClosed) (euclideanImage_convex hCConvex)
    (coordinateToEuclidean x)
  rcases hm with ⟨z, hz, heq⟩
  have : coordinateEuclideanProjection C hCNonempty hCClosed hCConvex x = z := by
    simp only [coordinateEuclideanProjection]
    rw [← heq]
    simp
  rwa [this]

theorem coordinateEuclideanProjection_pythagorean
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C)
    (x z : Fin p → ℝ) (hz : z ∈ C) :
    sqDist (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex x) z +
        sqDist x (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex x) ≤
      sqDist x z := by
  have hzE : coordinateToEuclidean z ∈ euclideanImage C := ⟨z, hz, rfl⟩
  have h := euclideanProjection_pythagorean (euclideanImage C)
    (euclideanImage_nonempty hCNonempty) (euclideanImage_isClosed hCClosed)
    (euclideanImage_convex hCConvex) (coordinateToEuclidean x)
    (coordinateToEuclidean z) hzE
  simpa only [coordinateEuclideanProjection, ← dist_sq_toEuclidean,
    coordinateToEuclidean_fromEuclidean, dist_eq_norm] using h

theorem coordinateEuclideanProjection_sqDist_le
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C)
    (x z : Fin p → ℝ) (hz : z ∈ C) :
    sqDist (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex x) z ≤
      sqDist x z :=
  le_trans (le_add_of_nonneg_right (by
      unfold sqDist sqNorm
      exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i -
        coordinateEuclideanProjection C hCNonempty hCClosed hCConvex x i)))
    (coordinateEuclideanProjection_pythagorean C hCNonempty hCClosed hCConvex x z hz)

theorem coordinateEuclideanProjection_measurable
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C) :
    Measurable (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex) := by
  exact measurable_fromEuclidean.comp
    ((euclideanProjection_measurable (euclideanImage C) (euclideanImage_nonempty hCNonempty)
      (euclideanImage_isClosed hCClosed) (euclideanImage_convex hCConvex)).comp
        measurable_toEuclidean)

theorem coordinateEuclideanProjection_mapsIntoFeasibleSet
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C) :
    MapsIntoFeasibleSet C (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex) :=
  fun x ↦ coordinateEuclideanProjection_mem C hCNonempty hCClosed hCConvex x

theorem coordinateEuclideanProjection_hasProjectionDistanceBound
    {p : ℕ} (C : Set (Fin p → ℝ))
    (hCNonempty : C.Nonempty) (hCClosed : IsClosed C) (hCConvex : Convex ℝ C) :
    HasProjectionDistanceBound C
      (coordinateEuclideanProjection C hCNonempty hCClosed hCConvex) :=
  fun x z hz ↦ coordinateEuclideanProjection_sqDist_le C hCNonempty hCClosed hCConvex x z hz

end NegDRO
