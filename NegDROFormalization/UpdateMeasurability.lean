import NegDROFormalization.ExponentiatedGradient
import NegDROFormalization.PrimalProjectionRecursion

/-!
# Measurability of finite-dimensional primal and EG updates

The geometric properties of the projection and simplex are deliberately separate from this
module. Measurability of the supplied projection map is an explicit interface.
-/

set_option autoImplicit false

open MeasureTheory

namespace NegDRO

/-- A finite real vector-valued map is measurable when every coordinate is measurable. -/
theorem measurable_finVector_of_coordinatewise
    {Omega : Type*} {m : MeasurableSpace Omega} {n : ℕ}
    {f : Omega → Fin n → ℝ}
    (hf : ∀ i, Measurable[m] (fun omega => f omega i)) :
    Measurable[m] f :=
  measurable_pi_iff.mpr hf

/-- Coordinate projection of a measurable finite real vector-valued map. -/
theorem measurable_coordinate_of_finVector
    {Omega : Type*} {m : MeasurableSpace Omega} {n : ℕ}
    {f : Omega → Fin n → ℝ} (hf : Measurable[m] f) (i : Fin n) :
    Measurable[m] (fun omega => f omega i) :=
  hf.eval

/-- A measurable finite-vector map has a.e. strongly measurable real coordinates for every
measure on the same source measurable space. -/
theorem aestronglyMeasurable_coordinate_of_measurable_finVector
    {Omega : Type*} {m mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} {n : ℕ}
    {f : Omega → Fin n → ℝ} (hf : Measurable[m] f) (i : Fin n) :
    AEStronglyMeasurable[m] (fun omega => f omega i) mu :=
  (measurable_coordinate_of_finVector hf i).aestronglyMeasurable (μ := mu)

/-- Joint measurability of `(b,g) ↦ b - eta * g` for a fixed real step size. -/
theorem measurable_gradientStep_joint
    {p : ℕ} (eta : ℝ) :
    Measurable (fun z : (Fin p → ℝ) × (Fin p → ℝ) =>
      gradientStep z.1 eta z.2) := by
  apply measurable_finVector_of_coordinatewise
  intro i
  exact (measurable_fst.eval.sub
    (measurable_const.mul measurable_snd.eval))

/-- Measurability of a random unprojected gradient step from measurable vector inputs. -/
theorem measurable_gradientStep_comp
    {Omega : Type*} {m : MeasurableSpace Omega} {p : ℕ}
    (eta : ℝ) {b g : Omega → Fin p → ℝ}
    (hb : Measurable[m] b) (hg : Measurable[m] g) :
    Measurable[m] (fun omega => gradientStep (b omega) eta (g omega)) := by
  exact (measurable_gradientStep_joint eta).comp (hb.prodMk hg)

/-- Joint measurability of the projected gradient update under the explicit interface
`Measurable P`. Projection geometry alone does not imply this premise. -/
theorem measurable_projectedGradientStep_joint
    {p : ℕ} (P : (Fin p → ℝ) → Fin p → ℝ) (eta : ℝ)
    (hPMeas : Measurable P) :
    Measurable (fun z : (Fin p → ℝ) × (Fin p → ℝ) =>
      projectedGradientStep P z.1 eta z.2) := by
  exact hPMeas.comp (measurable_gradientStep_joint eta)

/-- Measurability of a random projected gradient update from measurable vector inputs. -/
theorem measurable_projectedGradientStep_comp
    {Omega : Type*} {m : MeasurableSpace Omega} {p : ℕ}
    (P : (Fin p → ℝ) → Fin p → ℝ) (eta : ℝ)
    {b g : Omega → Fin p → ℝ} (hPMeas : Measurable P)
    (hb : Measurable[m] b) (hg : Measurable[m] g) :
    Measurable[m] (fun omega =>
      projectedGradientStep P (b omega) eta (g omega)) := by
  exact (measurable_projectedGradientStep_joint P eta hPMeas).comp
    (hb.prodMk hg)

/-- Joint measurability of the actual finite EG normalizer. No positivity premise is needed. -/
theorem measurable_egNormalizer_joint
    {n : ℕ} (eta : ℝ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      egNormalizer z.1 z.2 eta) := by
  simp only [egNormalizer]
  apply Finset.measurable_sum
  intro i _hi
  exact measurable_fst.eval.mul
    (measurable_const.mul measurable_snd.eval).exp

/-- Measurability of the EG normalizer evaluated on measurable random vector inputs. -/
theorem measurable_egNormalizer_comp
    {Omega : Type*} {m : MeasurableSpace Omega} {n : ℕ}
    (eta : ℝ) {w g : Omega → Fin n → ℝ}
    (hw : Measurable[m] w) (hg : Measurable[m] g) :
    Measurable[m] (fun omega => egNormalizer (w omega) (g omega) eta) := by
  exact (measurable_egNormalizer_joint eta).comp (hw.prodMk hg)

/-- Joint measurability of the actual normalized EG update. Real division is total, so this
analytic statement does not need normalizer positivity or simplex hypotheses. -/
theorem measurable_egUpdate_joint
    {n : ℕ} (eta : ℝ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      egUpdate z.1 z.2 eta) := by
  apply measurable_finVector_of_coordinatewise
  intro i
  exact (measurable_fst.eval.mul
    (measurable_const.mul measurable_snd.eval).exp).div
      (measurable_egNormalizer_joint eta)

/-- Measurability of the EG update evaluated on measurable random vector inputs. -/
theorem measurable_egUpdate_comp
    {Omega : Type*} {m : MeasurableSpace Omega} {n : ℕ}
    (eta : ℝ) {w g : Omega → Fin n → ℝ}
    (hw : Measurable[m] w) (hg : Measurable[m] g) :
    Measurable[m] (fun omega => egUpdate (w omega) (g omega) eta) := by
  exact (measurable_egUpdate_joint eta).comp (hw.prodMk hg)

end NegDRO
