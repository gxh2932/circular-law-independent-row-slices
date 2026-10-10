import CircularLaw.TruncatedCosineBound
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Weighted Jensen for the concentration argument

Tilting a finite measure by a nonnegative integrable weight and its actual
integral gives a probability law. Jensen applied to that law yields the
exponential bound used to average normalized cosine kernels. Zero weights
are handled explicitly, with no division-by-zero assumption.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CircularLaw

def momentTiltLaw (ν : Measure ℂ) (w : ℂ → ℝ) : Measure ℂ :=
  ν.withDensity (fun x => ENNReal.ofReal (w x / (∫ y, w y ∂ν)))

theorem momentTiltLaw_probability (ν : Measure ℂ) {w : ℂ → ℝ}
    (hwInt : Integrable w ν) (hwNonneg : ∀ x, 0 ≤ w x)
    (hA : 0 < ∫ x, w x ∂ν) : IsProbabilityMeasure (momentTiltLaw ν w) := by
  constructor
  rw [momentTiltLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hwInt.div_const _)
      (ae_of_all _ (fun x => div_nonneg (hwNonneg x) hA.le)), integral_div,
    div_self hA.ne', ENNReal.ofReal_one]

theorem momentTiltLaw_integral (ν : Measure ℂ) {w : ℂ → ℝ}
    (hw : Measurable w) (hwNonneg : ∀ x, 0 ≤ w x) (hA : 0 < ∫ x, w x ∂ν)
    (f : ℂ → ℝ) :
    (∫ x, f x ∂momentTiltLaw ν w) =
      (∫ x, (w x / (∫ y, w y ∂ν)) * f x ∂ν) := by
  rw [momentTiltLaw, integral_withDensity_eq_integral_toReal_smul
    (hw.div_const _).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hwNonneg _) hA.le), smul_eq_mul]

theorem normalized_weight_mul_quotient {A w h : ℝ} (hA : A ≠ 0)
    (hZero : w = 0 → h = 0) : (w / A) * (-A * h / (2 * w)) = -h / 2 := by
  by_cases hw : w = 0
  · simp only [hw, hZero hw, mul_zero, zero_div, neg_zero]
  · field_simp

theorem weighted_exponential_jensen (ν : Measure ℂ) {w h : ℂ → ℝ}
    (hw : Measurable w) (hwInt : Integrable w ν) (hwNonneg : ∀ x, 0 ≤ w x)
    (hh : Measurable h) (hhInt : Integrable h ν) (hhNonneg : ∀ x, 0 ≤ h x)
    (hZero : ∀ x, w x = 0 → h x = 0) (hA : 0 < ∫ x, w x ∂ν) :
    Real.exp (-(∫ x, h x ∂ν) / 2) ≤
      (∫ x, (w x / (∫ y, w y ∂ν)) *
        Real.exp (-(∫ y, w y ∂ν) * h x / (2 * w x)) ∂ν) := by
  let A := ∫ x, w x ∂ν
  let f : ℂ → ℝ := fun x => -A * h x / (2 * w x)
  letI := momentTiltLaw_probability ν hwInt hwNonneg hA
  have hCancel (x : ℂ) : (w x / A) * f x = -h x / 2 :=
    normalized_weight_mul_quotient hA.ne' (hZero x)
  have hfInt : Integrable f (momentTiltLaw ν w) := by
    rw [momentTiltLaw, integrable_withDensity_iff_integrable_smul'
      (hw.div_const _).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (div_nonneg (hwNonneg _) hA.le), smul_eq_mul]
    change Integrable (fun x => (w x / A) * f x) ν
    simp_rw [hCancel]
    exact hhInt.neg.div_const 2
  have hfNonpos (x : ℂ) : f x ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA.le) (hhNonneg x))
      (mul_nonneg (by norm_num) (hwNonneg x))
  have hExpInt : Integrable (Real.exp ∘ f) (momentTiltLaw ν w) := by
    have hfMeas : Measurable f := (measurable_const.mul hh).div (measurable_const.mul hw)
    apply integrable_of_abs_bound _ (Real.measurable_exp.comp hfMeas)
      (C := 1)
    intro x
    change |Real.exp (f x)| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (hfNonpos x)
  have hJensen := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all _ (fun _ => Set.mem_univ _)) hfInt hExpInt
  rw [momentTiltLaw_integral ν hw hwNonneg hA, momentTiltLaw_integral ν hw hwNonneg hA] at hJensen
  change Real.exp (∫ x, (w x / A) * f x ∂ν) ≤
    (∫ x, (w x / A) * Real.exp (f x) ∂ν) at hJensen
  simp_rw [hCancel] at hJensen
  rw [integral_div, integral_neg] at hJensen
  exact hJensen

end CircularLaw
