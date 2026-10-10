import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual beta-measure moments

The real beta density is nonnegative and supported in the open unit
interval. Multiplying it by a natural power shifts its first shape
parameter. The actual Bochner moment is the ratio of beta constants.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CircularLaw

theorem beta_density_real_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hβ).le
  · simp only [betaPDFReal, if_neg hx, le_refl]

theorem beta_density_measurable (α β : ℝ) : Measurable (betaPDF α β) :=
  ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β)

theorem beta_density_toReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (betaPDF α β x).toReal = betaPDFReal α β x :=
  ENNReal.toReal_ofReal (beta_density_real_nonneg hα hβ x)

theorem beta_measure_ae_unit_interval (α β : ℝ) :
    ∀ᵐ x ∂betaMeasure α β, 0 < x ∧ x < 1 := by
  rw [betaMeasure, ae_withDensity_iff (beta_density_measurable α β)]
  apply Filter.Eventually.of_forall
  intro x hx
  by_contra h
  exact hx (by simp only [betaPDF, betaPDFReal, if_neg h, ENNReal.ofReal_zero])

theorem beta_density_real_integral_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x, betaPDFReal α β x) = 1 := by
  letI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (beta_density_measurable α β)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) (fun _ : ℝ => (1 : ℝ))
  change (∫ _x : ℝ, (1 : ℝ) ∂betaMeasure α β) =
    ∫ x, (betaPDF α β x).toReal • (1 : ℝ) at h
  simp only [smul_eq_mul, beta_density_toReal hα hβ, mul_one] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h.symm

theorem beta_density_power_shift {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (x : ℝ) :
    betaPDFReal α β x * x ^ k =
      (beta (α + k) β / beta α β) * betaPDFReal (α + k) β x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hShift : 0 < α + (k : ℝ) := by positivity
    have hPow : x ^ (α + (k : ℝ) - 1) = x ^ (α - 1) * x ^ k := by
      rw [show α + (k : ℝ) - 1 = (α - 1) + (k : ℝ) by ring,
        Real.rpow_add hx.1, Real.rpow_natCast]
    simp only [betaPDFReal, if_pos hx]
    rw [hPow]
    field_simp [ne_of_gt (beta_pos hα hβ), ne_of_gt (beta_pos hShift hβ)]
  · simp only [betaPDFReal, if_neg hx, zero_mul, mul_zero]

theorem beta_measure_power_integral {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    (∫ x, x ^ k ∂betaMeasure α β) = beta (α + k) β / beta α β := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul
    (beta_density_measurable α β)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, beta_density_toReal hα hβ, beta_density_power_shift hα hβ]
  rw [integral_const_mul, beta_density_real_integral_one (by positivity) hβ, mul_one]

theorem beta_measure_power_integrable {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (betaMeasure α β) := by
  letI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [beta_measure_ae_unit_interval α β] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.le k)]
  exact pow_le_one₀ hx.1.le hx.2.le

end CircularLaw
