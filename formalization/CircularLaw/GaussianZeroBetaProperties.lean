import CircularLaw.GaussianZeroBetaIdentification

/-!
# Explicit integrals and sharp support of the actual zero-shift limit

The beta representation gives support below two and an actual density
integral for every strongly measurable test. Its logarithmic integral
reduces to the logarithmic moment of beta(1/2,3/2), with integrability
inherited from the checked Gaussian logarithmic-integrability theorem.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace CircularLaw

theorem continuous_zero_beta_sqrt_map :
    Continuous (fun x : ℝ => nonnegativeRealSquareRoot (4 * x)) := by
  change Continuous (nonnegativeRealSquareRoot ∘ (fun x : ℝ => 4 * x))
  exact continuous_nonnegative_real_square_root.comp (continuous_const.mul continuous_id)

theorem beta_nnreal_log_stronglyMeasurable :
    StronglyMeasurable (fun t : ℝ≥0 => Real.log (t : ℝ)) :=
  (Real.measurable_log.comp NNReal.continuous_coe.measurable).stronglyMeasurable

theorem beta_half_density_real (x : ℝ) :
    betaPDFReal (1 / 2) (3 / 2) x =
      if 0 < x ∧ x < 1 then
        (2 / Real.pi) * x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (1 / 2 : ℝ) else 0 := by
  simp only [betaPDFReal, beta_half_three_halves_constant,
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
    show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, one_div_div]

theorem gaussian_zero_shift_beta_test_integral (f : ℝ≥0 → ℝ) (hf : StronglyMeasurable f) :
    (∫ t, f t ∂gaussianShiftedSingularLimit 0) =
      ∫ x, betaPDFReal (1 / 2) (3 / 2) x * f (nonnegativeRealSquareRoot (4 * x)) := by
  rw [gaussian_zero_shift_limit_eq_sqrt_beta,
    integral_map_of_stronglyMeasurable
      continuous_zero_beta_sqrt_map.measurable hf,
    betaMeasure, integral_withDensity_eq_integral_toReal_smul
      (beta_density_measurable (1 / 2) (3 / 2))
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, beta_density_toReal (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 3 / 2)]

theorem gaussian_zero_shift_sharp_support :
    gaussianShiftedSingularLimit 0 {t : ℝ≥0 | (2 : ℝ) < (t : ℝ)} = 0 := by
  rw [gaussian_zero_shift_limit_eq_sqrt_beta, Measure.map_apply
    continuous_zero_beta_sqrt_map.measurable
    (measurableSet_lt measurable_const NNReal.continuous_coe.measurable)]
  have hBound : ∀ᵐ x ∂betaMeasure (1 / 2) (3 / 2), Real.sqrt (4 * x) ≤ 2 := by
    filter_upwards [beta_measure_ae_unit_interval (1 / 2) (3 / 2)] with x hx
    calc
      Real.sqrt (4 * x) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by norm_num
  have hNot : ∀ᵐ x ∂betaMeasure (1 / 2) (3 / 2), ¬ (2 < Real.sqrt (4 * x)) :=
    hBound.mono (fun _ h => not_lt_of_ge h)
  simpa only [Set.preimage_setOf_eq, nonnegativeRealSquareRoot, not_not] using (ae_iff.mp hNot)

theorem gaussian_previous_zero_limit_sharp_support :
    gaussianZeroShiftSingularLimit {t : ℝ≥0 | (2 : ℝ) < (t : ℝ)} = 0 := by
  rw [← gaussian_shifted_limit_at_zero]
  exact gaussian_zero_shift_sharp_support

theorem gaussian_zero_shift_log_integral_beta :
    (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit 0) =
      ∫ x, betaPDFReal (1 / 2) (3 / 2) x * Real.log (Real.sqrt (4 * x)) :=
  gaussian_zero_shift_beta_test_integral (fun t => Real.log (t : ℝ))
    beta_nnreal_log_stronglyMeasurable

theorem beta_half_log_sqrt_ae :
    ∀ᵐ x ∂gaussianZeroBetaBase,
      Real.log (Real.sqrt (4 * x)) = Real.log 2 + Real.log x / 2 := by
  filter_upwards [beta_measure_ae_unit_interval (1 / 2) (3 / 2)] with x hx
  rw [Real.log_sqrt (by linarith : (0 : ℝ) ≤ 4 * x),
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.1.ne']
  have hFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1; norm_num
  rw [hFour]
  ring

theorem beta_half_log_integrable : Integrable Real.log gaussianZeroBetaBase := by
  have hInt := gaussian_shifted_limit_log_integrable 0
  rw [gaussian_zero_shift_limit_eq_sqrt_beta] at hInt
  have hComp : Integrable (fun x => Real.log (Real.sqrt (4 * x))) gaussianZeroBetaBase :=
    (integrable_map_measure (Real.measurable_log.comp NNReal.continuous_coe.measurable).aestronglyMeasurable
      continuous_zero_beta_sqrt_map.measurable.aemeasurable).mp hInt
  have hFormula : Integrable (fun x => Real.log 2 + Real.log x / 2) gaussianZeroBetaBase :=
    hComp.congr beta_half_log_sqrt_ae
  have hScaled := (hFormula.sub (integrable_const (Real.log 2))).const_mul 2
  convert hScaled using 1
  funext x
  change Real.log x = 2 * ((Real.log 2 + Real.log x / 2) - Real.log 2)
  ring

theorem gaussian_zero_shift_log_integral_beta_log_moment :
    (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit 0) =
      Real.log 2 + (∫ x, Real.log x ∂gaussianZeroBetaBase) / 2 := by
  rw [gaussian_zero_shift_limit_eq_sqrt_beta, integral_map_of_stronglyMeasurable
    continuous_zero_beta_sqrt_map.measurable
    beta_nnreal_log_stronglyMeasurable]
  change (∫ x, Real.log (Real.sqrt (4 * x)) ∂gaussianZeroBetaBase) = _
  rw [integral_congr_ae beta_half_log_sqrt_ae,
    integral_add (integrable_const _) (beta_half_log_integrable.div_const 2), integral_div]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

end CircularLaw
