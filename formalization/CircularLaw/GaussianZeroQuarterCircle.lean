import CircularLaw.BetaQuarterCircleChange
import CircularLaw.GaussianZeroLogValue

/-!
# The quarter-circle density of the actual zero-shift Gaussian limit

The measure on (0,2) with density sqrt(4-s^2)/pi is a probability law.
Mapping its coordinate into NNReal gives exactly the actual Gaussian
singular weak limit, with the integral identity valid for every strongly
measurable real test, including the logarithm.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace CircularLaw

def quarterCircleWeight (s : ℝ) : ℝ := Real.sqrt (4 - s ^ 2) / Real.pi

def quarterCircleRealMeasure : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 2)).withDensity (fun s => ENNReal.ofReal (quarterCircleWeight s))

theorem quarter_circle_weight_continuous : Continuous quarterCircleWeight := by
  unfold quarterCircleWeight
  fun_prop

theorem quarter_circle_weight_nonneg (s : ℝ) : 0 ≤ quarterCircleWeight s :=
  div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le

theorem quarter_circle_weight_integrable : IntegrableOn quarterCircleWeight (Ioo (0 : ℝ) 2) :=
  (quarter_circle_weight_continuous.locallyIntegrable.integrableOn_isCompact
    isCompact_Icc).mono_set Ioo_subset_Icc_self

theorem quarter_circle_density_measurable :
    Measurable (fun s => ENNReal.ofReal (quarterCircleWeight s)) :=
  ENNReal.measurable_ofReal.comp quarter_circle_weight_continuous.measurable

theorem gaussian_zero_quarter_circle_test_integral (f : ℝ≥0 → ℝ) (hf : StronglyMeasurable f) :
    (∫ t, f t ∂gaussianShiftedSingularLimit 0) =
      ∫ s in Ioo (0 : ℝ) 2, quarterCircleWeight s * f (Real.toNNReal s) := by
  rw [gaussian_zero_shift_beta_test_integral f hf]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioo (0 : ℝ) 1) (fun x hx => by
      simp only [mem_Ioo] at hx
      simp only [betaPDFReal, if_neg hx, zero_mul])]
  exact beta_quarter_circle_change_integral f

theorem quarter_circle_weight_integral_one :
    (∫ s in Ioo (0 : ℝ) 2, quarterCircleWeight s) = 1 := by
  have h := gaussian_zero_quarter_circle_test_integral (fun _ => 1) stronglyMeasurable_const
  simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, mul_one] using h.symm

instance quarter_circle_real_probability : IsProbabilityMeasure quarterCircleRealMeasure where
  measure_univ := by
    rw [quarterCircleRealMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
        quarter_circle_weight_integrable
        (Filter.Eventually.of_forall quarter_circle_weight_nonneg),
      quarter_circle_weight_integral_one, ENNReal.ofReal_one]

def quarterCircleSingularMeasure : Measure ℝ≥0 :=
  quarterCircleRealMeasure.map Real.toNNReal

theorem quarter_circle_coordinate_measurable : Measurable Real.toNNReal := by fun_prop

instance quarter_circle_singular_probability : IsProbabilityMeasure quarterCircleSingularMeasure :=
  Measure.isProbabilityMeasure_map quarter_circle_coordinate_measurable.aemeasurable

theorem quarter_circle_singular_test_integral (f : ℝ≥0 → ℝ) (hf : StronglyMeasurable f) :
    (∫ t, f t ∂quarterCircleSingularMeasure) =
      ∫ s in Ioo (0 : ℝ) 2, quarterCircleWeight s * f (Real.toNNReal s) := by
  rw [quarterCircleSingularMeasure, integral_map_of_stronglyMeasurable
    quarter_circle_coordinate_measurable hf, quarterCircleRealMeasure,
    integral_withDensity_eq_integral_toReal_smul
      quarter_circle_density_measurable
      (Filter.Eventually.of_forall (fun s => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (quarter_circle_weight_nonneg _)]

theorem gaussian_zero_shift_limit_eq_quarter_circle :
    gaussianShiftedSingularLimit 0 = quarterCircleSingularMeasure := by
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hf : StronglyMeasurable (s.indicator (fun _ : ℝ≥0 => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hs
  have h := (gaussian_zero_quarter_circle_test_integral _ hf).trans
    (quarter_circle_singular_test_integral _ hf).symm
  change (∫ t, s.indicator (1 : ℝ≥0 → ℝ) t ∂gaussianShiftedSingularLimit 0) =
    (∫ t, s.indicator (1 : ℝ≥0 → ℝ) t ∂quarterCircleSingularMeasure) at h
  rw [integral_indicator_one hs, integral_indicator_one hs] at h
  exact h

theorem gaussian_previous_zero_limit_eq_quarter_circle :
    gaussianZeroShiftSingularLimit = quarterCircleSingularMeasure := by
  rw [← gaussian_shifted_limit_at_zero, gaussian_zero_shift_limit_eq_quarter_circle]

theorem gaussian_zero_quarter_circle_weak_convergence :
    EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x))
      quarterCircleSingularMeasure := by
  rw [← gaussian_zero_shift_limit_eq_quarter_circle]
  exact gaussian_shifted_weak_convergence 0

theorem gaussian_zero_quarter_circle_log_integral :
    (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit 0) =
      ∫ s in Ioo (0 : ℝ) 2, (Real.sqrt (4 - s ^ 2) / Real.pi) * Real.log s := by
  rw [gaussian_zero_quarter_circle_test_integral _ beta_nnreal_log_stronglyMeasurable]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [Real.coe_toNNReal _ hs.1.le]
  rfl

theorem quarter_circle_singular_log_integrable :
    Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) quarterCircleSingularMeasure := by
  rw [← gaussian_zero_shift_limit_eq_quarter_circle]
  exact gaussian_shifted_limit_log_integrable 0

theorem quarter_circle_singular_log_integral_value :
    (∫ t, Real.log (t : ℝ) ∂quarterCircleSingularMeasure) = -(1 / 2 : ℝ) := by
  rw [← gaussian_zero_shift_limit_eq_quarter_circle]
  exact gaussian_zero_shift_log_integral_value

theorem quarter_circle_density_log_integral_value :
    (∫ s in Ioo (0 : ℝ) 2, (Real.sqrt (4 - s ^ 2) / Real.pi) * Real.log s) =
      -(1 / 2 : ℝ) := by
  rw [← gaussian_zero_quarter_circle_log_integral, gaussian_zero_shift_log_integral_value]

end CircularLaw
