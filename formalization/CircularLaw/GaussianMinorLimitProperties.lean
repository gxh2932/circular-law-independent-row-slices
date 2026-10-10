import CircularLaw.BernoulliPrincipalMinorAmbientWeakLimit
import CircularLaw.GaussianShiftedLogValue

/-!
# Mass bounds and logarithmic values for the principal-minor limiting law

The positive scaling of the actual Gaussian law preserves a linear bound
near zero and compact upper support. Its finite logarithmic integral has
the exact scaling correction. As the minor ratio tends to one, this value
converges to the paper's full circular potential, including boundary shifts.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_minor_limit_small_mass {theta : ℝ} (hTheta : 0 < theta)
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (gaussianMinorSingularLimit theta z).real {r : ℝ≥0 | (r : ℝ) < t} ≤
      (48 / Real.sqrt theta) * t := by
  have hc : 0 < Real.sqrt theta := Real.sqrt_pos.2 hTheta
  have hg : Measurable (fun r : ℝ≥0 => Real.toNNReal (Real.sqrt theta) * r) :=
    (continuous_const.mul continuous_id).measurable
  have hs : MeasurableSet {r : ℝ≥0 | (r : ℝ) < t} :=
    measurableSet_lt NNReal.continuous_coe.measurable measurable_const
  rw [gaussianMinorSingularLimit, map_measureReal_apply hg hs]
  have hSet : (fun r : ℝ≥0 => Real.toNNReal (Real.sqrt theta) * r) ⁻¹'
      {r : ℝ≥0 | (r : ℝ) < t} = {r : ℝ≥0 | (r : ℝ) < t / Real.sqrt theta} := by
    ext r
    change (Real.toNNReal (Real.sqrt theta) * r : ℝ≥0).toReal < t ↔
      (r : ℝ) < t / Real.sqrt theta
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hc.le]
    simpa only [mul_comm] using (lt_div_iff₀ hc (a := (r : ℝ)) (b := t)).symm
  rw [hSet]
  calc
    _ ≤ 48 * (t / Real.sqrt theta) :=
      gaussian_shifted_limit_small_mass (z / (Real.sqrt theta : ℂ)) (div_pos ht hc)
    _ = _ := by ring

theorem gaussian_minor_limit_support {theta : ℝ} (hTheta : 0 < theta) (z : ℂ) :
    gaussianMinorSingularLimit theta z {t : ℝ≥0 |
      Real.sqrt theta * (128 + ‖z / (Real.sqrt theta : ℂ)‖) < (t : ℝ)} = 0 :=
  scaled_nonnegative_measure_support
    (gaussianShiftedSingularLimit (z / (Real.sqrt theta : ℂ))) (Real.sqrt_pos.2 hTheta)
    (gaussian_shifted_limit_support _)

theorem gaussian_minor_limit_finite_logarithmic_integral {theta : ℝ}
    (hTheta : 0 < theta) (z : ℂ) : FiniteLogarithmicIntegral (gaussianMinorSingularLimit theta z) :=
  finite_logarithmic_integral_of_mass_and_support (gaussianMinorSingularLimit theta z)
    (div_pos (by norm_num) (Real.sqrt_pos.2 hTheta))
    (fun _ ht => gaussian_minor_limit_small_mass hTheta z ht)
    (Real.sqrt theta * (128 + ‖z / (Real.sqrt theta : ℂ)‖))
    (gaussian_minor_limit_support hTheta z)

theorem gaussian_minor_limit_log_integral {theta : ℝ} (hTheta : 0 < theta) (z : ℂ) :
    (∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit theta z) =
      Real.log (Real.sqrt theta) + circularLogPotential (z / (Real.sqrt theta : ℂ)) := by
  let ν := gaussianShiftedSingularLimit (z / (Real.sqrt theta : ℂ))
  have hc : 0 < Real.sqrt theta := Real.sqrt_pos.2 hTheta
  have hg : Measurable (fun r : ℝ≥0 => Real.toNNReal (Real.sqrt theta) * r) :=
    (continuous_const.mul continuous_id).measurable
  have hf : StronglyMeasurable (fun t : ℝ≥0 => Real.log (t : ℝ)) :=
    (Real.measurable_log.comp NNReal.continuous_coe.measurable).stronglyMeasurable
  have hMap : (∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit theta z) =
      ∫ t : ℝ≥0, Real.log ((Real.toNNReal (Real.sqrt theta) * t : ℝ≥0) : ℝ) ∂ν :=
    integral_map_of_stronglyMeasurable hg hf
  rw [hMap]
  have hNe : ∀ᵐ t : ℝ≥0 ∂ν, t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using gaussian_shifted_limit_zero_atom
      (z / (Real.sqrt theta : ℂ))
  have hEq : (fun t : ℝ≥0 => Real.log ((Real.toNNReal (Real.sqrt theta) * t : ℝ≥0) : ℝ)) =ᵐ[ν]
      (fun t : ℝ≥0 => Real.log (Real.sqrt theta) + Real.log (t : ℝ)) := by
    filter_upwards [hNe] with t ht
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hc.le]
    exact Real.log_mul hc.ne' (by exact_mod_cast ht)
  rw [integral_congr_ae hEq,
    integral_add (integrable_const _) (gaussian_shifted_limit_log_integrable _),
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    gaussian_shifted_log_integral_eq_circular]

theorem gaussian_minor_limit_negative_log_value {theta : ℝ} (hTheta : 0 < theta) (z : ℂ) :
    -(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit theta z) =
      circularPaperPotential (z / (Real.sqrt theta : ℂ)) - Real.log (Real.sqrt theta) := by
  rw [gaussian_minor_limit_log_integral hTheta z, circularPaperPotential]
  ring

theorem gaussian_minor_limit_negative_log_tendsto (theta : ℕ → ℝ) (z : ℂ)
    (hTheta : ∀ᶠ n in atTop, 0 < theta n) (hLimit : Tendsto theta atTop (𝓝 1)) :
    Tendsto (fun n => -(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit (theta n) z))
      atTop (𝓝 (circularPaperPotential z)) := by
  have hRoot : Tendsto (fun n => Real.sqrt (theta n)) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one] using hLimit.sqrt
  have hRootC : Tendsto (fun n => (Real.sqrt (theta n) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp hRoot
  have hShift : Tendsto (fun n => z / (Real.sqrt (theta n) : ℂ)) atTop (𝓝 z) := by
    simpa only [div_one] using tendsto_const_nhds.div hRootC (by norm_num : (1 : ℂ) ≠ 0)
  have hValue := (circular_paper_potential_continuous.continuousAt.tendsto.comp hShift).sub
    ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hRoot)
  simp only [Real.log_one, sub_zero] at hValue
  apply hValue.congr'
  filter_upwards [hTheta] with n hn
  exact (gaussian_minor_limit_negative_log_value hn z).symm

end CircularLaw
