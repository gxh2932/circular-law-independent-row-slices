import CircularLaw.DensityMeasure

/-!
# Uniform planar disk noise

The smoothing argument uses a centered uniform disk law. Its normalization,
support, reflection symmetry, zero mean, and second-moment bound are proved
from planar area; they are not additional assumptions on the noise.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CircularLaw

def planarDiskLaw (r : ℝ) : Measure ℂ :=
  ENNReal.ofReal ((r ^ 2 * Real.pi)⁻¹) • volume.restrict (Metric.closedBall 0 r)

theorem planarDiskLaw_probability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (planarDiskLaw r) := by
  have harea : 0 < r ^ 2 * Real.pi := mul_pos (sq_pos_of_pos hr) Real.pi_pos
  constructor
  rw [planarDiskLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Complex.volume_closedBall]
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [← hpi, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (sq_nonneg r),
    ← ENNReal.ofReal_mul (inv_nonneg.2 harea.le), inv_mul_cancel₀ harea.ne',
    ENNReal.ofReal_one]

theorem planarDiskLaw_norm_le {r : ℝ} : ∀ᵐ x ∂planarDiskLaw r, ‖x‖ ≤ r := by
  apply Measure.ae_smul_measure
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
    (ae_restrict_mem (μ := (volume : Measure ℂ)) (measurableSet_closedBall (x := 0) (ε := r)))

theorem planarDiskLaw_map_neg (r : ℝ) :
    (planarDiskLaw r).map (fun x : ℂ => -x) = planarDiskLaw r := by
  have hPre : (fun x : ℂ => -x) ⁻¹' Metric.closedBall 0 r = Metric.closedBall 0 r := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg]
  have hMap : ((volume : Measure ℂ).restrict (Metric.closedBall 0 r)).map
      (fun x : ℂ => -x) = (volume.map (fun x : ℂ => -x)).restrict
        (Metric.closedBall 0 r) := by
    rw [Measure.restrict_map measurable_neg measurableSet_closedBall, hPre]
  rw [planarDiskLaw, Measure.map_smul, hMap, Measure.map_neg_eq_self]

theorem planarDiskLaw_integrable_id {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℂ => x) (planarDiskLaw r) := by
  haveI := planarDiskLaw_probability hr
  exact (integrable_const r).mono' measurable_id.aestronglyMeasurable planarDiskLaw_norm_le

theorem planarDiskLaw_mean_zero (r : ℝ) :
    (∫ x : ℂ, x ∂planarDiskLaw r) = 0 := by
  have h : (∫ x : ℂ, x ∂planarDiskLaw r) = -(∫ x : ℂ, x ∂planarDiskLaw r) := by
    calc
      _ = ∫ x : ℂ, x ∂(planarDiskLaw r).map (fun y : ℂ => -y) := by
        rw [planarDiskLaw_map_neg]
      _ = ∫ x : ℂ, -x ∂planarDiskLaw r :=
        integral_map measurable_neg.aemeasurable measurable_id.aestronglyMeasurable
      _ = _ := integral_neg (fun x : ℂ => x)
  linear_combination h / 2

theorem planarDiskLaw_integrable_norm_sq {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) (planarDiskLaw r) := by
  haveI := planarDiskLaw_probability hr
  apply (integrable_const (r ^ 2)).mono' (by fun_prop)
  filter_upwards [planarDiskLaw_norm_le (r := r)] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] using
    (sq_le_sq₀ (norm_nonneg x) hr.le).2 hx

theorem planarDiskLaw_second_moment_le {r : ℝ} (hr : 0 < r) :
    (∫ x : ℂ, ‖x‖ ^ 2 ∂planarDiskLaw r) ≤ r ^ 2 := by
  haveI := planarDiskLaw_probability hr
  calc
    _ ≤ ∫ _ : ℂ, r ^ 2 ∂planarDiskLaw r := by
      apply integral_mono_ae (planarDiskLaw_integrable_norm_sq hr) (integrable_const _)
      filter_upwards [planarDiskLaw_norm_le (r := r)] with x hx
      exact (sq_le_sq₀ (norm_nonneg x) hr.le).2 hx
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

end CircularLaw
