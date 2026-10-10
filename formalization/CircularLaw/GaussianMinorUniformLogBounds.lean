import CircularLaw.GaussianMinorLimitProperties
import CircularLaw.LinearMassLogClipping

/-!
# Uniform limiting-law logarithmic bounds as the minor fraction vanishes

For minor ratios in [1/2,1], one common mass constant and upper support
bound control all limiting laws. Negative clipping has a uniform
exponential error, and sufficiently large positive clipping is exact.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_minor_limit_uniform_small_mass {theta : ℝ}
    (hTheta : 1 / 2 ≤ theta) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (gaussianMinorSingularLimit theta z).real {r : ℝ≥0 | (r : ℝ) < t} ≤ 96 * t := by
  have hPos : 0 < theta := by linarith
  have hRoot : 0 < Real.sqrt theta := Real.sqrt_pos.2 hPos
  have hLower : (1 / 2 : ℝ) ≤ Real.sqrt theta := by
    nlinarith [Real.sq_sqrt hPos.le, Real.sqrt_nonneg theta]
  have hCoefficient : 48 / Real.sqrt theta ≤ 96 :=
    (div_le_iff₀ hRoot).mpr (by linarith)
  exact (gaussian_minor_limit_small_mass hPos z ht).trans
    (mul_le_mul_of_nonneg_right hCoefficient ht.le)

theorem gaussian_minor_limit_uniform_support {theta : ℝ}
    (hPos : 0 < theta) (hOne : theta ≤ 1) (z : ℂ) :
    gaussianMinorSingularLimit theta z {t : ℝ≥0 | 128 + ‖z‖ < (t : ℝ)} = 0 := by
  have hRoot : 0 < Real.sqrt theta := Real.sqrt_pos.2 hPos
  have hRootOne : Real.sqrt theta ≤ 1 := by
    nlinarith [Real.sq_sqrt hPos.le, Real.sqrt_nonneg theta]
  have hRadius : Real.sqrt theta * (128 + ‖z / (Real.sqrt theta : ℂ)‖) ≤ 128 + ‖z‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRoot.le]
    have hCancel : Real.sqrt theta * (‖z‖ / Real.sqrt theta) = ‖z‖ := by
      field_simp
    nlinarith
  exact measure_mono_null (fun _ ht => hRadius.trans_lt ht) (gaussian_minor_limit_support hPos z)

theorem gaussian_minor_limit_uniform_negative_clipping {theta : ℝ}
    (hTheta : 1 / 2 ≤ theta) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t, clippedNegativeLog T t ∂gaussianMinorSingularLimit theta z) -
      ∫ t, hermitizationNegativeLog t ∂gaussianMinorSingularLimit theta z| ≤
        192 * Real.exp (-T / 2) := by
  simpa only [show (2 : ℝ) * 96 = 192 by norm_num] using
    negative_log_clipping_integral_error_of_linear_mass (gaussianMinorSingularLimit theta z)
      (by norm_num : (0 : ℝ) < 96) hT
      (fun _ ht => gaussian_minor_limit_uniform_small_mass hTheta z ht)

theorem gaussian_minor_limit_uniform_positive_clipping {theta : ℝ}
    (hPos : 0 < theta) (hOne : theta ≤ 1) (z : ℂ) {T : ℝ}
    (hT : Real.log (128 + ‖z‖) ≤ T) :
    (∫ t, clippedPositiveLog T t ∂gaussianMinorSingularLimit theta z) =
      ∫ t, hermitizationPositiveLog t ∂gaussianMinorSingularLimit theta z := by
  apply clipped_positive_log_integral_eq_of_support _ _
    (gaussian_minor_limit_uniform_support hPos hOne z)
  simpa only [max_eq_left (show (1 : ℝ) ≤ 128 + ‖z‖ by linarith [norm_nonneg z])] using hT

end CircularLaw
