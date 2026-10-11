import CircularLaw.ComplexGaussianNormLaplace
import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact lower Laplace transforms for every deterministic Gaussian shift

Completing the square in the actual planar Gaussian density gives
`E exp(-a |G+w|^2) = (1+a)^-1 exp(-a/(1+a) |w|^2)` for `a>=0`.
In particular, the shifted lower Laplace transform is at most the
unshifted one. No Gaussian comparison principle is assumed.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem complex_gaussian_shift_complete_square {a : ℝ} (ha : 0 ≤ a) (z w : ℂ) :
    ‖z‖ ^ 2 + a * ‖z + w‖ ^ 2 =
      (1 + a) * ‖z + (a / (1 + a)) • w‖ ^ 2 + (a / (1 + a)) * ‖w‖ ^ 2 := by
  have hDen : (1 + a) ≠ 0 := by positivity
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  field_simp
  ring

theorem standardComplexGaussianDensity_shift_lower_exponential {a : ℝ} (ha : 0 ≤ a)
    (z w : ℂ) :
    standardComplexGaussianDensity z * Real.exp (-a * ‖z + w‖ ^ 2) =
      (Real.pi⁻¹ * Real.exp (-(a / (1 + a)) * ‖w‖ ^ 2)) *
        planarGaussian (1 + a) (z + (a / (1 + a)) • w) := by
  have hExponent : -‖z‖ ^ 2 + -a * ‖z + w‖ ^ 2 =
      -(a / (1 + a)) * ‖w‖ ^ 2 + -(1 + a) * ‖z + (a / (1 + a)) • w‖ ^ 2 := by
    linarith only [complex_gaussian_shift_complete_square ha z w]
  unfold standardComplexGaussianDensity planarGaussian
  rw [mul_assoc, ← Real.exp_add, hExponent, Real.exp_add, ← mul_assoc]

theorem standardComplexGaussianLaw_shift_lower_exponential_integrable {a : ℝ}
    (ha : 0 ≤ a) (w : ℂ) :
    Integrable (fun z : ℂ => Real.exp (-a * ‖z + w‖ ^ 2)) standardComplexGaussianLaw := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)))

theorem standardComplexGaussianLaw_shift_lower_exponential_integral {a : ℝ}
    (ha : 0 ≤ a) (w : ℂ) :
    (∫ z : ℂ, Real.exp (-a * ‖z + w‖ ^ 2) ∂standardComplexGaussianLaw) =
      (1 + a)⁻¹ * Real.exp (-(a / (1 + a)) * ‖w‖ ^ 2) := by
  have hD : Measurable (fun z => ENNReal.ofReal (standardComplexGaussianDensity z)) := by
    unfold standardComplexGaussianDensity
    fun_prop
  have hNonneg (z : ℂ) : 0 ≤ standardComplexGaussianDensity z := by
    unfold standardComplexGaussianDensity
    positivity
  rw [standardComplexGaussianLaw_density, densityLaw,
    integral_withDensity_eq_integral_toReal_smul hD
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hNonneg _), smul_eq_mul,
    standardComplexGaussianDensity_shift_lower_exponential ha]
  rw [integral_const_mul, integral_add_right_eq_self,
    planarGaussian_integral (by positivity : 0 < 1 + a)]
  field_simp

theorem standardComplexGaussianLaw_shift_lower_exponential_integral_le {a : ℝ}
    (ha : 0 ≤ a) (w : ℂ) :
    (∫ z : ℂ, Real.exp (-a * ‖z + w‖ ^ 2) ∂standardComplexGaussianLaw) ≤ (1 + a)⁻¹ := by
  rw [standardComplexGaussianLaw_shift_lower_exponential_integral ha]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)))

end CircularLaw
