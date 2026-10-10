import CircularLaw.ComplexGaussianNormLaplace
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Exact moments of the actual standard complex Gaussian

Every polynomial moment is integrable. Polar Gamma integration gives
`E |G|^(2k) = k!`, with the manuscript variance-one-half normalization.
These are the radial inputs to the mixed-entry trace-moment argument.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CircularLaw

theorem standard_complex_gaussian_norm_power_integrable (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k) standardComplexGaussianLaw := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id standardComplexGaussianLaw k (by simp)).integrable_norm_pow'

theorem standard_complex_gaussian_mixed_power_integrable (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * star z ^ q) standardComplexGaussianLaw := by
  apply (standard_complex_gaussian_norm_power_integrable (p + q)).mono'
    (by fun_prop : AEStronglyMeasurable (fun z : ℂ => z ^ p * star z ^ q)
      standardComplexGaussianLaw)
  apply ae_of_all
  intro z
  simp only [norm_mul, norm_pow, norm_star, pow_add]
  exact le_rfl

theorem standard_complex_gaussian_even_norm_moment (k : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ (2 * k) ∂standardComplexGaussianLaw) = k.factorial := by
  have hD : Measurable (fun z => ENNReal.ofReal (standardComplexGaussianDensity z)) := by
    unfold standardComplexGaussianDensity
    fun_prop
  have hNonneg (z : ℂ) : 0 ≤ standardComplexGaussianDensity z := by
    unfold standardComplexGaussianDensity
    positivity
  rw [standardComplexGaussianLaw_density, densityLaw,
    integral_withDensity_eq_integral_toReal_smul hD
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hToReal (z : ℂ) : (ENNReal.ofReal (standardComplexGaussianDensity z)).toReal =
      standardComplexGaussianDensity z := ENNReal.toReal_ofReal (hNonneg z)
  simp only [hToReal, smul_eq_mul]
  unfold standardComplexGaussianDensity
  have hFun : (fun z : ℂ => (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2)) * ‖z‖ ^ (2 * k)) =
      fun z : ℂ => Real.pi⁻¹ * (‖z‖ ^ ((2 * k : ℕ) : ℝ) * Real.exp (-‖z‖ ^ (2 : ℝ))) := by
    funext z
    rw [Real.rpow_natCast, Real.rpow_two]
    ring
  rw [hFun, integral_const_mul,
    Complex.integral_rpow_mul_exp_neg_rpow (by norm_num : (1 : ℝ) ≤ 2)
      (by have h : (0 : ℝ) ≤ (2 * k : ℕ) := Nat.cast_nonneg _
          linarith : (-2 : ℝ) < ((2 * k : ℕ) : ℝ))]
  have hGammaArg : (((2 * k : ℕ) : ℝ) + 2) / 2 = (k : ℝ) + 1 := by
    push_cast
    ring
  rw [hGammaArg, Real.Gamma_nat_eq_factorial]
  field_simp

theorem complex_balanced_power_eq_norm_power (z : ℂ) (k : ℕ) :
    z ^ k * star z ^ k = ((‖z‖ ^ (2 * k) : ℝ) : ℂ) := by
  rw [← mul_pow]
  change (z * (starRingEnd ℂ) z) ^ k = _
  rw [Complex.mul_conj', ← pow_mul, ← Complex.ofReal_pow]

theorem standard_complex_gaussian_balanced_moment (k : ℕ) :
    (∫ z : ℂ, z ^ k * star z ^ k ∂standardComplexGaussianLaw) = k.factorial := by
  simp only [complex_balanced_power_eq_norm_power, integral_complex_ofReal,
    standard_complex_gaussian_even_norm_moment, Complex.ofReal_natCast]

end CircularLaw
