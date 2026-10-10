import CircularLaw.ConvolutionConcentration
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Fourier kernels in the plane

These identities use the characteristic-function normalization
`exp(i*inner(x,t))`. The planar Gaussian integral is proved from mathlib's
finite-dimensional formula, with its integrability checked explicitly.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace CircularLaw

def planarGaussian (b : ℝ) (t : ℂ) : ℝ := Real.exp (-b * ‖t‖ ^ 2)

def gaussianFourierKernel (b : ℝ) (w t : ℂ) : ℂ :=
  Complex.exp (-(b : ℂ) * (‖t‖ : ℂ) ^ 2 + Complex.I * (⟪w, t⟫ : ℝ))

theorem gaussianFourierKernel_norm (b : ℝ) (w t : ℂ) :
    ‖gaussianFourierKernel b w t‖ = planarGaussian b t := by
  simp [gaussianFourierKernel, Complex.norm_exp, ← Complex.ofReal_pow, planarGaussian]

theorem gaussianFourierKernel_integrable {b : ℝ} (hb : 0 < b) (w : ℂ) :
    Integrable (gaussianFourierKernel b w) volume :=
  GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by simpa only [Complex.ofReal_re] using hb) Complex.I w

theorem planarGaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (planarGaussian b) volume := by
  simpa only [gaussianFourierKernel_norm] using
    (gaussianFourierKernel_integrable hb (0 : ℂ)).norm

theorem planarGaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ t : ℂ, planarGaussian b t) = Real.pi / b := by
  simpa only [planarGaussian, Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hb

theorem gaussianFourierKernel_integral {b : ℝ} (hb : 0 < b) (w : ℂ) :
    (∫ t : ℂ, gaussianFourierKernel b w t) =
      ((Real.pi / b) * Real.exp (-‖w‖ ^ 2 / (4 * b)) : ℝ) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (b : ℂ)) (by simpa only [Complex.ofReal_re] using hb) Complex.I w
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one, Complex.I_sq,
    neg_one_mul] at h
  unfold gaussianFourierKernel
  rw [h]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem gaussianFourierKernel_character (b : ℝ) (x z t : ℂ) :
    gaussianFourierKernel b (x - z) t =
      (planarGaussian b t : ℂ) *
        Complex.exp (-(⟪z, t⟫ : ℝ) * Complex.I) *
          Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) := by
  rw [planarGaussian, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
    gaussianFourierKernel, inner_sub_left]
  congr 1
  push_cast
  ring

end CircularLaw
