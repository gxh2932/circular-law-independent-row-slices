import CircularLaw.StandardComplexGaussian

/-!
# Exact real linear forms of the standard complex Gaussian

These formulas keep the variance-one-half normalization. In particular
they will determine the laws of real and imaginary parts of projected
coordinate differences.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem standardComplexGaussianLaw_realForm_formula (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = L 1 * z.re + L Complex.I * z.im := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = L 1 * z.re + L Complex.I * z.im := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring

theorem standardComplexGaussianLaw_realForm_mean (L : ℂ →L[ℝ] ℝ) :
    (∫ z, L z ∂standardComplexGaussianLaw) = 0 := by
  have hRe : HasGaussianLaw Complex.re standardComplexGaussianLaw :=
    (IsGaussian.hasGaussianLaw_id (μ := standardComplexGaussianLaw)).map_fun Complex.reCLM
  have hIm : HasGaussianLaw Complex.im standardComplexGaussianLaw :=
    (IsGaussian.hasGaussianLaw_id (μ := standardComplexGaussianLaw)).map_fun Complex.imCLM
  calc
    (∫ z, L z ∂standardComplexGaussianLaw) =
        ∫ z, L 1 * z.re + L Complex.I * z.im ∂standardComplexGaussianLaw :=
      integral_congr_ae (ae_of_all _ (standardComplexGaussianLaw_realForm_formula L))
    _ = 0 := by
      rw [integral_add (hRe.integrable.const_mul _) (hIm.integrable.const_mul _),
        integral_const_mul, integral_const_mul, standardComplexGaussianLaw_re_mean,
        standardComplexGaussianLaw_im_mean]
      simp

theorem standardComplexGaussianLaw_realForm_variance (L : ℂ →L[ℝ] ℝ) :
    Var[L; standardComplexGaussianLaw] = (L 1 ^ 2 + L Complex.I ^ 2) / 2 := by
  have hRe : HasGaussianLaw Complex.re standardComplexGaussianLaw :=
    (IsGaussian.hasGaussianLaw_id (μ := standardComplexGaussianLaw)).map_fun Complex.reCLM
  have hIm : HasGaussianLaw Complex.im standardComplexGaussianLaw :=
    (IsGaussian.hasGaussianLaw_id (μ := standardComplexGaussianLaw)).map_fun Complex.imCLM
  have hInd : IndepFun (fun z : ℂ => L 1 * z.re) (fun z : ℂ => L Complex.I * z.im)
      standardComplexGaussianLaw := standardComplexGaussianLaw_independent.comp
    (show Measurable (fun x : ℝ => L 1 * x) by fun_prop)
    (show Measurable (fun x : ℝ => L Complex.I * x) by fun_prop)
  have hEq : (L : ℂ → ℝ) = fun z => L 1 * z.re + L Complex.I * z.im :=
    funext (standardComplexGaussianLaw_realForm_formula L)
  calc
    Var[L; standardComplexGaussianLaw] =
        Var[fun z => L 1 * z.re + L Complex.I * z.im; standardComplexGaussianLaw] :=
      congrArg (fun f => variance f standardComplexGaussianLaw) hEq
    _ = (L 1 ^ 2 + L Complex.I ^ 2) / 2 := by
      rw [hInd.variance_fun_add (hRe.memLp_two.const_mul _) (hIm.memLp_two.const_mul _),
        variance_const_mul, variance_const_mul, standardComplexGaussianLaw_re_variance,
        standardComplexGaussianLaw_im_variance]
      ring

theorem standardComplexGaussianLaw_map_realForm (L : ℂ →L[ℝ] ℝ) :
    standardComplexGaussianLaw.map L =
      gaussianReal 0 ((L 1 ^ 2 + L Complex.I ^ 2) / 2).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal L, standardComplexGaussianLaw_realForm_mean,
    standardComplexGaussianLaw_realForm_variance]

theorem standardComplexGaussianLaw_charFunDual (L : ℂ →L[ℝ] ℝ) :
    charFunDual standardComplexGaussianLaw L =
      Complex.exp (-(((L 1 ^ 2 + L Complex.I ^ 2) / 4 : ℝ) : ℂ)) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, standardComplexGaussianLaw_realForm_mean,
    standardComplexGaussianLaw_realForm_variance]
  congr 1
  push_cast
  ring

theorem complex_realForm_rotated_norm_sq (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z ^ 2 + L (Complex.I * z) ^ 2 = (L 1 ^ 2 + L Complex.I ^ 2) * ‖z‖ ^ 2 := by
  rw [standardComplexGaussianLaw_realForm_formula L z,
    standardComplexGaussianLaw_realForm_formula L (Complex.I * z),
    ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, Complex.normSq_apply]
  ring

theorem standardComplexGaussianLaw_norm_sq_mean :
    (∫ z, ‖z‖ ^ 2 ∂standardComplexGaussianLaw) = 1 := by
  have hRe : HasGaussianLaw Complex.re standardComplexGaussianLaw :=
    (IsGaussian.hasGaussianLaw_id (μ := standardComplexGaussianLaw)).map_fun Complex.reCLM
  have hIm : HasGaussianLaw Complex.im standardComplexGaussianLaw :=
    (IsGaussian.hasGaussianLaw_id (μ := standardComplexGaussianLaw)).map_fun Complex.imCLM
  have hReSq : (∫ z, z.re ^ 2 ∂standardComplexGaussianLaw) = (1 / 2 : ℝ) := by
    have h := standardComplexGaussianLaw_re_variance
    rw [variance_eq_integral (by fun_prop), standardComplexGaussianLaw_re_mean] at h
    simpa using h
  have hImSq : (∫ z, z.im ^ 2 ∂standardComplexGaussianLaw) = (1 / 2 : ℝ) := by
    have h := standardComplexGaussianLaw_im_variance
    rw [variance_eq_integral (by fun_prop), standardComplexGaussianLaw_im_mean] at h
    simpa using h
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [← pow_two]
  rw [integral_add hRe.memLp_two.integrable_sq hIm.memLp_two.integrable_sq]
  nlinarith only [hReSq, hImSq]

end CircularLaw
