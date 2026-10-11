import CircularLaw.PlanarGaussian

/-!
# The Gaussian Fourier bound for planar concentration

For an actual probability law, Fubini identifies its Gaussian average
with a weighted characteristic-function integral. A closed-ball indicator
is dominated by the Gaussian, giving the analytic upper bound used in
the planar sum-concentration argument.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace CircularLaw

theorem gaussianFourierKernel_prod_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (z : ℂ) :
    Integrable (fun p : ℂ × ℂ => gaussianFourierKernel b (p.1 - z) p.2) (μ.prod volume) := by
  apply ((planarGaussian_integrable hb).comp_snd μ).mono'
  · unfold gaussianFourierKernel
    fun_prop
  · exact ae_of_all _ (fun p => (gaussianFourierKernel_norm b (p.1 - z) p.2).le)

theorem integral_gaussianFourierKernel_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (b : ℝ) (z t : ℂ) :
    (∫ x, gaussianFourierKernel b (x - z) t ∂μ) =
      (planarGaussian b t : ℂ) * Complex.exp (-(⟪z, t⟫ : ℝ) * Complex.I) * charFun μ t := by
  simp only [gaussianFourierKernel_character, integral_const_mul, charFun_apply]

theorem gaussian_character_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (z : ℂ) :
    Integrable (fun t => (planarGaussian b t : ℂ) *
      Complex.exp (-(⟪z, t⟫ : ℝ) * Complex.I) * charFun μ t) volume := by
  simpa only [integral_gaussianFourierKernel_probability] using
    (gaussianFourierKernel_prod_integrable μ hb z).integral_prod_right

theorem gaussian_probability_fourier_identity (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (∫ t, (planarGaussian b t : ℂ) *
      Complex.exp (-(⟪z, t⟫ : ℝ) * Complex.I) * charFun μ t) =
      ((Real.pi / b) * (∫ x, Real.exp (-‖x - z‖ ^ 2 / (4 * b)) ∂μ) : ℝ) := by
  calc
    _ = ∫ t, ∫ x, gaussianFourierKernel b (x - z) t ∂μ := by
      simp only [integral_gaussianFourierKernel_probability]
    _ = ∫ x, (∫ t, gaussianFourierKernel b (x - z) t) ∂μ :=
      (integral_integral_swap (gaussianFourierKernel_prod_integrable μ hb z)).symm
    _ = _ := by
      simp only [gaussianFourierKernel_integral hb, Complex.ofReal_mul,
        integral_const_mul, integral_complex_ofReal]

theorem gaussian_character_norm (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (b : ℝ) (z t : ℂ) :
    ‖(planarGaussian b t : ℂ) * Complex.exp (-(⟪z, t⟫ : ℝ) * Complex.I) * charFun μ t‖ =
      planarGaussian b t * ‖charFun μ t‖ := by
  rw [norm_mul, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-b * ‖t‖ ^ 2)), planarGaussian, mul_one]

theorem gaussian_modulus_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun t => planarGaussian b t * ‖charFun μ t‖) volume := by
  simpa only [gaussian_character_norm] using (gaussian_character_integrable μ hb (0 : ℂ)).norm

theorem gaussian_probability_average_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (∫ x, Real.exp (-‖x - z‖ ^ 2 / (4 * b)) ∂μ) ≤
      (b / Real.pi) * (∫ t, planarGaussian b t * ‖charFun μ t‖) := by
  have h := norm_integral_le_integral_norm (μ := volume) (fun t => (planarGaussian b t : ℂ) *
    Complex.exp (-(⟪z, t⟫ : ℝ) * Complex.I) * charFun μ t)
  rw [gaussian_probability_fourier_identity μ hb z] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (div_pos Real.pi_pos hb).le (integral_nonneg (fun _ => (Real.exp_pos _).le))),
    gaussian_character_norm] at h
  have hFactor : (b / Real.pi) * (Real.pi / b) = 1 := by field_simp
  have hMul := mul_le_mul_of_nonneg_left h (div_pos hb Real.pi_pos).le
  simpa only [← mul_assoc, hFactor, one_mul] using hMul

theorem probability_closedBall_le_gaussian_average (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    μ.real (Metric.closedBall z r) ≤
      Real.exp 1 * (∫ x, Real.exp (-‖x - z‖ ^ 2 / r ^ 2) ∂μ) := by
  have hInt : Integrable (fun x => Real.exp (-‖x - z‖ ^ 2 / r ^ 2)) μ := by
    apply integrable_of_abs_bound μ (by fun_prop) (C := 1)
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (sq_nonneg r))
  have h := integral_mono
    ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
    (hInt.const_mul (Real.exp 1)) (fun x => by
      by_cases hx : x ∈ Metric.closedBall z r
      · rw [Set.indicator_of_mem hx, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        have hDist : ‖x - z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
        have hSq := pow_le_pow_left₀ (norm_nonneg _) hDist 2
        have hRatio : ‖x - z‖ ^ 2 / r ^ 2 ≤ 1 :=
          (div_le_one (sq_pos_of_pos hr)).mpr hSq
        rw [neg_div]
        linarith
      · rw [Set.indicator_of_notMem hx]
        positivity)
  rw [integral_indicator_const 1 measurableSet_closedBall] at h
  simpa only [smul_eq_mul, mul_one, integral_const_mul] using h

theorem gaussian_planar_small_ball (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    μ.real (Metric.closedBall z r) ≤
      Real.exp 1 * (r ^ 2 / (4 * Real.pi)) *
        (∫ t, Real.exp (-(r ^ 2 / 4) * ‖t‖ ^ 2) * ‖charFun μ t‖) := by
  have hB : 0 < r ^ 2 / 4 := by positivity
  have hAverage := gaussian_probability_average_le μ hB z
  have hScale : 4 * (r ^ 2 / 4) = r ^ 2 := by ring
  rw [hScale] at hAverage
  have h := (probability_closedBall_le_gaussian_average μ hr z).trans
    (mul_le_mul_of_nonneg_left hAverage (Real.exp_pos 1).le)
  simpa only [planarGaussian, div_div, mul_assoc] using h

end CircularLaw
