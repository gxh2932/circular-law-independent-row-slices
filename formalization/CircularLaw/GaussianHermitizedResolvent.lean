import CircularLaw.GaussianShiftedResolventCubic

/-!
# The actual Gaussian Hermitized resolvent satisfies the Dyson equation

At a positive real spectral parameter, the actual integral of
`t/(t^2+s^2)` is positive and bounded. Substitution into the analytic
squared-resolvent cubic gives its exact scalar Dyson equation. The
equation also bounds the actual resolvent by one uniformly as t tends
to zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def hermitizedResolventKernel (t : ℝ) (s : ℝ≥0) : ℝ :=
  t / (t ^ 2 + (s : ℝ) ^ 2)

def gaussianHermitizedResolvent (r t : ℝ) : ℝ :=
  ∫ s, hermitizedResolventKernel t s ∂gaussianShiftedSingularLimit (r : ℂ)

theorem hermitized_resolvent_kernel_pos {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    0 < hermitizedResolventKernel t s := by
  unfold hermitizedResolventKernel
  exact div_pos ht (by positivity)

theorem hermitized_resolvent_kernel_bound {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    hermitizedResolventKernel t s ≤ 1 / t := by
  unfold hermitizedResolventKernel
  apply (div_le_div_iff₀ (by positivity : 0 < t ^ 2 + (s : ℝ) ^ 2) ht).2
  nlinarith [sq_nonneg (s : ℝ)]

theorem hermitized_resolvent_kernel_measurable (t : ℝ) :
    Measurable (hermitizedResolventKernel t) := by
  unfold hermitizedResolventKernel
  fun_prop

theorem hermitized_resolvent_kernel_integrable (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0 < t) : Integrable (hermitizedResolventKernel t) ν := by
  apply Integrable.of_bound (hermitized_resolvent_kernel_measurable t).aestronglyMeasurable (1 / t)
  exact Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs, abs_of_pos (hermitized_resolvent_kernel_pos ht s)]
    exact hermitized_resolvent_kernel_bound ht s)

theorem gaussian_hermitized_resolvent_pos (r : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < gaussianHermitizedResolvent r t := by
  rw [gaussianHermitizedResolvent,
    integral_pos_iff_support_of_nonneg (fun s => (hermitized_resolvent_kernel_pos ht s).le)
      (hermitized_resolvent_kernel_integrable _ ht)]
  have hSupport : Function.support (hermitizedResolventKernel t) = Set.univ := by
    ext s
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hermitized_resolvent_kernel_pos ht s)
  rw [hSupport]
  simp

theorem gaussian_hermitized_resolvent_bound (r : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianHermitizedResolvent r t ≤ 1 / t := by
  calc
    _ ≤ ∫ _ : ℝ≥0, 1 / t ∂gaussianShiftedSingularLimit (r : ℂ) :=
      integral_mono (hermitized_resolvent_kernel_integrable _ ht) (integrable_const _)
        (hermitized_resolvent_kernel_bound ht)
    _ = _ := by simp

theorem gaussian_hermitized_squared_resolvent (r : ℝ) {t : ℝ} (ht : 0 < t) :
    squaredResolvent (gaussianShiftedSingularLimit (r : ℂ))
      (Complex.ofReal (-(t ^ 2)⁻¹)) = Complex.ofReal (t * gaussianHermitizedResolvent r t) := by
  have hPoint (s : ℝ≥0) :
      squaredResolventKernel (Complex.ofReal (-(t ^ 2)⁻¹)) s =
        Complex.ofReal (t * hermitizedResolventKernel t s) := by
    simp only [squaredResolventKernel, hermitizedResolventKernel, ← Complex.ofReal_one,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_inv]
    apply congrArg Complex.ofReal
    have hDen : 0 < t ^ 2 + (s : ℝ) ^ 2 := by positivity
    field_simp [ne_of_gt ht, ne_of_gt hDen]
    ring
  unfold squaredResolvent gaussianHermitizedResolvent
  simp only [hPoint]
  rw [integral_complex_ofReal, integral_const_mul]

theorem gaussian_hermitized_resolvent_equation (r : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianHermitizedResolvent r t * ((t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2) =
      t + gaussianHermitizedResolvent r t := by
  let g := gaussianHermitizedResolvent r t
  have hq : (Complex.ofReal (-(t ^ 2)⁻¹)).re < 0 := by
    simp only [Complex.ofReal_re]
    exact neg_neg_of_pos (inv_pos.mpr (sq_pos_of_pos ht))
  have hC := gaussian_shifted_resolvent_cubic r hq
  unfold gaussianShiftedResolventCubic at hC
  rw [gaussian_hermitized_squared_resolvent r ht] at hC
  dsimp only at hC
  have hReal : (-(t ^ 2)⁻¹) ^ 2 * (t * g) ^ 3 -
      2 * (-(t ^ 2)⁻¹) * (t * g) ^ 2 +
        (1 + (-(t ^ 2)⁻¹) * (1 - r ^ 2)) * (t * g) - 1 = 0 := by
    exact_mod_cast hC
  have hCalc : t * ((-(t ^ 2)⁻¹) ^ 2 * (t * g) ^ 3 -
      2 * (-(t ^ 2)⁻¹) * (t * g) ^ 2 +
        (1 + (-(t ^ 2)⁻¹) * (1 - r ^ 2)) * (t * g) - 1) =
      g * ((t + g) ^ 2 + r ^ 2) - (t + g) := by
    field_simp [ne_of_gt ht]
    ring
  apply sub_eq_zero.mp
  rw [← hCalc, hReal, mul_zero]

theorem gaussian_hermitized_resolvent_dyson (r : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianHermitizedResolvent r t = (t + gaussianHermitizedResolvent r t) /
      ((t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2) := by
  have hPos : 0 < t + gaussianHermitizedResolvent r t :=
    add_pos ht (gaussian_hermitized_resolvent_pos r ht)
  apply (eq_div_iff (by positivity : (t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2 ≠ 0)).2
  exact gaussian_hermitized_resolvent_equation r ht

theorem gaussian_hermitized_resolvent_unit_bound (r : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianHermitizedResolvent r t ≤ 1 := by
  let g := gaussianHermitizedResolvent r t
  have hg : 0 < g := gaussian_hermitized_resolvent_pos r ht
  have hEq := gaussian_hermitized_resolvent_equation r ht
  change g * ((t + g) ^ 2 + r ^ 2) = t + g at hEq
  have hGU : g * (t + g) ≤ 1 := by
    apply (mul_le_mul_iff_right₀ (add_pos ht hg)).mp
    nlinarith [mul_nonneg hg.le (sq_nonneg r)]
  nlinarith [mul_nonneg ht.le hg.le]

theorem gaussian_hermitized_resolvent_denominator_gt_one (r : ℝ) {t : ℝ} (ht : 0 < t) :
    1 < (t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2 := by
  apply (mul_lt_mul_iff_left₀ (gaussian_hermitized_resolvent_pos r ht)).mp
  nlinarith [gaussian_hermitized_resolvent_equation r ht]

end CircularLaw
