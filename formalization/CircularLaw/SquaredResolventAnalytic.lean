import CircularLaw.GaussianShiftedLimitProperties
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic squared resolvents of the actual Gaussian limiting measures

For a compactly supported finite nonnegative-coordinate measure, the
squared resolvent is analytic on the left complex half-plane. Bounds on
the actual kernel and derivative justify differentiation under the
integral. The Gaussian weak limit supplies the required support bound.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

def squaredResolventKernel (q : ℂ) (t : ℝ≥0) : ℂ :=
  (1 - q * (Complex.ofReal ((t : ℝ) ^ 2)))⁻¹

def squaredResolventKernelDerivative (q : ℂ) (t : ℝ≥0) : ℂ :=
  (Complex.ofReal ((t : ℝ) ^ 2)) / (1 - q * (Complex.ofReal ((t : ℝ) ^ 2))) ^ 2

def squaredResolvent (ν : Measure ℝ≥0) (q : ℂ) : ℂ :=
  ∫ t, squaredResolventKernel q t ∂ν

theorem squared_resolvent_denominator_norm {q : ℂ} (hq : q.re < 0) (t : ℝ≥0) :
    1 ≤ ‖1 - q * (Complex.ofReal ((t : ℝ) ^ 2))‖ := by
  have hRe : 1 ≤ (1 - q * (Complex.ofReal ((t : ℝ) ^ 2))).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [sq_nonneg (t : ℝ)]
  exact hRe.trans (Complex.re_le_norm _)

theorem squared_resolvent_denominator_ne_zero {q : ℂ} (hq : q.re < 0) (t : ℝ≥0) :
    1 - q * (Complex.ofReal ((t : ℝ) ^ 2)) ≠ 0 := by
  have h := squared_resolvent_denominator_norm hq t
  intro he
  rw [he, norm_zero] at h
  norm_num at h

theorem squared_resolvent_kernel_norm {q : ℂ} (hq : q.re < 0) (t : ℝ≥0) :
    ‖squaredResolventKernel q t‖ ≤ 1 := by
  rw [squaredResolventKernel, norm_inv]
  simpa only [one_div, inv_one] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (squared_resolvent_denominator_norm hq t)

theorem squared_resolvent_kernel_derivative_norm {q : ℂ} (hq : q.re < 0)
    {R : ℝ} {t : ℝ≥0} (ht : (t : ℝ) ≤ R) :
    ‖squaredResolventKernelDerivative q t‖ ≤ R ^ 2 := by
  have hD := squared_resolvent_denominator_norm hq t
  have hD2 : 1 ≤ ‖1 - q * (Complex.ofReal ((t : ℝ) ^ 2))‖ ^ 2 := by nlinarith
  simp only [squaredResolventKernelDerivative, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  rw [sq_abs]
  calc
    _ ≤ (t : ℝ) ^ 2 := div_le_self (sq_nonneg _) hD2
    _ ≤ R ^ 2 := pow_le_pow_left₀ t.property ht 2

theorem squared_resolvent_kernel_measurable (q : ℂ) : Measurable (squaredResolventKernel q) := by
  unfold squaredResolventKernel
  fun_prop

theorem squared_resolvent_kernel_derivative_measurable (q : ℂ) :
    Measurable (squaredResolventKernelDerivative q) := by
  unfold squaredResolventKernelDerivative
  fun_prop

theorem squared_resolvent_kernel_hasDerivAt {q : ℂ} (hq : q.re < 0) (t : ℝ≥0) :
    HasDerivAt (fun p => squaredResolventKernel p t)
      (squaredResolventKernelDerivative q t) q := by
  have h := ((hasDerivAt_const q (1 : ℂ)).sub
    ((hasDerivAt_id q).mul_const (Complex.ofReal ((t : ℝ) ^ 2)))).inv
      (squared_resolvent_denominator_ne_zero hq t)
  simpa only [squaredResolventKernel, squaredResolventKernelDerivative,
    one_mul, zero_sub, neg_neg] using h

theorem squared_resolvent_kernel_integrable (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {q : ℂ} (hq : q.re < 0) : Integrable (squaredResolventKernel q) ν :=
  Integrable.of_bound (squared_resolvent_kernel_measurable q).aestronglyMeasurable 1
    (Eventually.of_forall (squared_resolvent_kernel_norm hq))

theorem squared_resolvent_hasDerivAt (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ∀ᵐ (t : ℝ≥0) ∂ν, (t : ℝ) ≤ R)
    {q : ℂ} (hq : q.re < 0) :
    HasDerivAt (squaredResolvent ν)
      (∫ t, squaredResolventKernelDerivative q t ∂ν) q := by
  have hs : {p : ℂ | p.re < 0} ∈ 𝓝 q :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hq
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := squaredResolventKernel) (F' := squaredResolventKernelDerivative)
    (bound := fun _ => R ^ 2) hs
    (Eventually.of_forall (fun p =>
      (squared_resolvent_kernel_measurable p).aestronglyMeasurable))
    (squared_resolvent_kernel_integrable ν hq)
    (squared_resolvent_kernel_derivative_measurable q).aestronglyMeasurable
    (hSupport.mono (fun t ht p hp => squared_resolvent_kernel_derivative_norm hp ht))
    (integrable_const _) (Eventually.of_forall (fun t p hp =>
      squared_resolvent_kernel_hasDerivAt hp t))).2

theorem squared_resolvent_analyticOnNhd (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ∀ᵐ (t : ℝ≥0) ∂ν, (t : ℝ) ≤ R) :
    AnalyticOnNhd ℂ (squaredResolvent ν) {q : ℂ | q.re < 0} := by
  have hDiff : DifferentiableOn ℂ (squaredResolvent ν) {q : ℂ | q.re < 0} :=
    fun q hq => (squared_resolvent_hasDerivAt ν R hSupport hq).differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd (isOpen_lt Complex.continuous_re continuous_const)

theorem gaussian_shifted_limit_support_ae (z : ℂ) :
    ∀ᵐ (t : ℝ≥0) ∂gaussianShiftedSingularLimit z, (t : ℝ) ≤ 128 + ‖z‖ := by
  rw [ae_iff]
  simpa only [not_le] using gaussian_shifted_limit_support z

theorem gaussian_shifted_squared_resolvent_analytic (z : ℂ) :
    AnalyticOnNhd ℂ (squaredResolvent (gaussianShiftedSingularLimit z))
      {q : ℂ | q.re < 0} :=
  squared_resolvent_analyticOnNhd (gaussianShiftedSingularLimit z) (128 + ‖z‖)
    (gaussian_shifted_limit_support_ae z)

end CircularLaw
