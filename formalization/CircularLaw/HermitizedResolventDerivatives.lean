import CircularLaw.GaussianHermitizedResolvent
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating the actual Hermitized resolvent

The derivative of t/(t^2+s^2) has absolute value at most 1/t^2 for
positive t. A fixed neighborhood of each positive parameter gives a
uniform integrable bound, so differentiation under every finite measure
is justified without assuming a derivative of its limiting moments.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

def hermitizedResolventKernelDerivative (t : ℝ) (s : ℝ≥0) : ℝ :=
  ((s : ℝ) ^ 2 - t ^ 2) / (t ^ 2 + (s : ℝ) ^ 2) ^ 2

theorem hermitized_resolvent_kernel_hasDerivAt {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    HasDerivAt (fun u => hermitizedResolventKernel u s)
      (hermitizedResolventKernelDerivative t s) t := by
  have h := (hasDerivAt_id t).div (((hasDerivAt_id t).pow 2).add_const ((s : ℝ) ^ 2))
    (by positivity : t ^ 2 + (s : ℝ) ^ 2 ≠ 0)
  convert h using 1
  dsimp [hermitizedResolventKernelDerivative]
  ring

theorem hermitized_resolvent_kernel_derivative_measurable (t : ℝ) :
    Measurable (hermitizedResolventKernelDerivative t) := by
  unfold hermitizedResolventKernelDerivative
  fun_prop

theorem hermitized_resolvent_kernel_derivative_bound {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    ‖hermitizedResolventKernelDerivative t s‖ ≤ 1 / t ^ 2 := by
  have hDen : 0 < t ^ 2 + (s : ℝ) ^ 2 := by positivity
  have hAbs : |(s : ℝ) ^ 2 - t ^ 2| ≤ (s : ℝ) ^ 2 + t ^ 2 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (s : ℝ)], by nlinarith [sq_nonneg t]⟩
  simp only [hermitizedResolventKernelDerivative, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_pos hDen]
  calc
    _ ≤ ((s : ℝ) ^ 2 + t ^ 2) / (t ^ 2 + (s : ℝ) ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hAbs (sq_nonneg _)
    _ = 1 / (t ^ 2 + (s : ℝ) ^ 2) := by field_simp; ring
    _ ≤ 1 / t ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos ht) (by nlinarith [sq_nonneg (s : ℝ)])

theorem hermitized_resolvent_kernel_derivative_local_bound {t u : ℝ}
    (ht : 0 < t) (hu : t / 2 < u) (s : ℝ≥0) :
    ‖hermitizedResolventKernelDerivative u s‖ ≤ 4 / t ^ 2 := by
  have hu0 : 0 < u := by linarith
  calc
    _ ≤ 1 / u ^ 2 := hermitized_resolvent_kernel_derivative_bound hu0 s
    _ ≤ 4 / t ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hu0) (sq_pos_of_pos ht)).2
      have htu : t ≤ 2 * u := by linarith
      have hPow := pow_le_pow_left₀ ht.le htu 2
      nlinarith

theorem hermitized_resolvent_integral_hasDerivAt (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∫ s, hermitizedResolventKernel u s ∂ν)
      (∫ s, hermitizedResolventKernelDerivative t s ∂ν) t := by
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := hermitizedResolventKernel) (F' := hermitizedResolventKernelDerivative)
    (bound := fun _ => 4 / t ^ 2) hs
    (Eventually.of_forall (fun u =>
      (hermitized_resolvent_kernel_measurable u).aestronglyMeasurable))
    (hermitized_resolvent_kernel_integrable ν ht)
    (hermitized_resolvent_kernel_derivative_measurable t).aestronglyMeasurable
    (Eventually.of_forall (fun s u hu =>
      hermitized_resolvent_kernel_derivative_local_bound ht hu s)) (integrable_const _)
    (Eventually.of_forall (fun s u hu =>
      hermitized_resolvent_kernel_hasDerivAt (by linarith [show t / 2 < u from hu]) s))).2

theorem gaussian_hermitized_resolvent_hasDerivAt (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianHermitizedResolvent r)
      (∫ s, hermitizedResolventKernelDerivative t s ∂gaussianShiftedSingularLimit (r : ℂ)) t :=
  hermitized_resolvent_integral_hasDerivAt (gaussianShiftedSingularLimit (r : ℂ)) ht

end CircularLaw
