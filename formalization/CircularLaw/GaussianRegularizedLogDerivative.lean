import CircularLaw.HermitizedResolventDerivatives
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivative of the actual Gaussian regularized logarithmic integral

Compact support makes the logarithmic kernel integrable at each positive
regularization. A uniform bound on its derivative justifies differentiating
the actual limiting-measure integral. The explicit Dyson expression has
the same derivative, with no assumption on its logarithmic value.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

def regularizedSingularLogKernel (t : ℝ) (s : ℝ≥0) : ℝ :=
  (1 / 2 : ℝ) * Real.log (t ^ 2 + (s : ℝ) ^ 2)

def gaussianRegularizedLog (r t : ℝ) : ℝ :=
  ∫ s, regularizedSingularLogKernel t s ∂gaussianShiftedSingularLimit (r : ℂ)

def gaussianRegularizedLogFormula (r t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2) -
    (1 / 2 : ℝ) * gaussianHermitizedResolvent r t ^ 2

theorem regularized_singular_log_kernel_measurable (t : ℝ) :
    Measurable (regularizedSingularLogKernel t) := by
  unfold regularizedSingularLogKernel
  fun_prop

theorem regularized_singular_log_kernel_bound {t : ℝ} (ht : 0 < t)
    {R : ℝ} {s : ℝ≥0} (hs : (s : ℝ) ≤ R) :
    ‖regularizedSingularLogKernel t s‖ ≤
      (|Real.log (t ^ 2)| + |Real.log (t ^ 2 + R ^ 2)|) / 2 := by
  have hLo : Real.log (t ^ 2) ≤ Real.log (t ^ 2 + (s : ℝ) ^ 2) :=
    Real.log_le_log (sq_pos_of_pos ht) (by nlinarith [sq_nonneg (s : ℝ)])
  have hHi : Real.log (t ^ 2 + (s : ℝ) ^ 2) ≤ Real.log (t ^ 2 + R ^ 2) :=
    Real.log_le_log (by positivity) (by
      have hPow := pow_le_pow_left₀ s.property hs 2
      simpa only [add_comm] using add_le_add_left hPow (t ^ 2))
  have hAbs : |Real.log (t ^ 2 + (s : ℝ) ^ 2)| ≤
      |Real.log (t ^ 2)| + |Real.log (t ^ 2 + R ^ 2)| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log (t ^ 2)), abs_nonneg (Real.log (t ^ 2 + R ^ 2))]
    · linarith [le_abs_self (Real.log (t ^ 2 + R ^ 2)), abs_nonneg (Real.log (t ^ 2))]
  simp only [regularizedSingularLogKernel, Real.norm_eq_abs, abs_mul]
  norm_num only [abs_div, abs_one] at *
  linarith

theorem regularized_singular_log_kernel_integrable (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ∀ᵐ (s : ℝ≥0) ∂ν, (s : ℝ) ≤ R)
    {t : ℝ} (ht : 0 < t) : Integrable (regularizedSingularLogKernel t) ν :=
  Integrable.of_bound (regularized_singular_log_kernel_measurable t).aestronglyMeasurable
    ((|Real.log (t ^ 2)| + |Real.log (t ^ 2 + R ^ 2)|) / 2)
    (hSupport.mono (fun _ hs => regularized_singular_log_kernel_bound ht hs))

theorem regularized_singular_log_kernel_hasDerivAt {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    HasDerivAt (fun u => regularizedSingularLogKernel u s) (hermitizedResolventKernel t s) t := by
  have h := ((((hasDerivAt_id t).pow 2).add_const ((s : ℝ) ^ 2)).log
    (by positivity : t ^ 2 + (s : ℝ) ^ 2 ≠ 0)).const_mul (1 / 2 : ℝ)
  convert h using 1
  dsimp [hermitizedResolventKernel]
  ring

theorem regularized_log_integral_hasDerivAt (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ∀ᵐ (s : ℝ≥0) ∂ν, (s : ℝ) ≤ R)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∫ s, regularizedSingularLogKernel u s ∂ν)
      (∫ s, hermitizedResolventKernel t s ∂ν) t := by
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hBound (s : ℝ≥0) (u : ℝ) (hu : t / 2 < u) :
      ‖hermitizedResolventKernel u s‖ ≤ 2 / t := by
    have hu0 : 0 < u := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (hermitized_resolvent_kernel_pos hu0 s)]
    calc
      _ ≤ 1 / u := hermitized_resolvent_kernel_bound hu0 s
      _ ≤ 2 / t := (div_le_div_iff₀ hu0 ht).2 (by linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := regularizedSingularLogKernel) (F' := hermitizedResolventKernel)
    (bound := fun _ => 2 / t) hs
    (Eventually.of_forall (fun u =>
      (regularized_singular_log_kernel_measurable u).aestronglyMeasurable))
    (regularized_singular_log_kernel_integrable ν R hSupport ht)
    (hermitized_resolvent_kernel_measurable t).aestronglyMeasurable
    (Eventually.of_forall hBound) (integrable_const _)
    (Eventually.of_forall (fun s u hu =>
      regularized_singular_log_kernel_hasDerivAt (by linarith [show t / 2 < u from hu]) s))).2

theorem gaussian_regularized_log_hasDerivAt (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianRegularizedLog r) (gaussianHermitizedResolvent r t) t :=
  regularized_log_integral_hasDerivAt (gaussianShiftedSingularLimit (r : ℂ))
    (128 + ‖(r : ℂ)‖) (gaussian_shifted_limit_support_ae (r : ℂ)) ht

theorem gaussian_regularized_log_formula_hasDerivAt (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianRegularizedLogFormula r) (gaussianHermitizedResolvent r t) t := by
  let g := gaussianHermitizedResolvent r t
  let g' := ∫ s, hermitizedResolventKernelDerivative t s ∂gaussianShiftedSingularLimit (r : ℂ)
  let u := t + g
  let D := u ^ 2 + r ^ 2
  have hG : HasDerivAt (gaussianHermitizedResolvent r) g' t :=
    gaussian_hermitized_resolvent_hasDerivAt r ht
  have hDen : 0 < D := by
    have hU : 0 < u := add_pos ht (gaussian_hermitized_resolvent_pos r ht)
    dsimp [D]
    positivity
  have hD := (((hasDerivAt_id t).add hG).pow 2).add_const (r ^ 2)
  have hLog := (hD.log (ne_of_gt hDen)).const_mul (1 / 2 : ℝ)
  have hSquare := (hG.pow 2).const_mul (1 / 2 : ℝ)
  have hDyson : u / D = g := (gaussian_hermitized_resolvent_dyson r ht).symm
  have hEq : (1 / 2 : ℝ) * (2 * u * (1 + g') / D) - (1 / 2 : ℝ) * (2 * g * g') = g := by
    calc
      _ = (u / D) * (1 + g') - g * g' := by ring
      _ = g := by rw [hDyson]; ring
  convert hLog.sub hSquare using 1
  dsimp only
  norm_num only
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, pow_one]
  exact hEq.symm

end CircularLaw
