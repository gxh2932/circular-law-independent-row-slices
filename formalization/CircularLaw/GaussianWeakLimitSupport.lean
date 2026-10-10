import CircularLaw.GaussianShiftedNormSupport
import CircularLaw.VaryingProbabilityUnique
import CircularLaw.VaryingProbabilitySqueeze
import CircularLaw.EmpiricalWeakConvergence

/-!
# Any actual shifted Gaussian weak limit inherits the proved support bound

The finite matrix norm estimate makes every bounded test vanishing below
`128+norm(z)` converge to zero in probability. Uniqueness of deterministic
probability limits identifies its weak-limit integral as zero. A positive
continuous upper cutoff then shows that the limiting law has no mass
above the radius. Weak convergence itself is an explicit, unproved input.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal BigOperators Topology

namespace CircularLaw

theorem gaussian_shifted_weak_limit_test_zero (z : ℂ) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν)
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (hBound : ∃ C : ℝ, ∀ t, |f t| ≤ C)
    (hZero : ∀ t : ℝ≥0, (t : ℝ) ≤ 128 + ‖z‖ → f t = 0) :
    (∫ t, f t ∂ν) = 0 := by
  have hConst : VaryingConvergesInProbability gaussianSquareMatrixLaw (fun _ _ => (0 : ℝ)) 0 := by
    intro ε hε
    simpa only [sub_self, abs_zero, not_lt_of_ge hε.le, Set.setOf_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hZeroLimit : VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) f) 0 := by
    apply varying_probability_of_agreement_outside_bad_event gaussianSquareMatrixLaw
      (fun n => {x | 128 * Real.sqrt (n : ℝ) < ‖complexMatrixOperator (gaussianSquareMatrix x)‖})
      hConst gaussian_matrix_operator_norm_bad_probability_tendsto
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro x hx
    have hOp := gaussian_shifted_operator_norm_bound_on_raw_event hn z x (le_of_not_gt hx)
    have hEntries (j : Fin n) : f (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j) = 0 :=
      hZero _ ((ordered_square_singular_value_le_operator_norm _ j).trans hOp)
    simp only [empiricalNonnegativeMean, finiteMean, hEntries, Finset.sum_const_zero, zero_div]
  exact varying_probability_limit_unique gaussianSquareMatrixLaw (hWeak f hf hBound) hZeroLimit

def upperSupportCutoff (R : ℝ) (t : ℝ≥0) : ℝ := min 1 (max 0 ((t : ℝ) - R))

theorem continuous_upper_support_cutoff (R : ℝ) : Continuous (upperSupportCutoff R) :=
  continuous_const.min (continuous_const.max (NNReal.continuous_coe.sub continuous_const))

theorem upper_support_cutoff_bounds (R : ℝ) (t : ℝ≥0) :
    0 ≤ upperSupportCutoff R t ∧ upperSupportCutoff R t ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem upper_support_cutoff_zero {R : ℝ} {t : ℝ≥0} (ht : (t : ℝ) ≤ R) :
    upperSupportCutoff R t = 0 := by
  rw [upperSupportCutoff, max_eq_left (sub_nonpos.mpr ht), min_eq_right zero_le_one]

theorem upper_support_cutoff_ne_zero_iff (R : ℝ) (t : ℝ≥0) :
    upperSupportCutoff R t ≠ 0 ↔ R < (t : ℝ) := by
  constructor
  · intro h
    by_contra ht
    exact h (upper_support_cutoff_zero (le_of_not_gt ht))
  · intro ht
    exact (lt_min zero_lt_one ((sub_pos.mpr ht).trans_le (le_max_right _ _))).ne'

theorem upper_support_cutoff_integrable (R : ℝ) (ν : Measure ℝ≥0) [IsFiniteMeasure ν] :
    Integrable (upperSupportCutoff R) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_upper_support_cutoff R).measurable.aestronglyMeasurable
  exact ae_of_all ν (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (upper_support_cutoff_bounds R t).1]
    exact (upper_support_cutoff_bounds R t).2)

theorem gaussian_shifted_weak_limit_support (z : ℂ) (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν) :
    ν {t : ℝ≥0 | 128 + ‖z‖ < (t : ℝ)} = 0 := by
  let R := 128 + ‖z‖
  have hBound : ∃ C : ℝ, ∀ t, |upperSupportCutoff R t| ≤ C := by
    refine ⟨1, fun t => ?_⟩
    rw [abs_of_nonneg (upper_support_cutoff_bounds R t).1]
    exact (upper_support_cutoff_bounds R t).2
  have hIntegral : (∫ t, upperSupportCutoff R t ∂ν) = 0 :=
    gaussian_shifted_weak_limit_test_zero z ν hWeak _ (continuous_upper_support_cutoff R)
      hBound
      (fun _ ht => upper_support_cutoff_zero ht)
  have hAe := (integral_eq_zero_iff_of_nonneg (fun t => (upper_support_cutoff_bounds R t).1)
    (upper_support_cutoff_integrable R ν)).mp hIntegral
  change ∀ᵐ t ∂ν, upperSupportCutoff R t = 0 at hAe
  rw [ae_iff] at hAe
  simpa only [Pi.zero_apply, upper_support_cutoff_ne_zero_iff] using hAe

end CircularLaw
