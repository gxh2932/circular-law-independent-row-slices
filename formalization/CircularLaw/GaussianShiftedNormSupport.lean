import CircularLaw.GaussianMatrixNorm
import CircularLaw.ComplexMatrixOperatorBounds

/-!
# Every shifted Gaussian singular value is uniformly bounded with high probability

Euclidean operator scaling and the actual shift give the radius
`128+norm(z)`. The probability that the shifted operator, or any actual
ordered singular value, exceeds it is at most `exp(-36*n)`.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem complex_matrix_operator_sqrt_normalization_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖complexMatrixOperator ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • A)‖ =
      ‖complexMatrixOperator A‖ / Real.sqrt (n : ℝ) := by
  rw [complex_matrix_operator_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

theorem gaussian_shifted_operator_norm_le {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) :
    ‖complexMatrixOperator (normalizedShiftedGaussianMatrix z x)‖ ≤
      ‖complexMatrixOperator (gaussianSquareMatrix x)‖ / Real.sqrt (n : ℝ) + ‖z‖ := by
  exact (complex_matrix_operator_shift_norm_le _ z).trans_eq
    (congrArg (fun t : ℝ => t + ‖z‖) (complex_matrix_operator_sqrt_normalization_norm _))

theorem gaussian_shifted_operator_norm_bound_on_raw_event {n : ℕ} (hn : 0 < n)
    (z : ℂ) (x : GaussianSquareSample n)
    (hRaw : ‖complexMatrixOperator (gaussianSquareMatrix x)‖ ≤ 128 * Real.sqrt (n : ℝ)) :
    ‖complexMatrixOperator (normalizedShiftedGaussianMatrix z x)‖ ≤ 128 + ‖z‖ := by
  have hRoot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  exact (gaussian_shifted_operator_norm_le z x).trans
    (add_le_add ((div_le_iff₀ hRoot).mpr hRaw) le_rfl)

theorem gaussian_shifted_operator_norm_tail {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (gaussianSquareMatrixLaw n).real
      {x | 128 + ‖z‖ < ‖complexMatrixOperator (normalizedShiftedGaussianMatrix z x)‖} ≤
        Real.exp (-36 * (n : ℝ)) := by
  apply (measureReal_mono (μ := gaussianSquareMatrixLaw n) (s₂ :=
    {x | 128 * Real.sqrt (n : ℝ) < ‖complexMatrixOperator (gaussianSquareMatrix x)‖}) ?_
    (measure_ne_top _ _)).trans (gaussian_matrix_operator_norm_tail hn)
  intro x hx
  by_contra h
  exact not_lt_of_ge (gaussian_shifted_operator_norm_bound_on_raw_event hn z x (le_of_not_gt h)) hx

theorem gaussian_shifted_singular_value_tail {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j, 128 + ‖z‖ < orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j} ≤
        Real.exp (-36 * (n : ℝ)) := by
  apply (measureReal_mono (μ := gaussianSquareMatrixLaw n) (s₂ :=
    {x | 128 + ‖z‖ < ‖complexMatrixOperator (normalizedShiftedGaussianMatrix z x)‖}) ?_
    (measure_ne_top _ _)).trans (gaussian_shifted_operator_norm_tail hn z)
  rintro x ⟨j, hj⟩
  exact hj.trans_le (ordered_square_singular_value_le_operator_norm _ j)

theorem gaussian_shifted_singular_value_bad_probability_tendsto (z : ℂ) :
    Tendsto (fun n : ℕ => (gaussianSquareMatrixLaw n).real
      {x | ∃ j, 128 + ‖z‖ < orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j})
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (gaussian_matrix_operator_norm_bad_probability_tendsto)
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro x ⟨j, hj⟩
  by_contra h
  have hBound := gaussian_shifted_operator_norm_bound_on_raw_event hn z x (le_of_not_gt h)
  exact not_lt_of_ge hBound (hj.trans_le (ordered_square_singular_value_le_operator_norm _ j))

end CircularLaw
