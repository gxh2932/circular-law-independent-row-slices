import CircularLaw.GaussianMomentConvergence
import CircularLaw.GaussianShiftedNormSupport
import CircularLaw.VaryingProbabilityPolynomial

/-!
# All actual squared Gaussian singular moments converge

The zeroth moment is one at positive dimension. Higher moments are exactly
the previously checked even singular moments, with the exact leading
pairing counts as their limits. The norm estimate bounds every squared
singular value by `128^2`, except on an event whose probability vanishes.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def gaussianSquaredSingularValues {n : ℕ} (x : GaussianSquareSample n) (j : Fin n) : ℝ :=
  (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x) j : ℝ) ^ 2

def gaussianZeroShiftMomentLimit (m : ℕ) : ℝ :=
  if m = 0 then 1 else (gaussianLeadingMomentCount (m - 1) : ℝ)

theorem gaussian_zero_shift_moment_limit_zero : gaussianZeroShiftMomentLimit 0 = 1 := by
  simp [gaussianZeroShiftMomentLimit]

theorem gaussian_zero_shift_moment_limit_succ (k : ℕ) :
    gaussianZeroShiftMomentLimit (k + 1) = (gaussianLeadingMomentCount k : ℝ) := by
  simp [gaussianZeroShiftMomentLimit]

theorem gaussian_squared_singular_moment_eq {n : ℕ} (k : ℕ) (x : GaussianSquareSample n) :
    finiteMean (fun j => gaussianSquaredSingularValues x j ^ (k + 1)) =
      gaussianZeroShiftSingularMoment k x := by
  simp only [gaussianZeroShiftSingularMoment, gaussianSingularMeasure, squareSingularMeasure,
    empiricalNonnegativeMeasure_integral, empiricalNonnegativeMean, gaussianSquaredSingularValues, pow_mul]

theorem gaussian_squared_singular_moments_converge (m : ℕ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => finiteMean (fun j => gaussianSquaredSingularValues x j ^ m))
      (gaussianZeroShiftMomentLimit m) := by
  cases m with
  | zero =>
    rw [gaussian_zero_shift_moment_limit_zero]
    intro ε hε
    have hEq : ∀ᶠ n : ℕ in atTop,
        (gaussianSquareMatrixLaw n).real
          {x | ε < |finiteMean (fun j => gaussianSquaredSingularValues x j ^ 0) - 1|} = 0 := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      simp only [pow_zero, finiteMean_const, sub_self, abs_zero, not_lt_of_ge hε.le,
        Set.setOf_false, measureReal_empty]
    exact (tendsto_congr' hEq).mpr tendsto_const_nhds
  | succ k =>
    simp only [gaussian_zero_shift_moment_limit_succ, gaussian_squared_singular_moment_eq]
    exact gaussian_zero_shift_moment_converges_in_probability k

theorem gaussian_squared_singular_values_nonneg {n : ℕ} (x : GaussianSquareSample n)
    (j : Fin n) : 0 ≤ gaussianSquaredSingularValues x j := sq_nonneg _

theorem gaussian_squared_singular_value_bound_failure_tendsto :
    Tendsto (fun n : ℕ => (gaussianSquareMatrixLaw n).real
      {x | ∃ j, (128 : ℝ) ^ 2 < gaussianSquaredSingularValues x j}) atTop (𝓝 0) := by
  have hEq (n : ℕ) :
      {x : GaussianSquareSample n | ∃ j, (128 : ℝ) ^ 2 < gaussianSquaredSingularValues x j} =
      {x | ∃ j, 128 + ‖(0 : ℂ)‖ < orderedSquareSingularValues (normalizedShiftedGaussianMatrix 0 x) j} := by
    ext x
    simp only [gaussianSquaredSingularValues, norm_zero, add_zero,
      squareSingularValuesNNReal, NNReal.coe_mk]
    exact exists_congr (fun j => sq_lt_sq₀ (by norm_num) (orderedSquareSingularValues_nonneg _ j))
  simp only [hEq]
  exact gaussian_shifted_singular_value_bad_probability_tendsto 0

end CircularLaw
