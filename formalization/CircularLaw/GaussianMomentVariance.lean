import CircularLaw.GaussianTwoTracePairings
import CircularLaw.GaussianSeparatePairings
import CircularLaw.GaussianMomentMeanLimits

/-!
# Actual all-order zero-shift Gaussian moment variances

The normalized even singular moment is the raw Gram trace divided by
`n^(order+1)`. Separate two-trace matchings give the squared mean exactly,
so its centered square expectation is the connected-pairing sum. The
proved exponent loss gives variance at most `(2*order)!/n`.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

def gaussianZeroShiftSingularMoment {n : ℕ} (k : ℕ) (x : GaussianSquareSample n) : ℝ :=
  ∫ t, (t : ℝ) ^ (2 * (k + 1)) ∂gaussianSingularMeasure 0 x

theorem gaussian_zero_shift_moment_eq_raw_trace {n : ℕ} (k : ℕ)
    (x : GaussianSquareSample n) :
    gaussianZeroShiftSingularMoment k x =
      ((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ (k + 1)).trace.re /
        (n : ℝ) ^ (k + 2) := by
  simp only [gaussianZeroShiftSingularMoment, gaussianSingularMeasure,
    normalizedShiftedGaussianMatrix, zero_smul, sub_zero]
  rw [square_singular_measure_even_moment, square_gram_trace_pow_smul]
  rw [pow_mul, inverse_sqrt_dimension_norm_sq]
  simp only [div_eq_mul_inv, pow_succ]
  ring

theorem gaussian_zero_shift_moment_integrable (n k : ℕ) :
    Integrable (gaussianZeroShiftSingularMoment (n := n) k) (gaussianSquareMatrixLaw n) := by
  change Integrable (fun x => gaussianZeroShiftSingularMoment (n := n) k x) _
  simp only [gaussian_zero_shift_moment_eq_raw_trace]
  exact (gaussian_gram_trace_pow_pairing_integrable n k).re.div_const _

theorem gaussian_zero_shift_moment_square_integrable (n k : ℕ) :
    Integrable (fun x => (gaussianZeroShiftSingularMoment (n := n) k x) ^ 2)
      (gaussianSquareMatrixLaw n) := by
  simp only [gaussian_zero_shift_moment_eq_raw_trace, div_pow]
  exact (gaussian_gram_trace_square_pairing_real_integrable n k).div_const _

theorem gaussian_zero_shift_moment_square_cycle_integral (n k : ℕ) :
    (∫ x, (gaussianZeroShiftSingularMoment k x) ^ 2 ∂gaussianSquareMatrixLaw n) =
      (∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
        (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ) / (n : ℝ) ^ (2 * (k + 1) + 2) := by
  simp only [gaussian_zero_shift_moment_eq_raw_trace, div_pow]
  rw [integral_div, gaussian_gram_trace_square_cycle_real_integral, ← pow_mul]
  congr 2
  omega

theorem gaussian_zero_shift_moment_square_integral (n k : ℕ) :
    (∫ x, (gaussianZeroShiftSingularMoment k x) ^ 2 ∂gaussianSquareMatrixLaw n) =
      (gaussianZeroShiftSingularMomentMean n k) ^ 2 + gaussianTwoTraceMixedContribution n k := by
  rw [gaussian_zero_shift_moment_square_cycle_integral, gaussian_two_trace_cycle_sum_split, add_div]
  congr 1
  · rw [gaussianZeroShiftSingularMomentMean, gaussian_zero_shift_singular_moment_cycle_integral,
      div_pow, ← pow_mul]
    congr 2
    omega
  · rw [gaussianTwoTraceMixedContribution, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp only [zero_div]

theorem integral_centered_square_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hfSq : Integrable (fun x => f x ^ 2) μ) (m : ℝ) :
    (∫ x, (f x - m) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - 2 * m * (∫ x, f x ∂μ) + m ^ 2 := by
  have hEq : (fun x => (f x - m) ^ 2) = fun x => f x ^ 2 - 2 * m * f x + m ^ 2 := by
    funext x
    ring
  have hSub : Integrable (fun x => f x ^ 2 - 2 * m * f x) μ :=
    hfSq.sub (hf.const_mul (2 * m))
  rw [hEq, integral_add hSub (integrable_const _),
    integral_sub hfSq (hf.const_mul (2 * m)), integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]

theorem gaussian_zero_shift_moment_centered_square_integrable (n k : ℕ) (m : ℝ) :
    Integrable (fun x => (gaussianZeroShiftSingularMoment k x - m) ^ 2)
      (gaussianSquareMatrixLaw n) := by
  have hEq : (fun x => (gaussianZeroShiftSingularMoment (n := n) k x - m) ^ 2) =
      fun x => gaussianZeroShiftSingularMoment k x ^ 2 -
        2 * m * gaussianZeroShiftSingularMoment k x + m ^ 2 := by
    funext x
    ring
  rw [hEq]
  exact ((gaussian_zero_shift_moment_square_integrable n k).sub
    ((gaussian_zero_shift_moment_integrable n k).const_mul _)).add (integrable_const _)

theorem gaussian_zero_shift_moment_centered_square_integral (n k : ℕ) :
    (∫ x, (gaussianZeroShiftSingularMoment k x - gaussianZeroShiftSingularMomentMean n k) ^ 2
      ∂gaussianSquareMatrixLaw n) = gaussianTwoTraceMixedContribution n k := by
  rw [integral_centered_square_real _ _ (gaussian_zero_shift_moment_integrable n k)
    (gaussian_zero_shift_moment_square_integrable n k), gaussian_zero_shift_moment_square_integral]
  change gaussianZeroShiftSingularMomentMean n k ^ 2 + gaussianTwoTraceMixedContribution n k -
    2 * gaussianZeroShiftSingularMomentMean n k * gaussianZeroShiftSingularMomentMean n k +
      gaussianZeroShiftSingularMomentMean n k ^ 2 = _
  ring

theorem gaussian_zero_shift_moment_variance_bound {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (∫ x, (gaussianZeroShiftSingularMoment k x - gaussianZeroShiftSingularMomentMean n k) ^ 2
      ∂gaussianSquareMatrixLaw n) ≤ ((2 * (k + 1)).factorial : ℝ) / n := by
  rw [gaussian_zero_shift_moment_centered_square_integral]
  exact gaussian_two_trace_mixed_contribution_bound hn k

end CircularLaw
