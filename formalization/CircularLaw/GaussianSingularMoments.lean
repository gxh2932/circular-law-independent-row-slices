import CircularLaw.GaussianGramTraceMoments
import CircularLaw.SquareSingularTraceMoments

/-!
# Actual Gaussian singular moments and probability bounds

The shifted second moment has mean `1+|z|^2` and is bounded in
probability under the actual varying Gaussian laws. At zero shift the
normalized fourth singular moment has exact expectation two at every
positive dimension. These calculations do not establish weak convergence.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

theorem square_gram_trace_pow_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) :
    (((c • A) * (c • A).conjTranspose) ^ k).trace.re =
      ‖c‖ ^ (2 * k) * ((A * A.conjTranspose) ^ k).trace.re := by
  have hGram : (c • A) * (c • A).conjTranspose =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (A * A.conjTranspose) := by
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    simpa using complex_balanced_power_eq_norm_power c 1
  rw [hGram, smul_pow, Matrix.trace_smul, smul_eq_mul]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, pow_mul]

theorem gaussian_singular_second_moment_nonneg {n : ℕ} (z : ℂ)
    (x : GaussianSquareSample n) : 0 ≤ gaussianSingularSecondMoment z x :=
  squareSingularMeasure_second_moment_nonneg _

theorem gaussian_singular_second_moment_tail_bound {n : ℕ} (hn : 0 < n) (z : ℂ)
    {M : ℝ} (hM : 0 < M) :
    (gaussianSquareMatrixLaw n).real {x | M < |gaussianSingularSecondMoment z x|} ≤
      (1 + ‖z‖ ^ 2) / M := by
  let μ := gaussianSquareMatrixLaw n
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (gaussian_singular_second_moment_nonneg z))
    (gaussian_singular_second_moment_integrable n z) M
  have hSubset : {x : GaussianSquareSample n | M < |gaussianSingularSecondMoment z x|} ⊆
      {x | M ≤ gaussianSingularSecondMoment z x} := by
    intro x hx
    change M < |gaussianSingularSecondMoment z x| at hx
    change M ≤ gaussianSingularSecondMoment z x
    simpa only [abs_of_nonneg (gaussian_singular_second_moment_nonneg z x)] using hx.le
  apply (le_div_iff₀ hM).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset) hM.le).trans
    (hMark.trans_eq (gaussian_singular_second_moment_integral hn z))

theorem gaussian_second_moment_bounded_in_probability (z : ℂ) :
    VaryingBoundedInProbability gaussianSquareMatrixLaw (fun _ => gaussianSingularSecondMoment z) := by
  intro δ hδ
  let C : ℝ := 1 + ‖z‖ ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let M : ℝ := C / δ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply (gaussian_singular_second_moment_tail_bound hn z hM).trans_lt
  change C / M < δ
  apply (div_lt_iff₀ hM).mpr
  dsimp [M]
  rw [mul_add, mul_div_cancel₀ C hδ.ne', mul_one]
  linarith

theorem gaussian_normalized_energy_bounded_in_probability :
    VaryingBoundedInProbability gaussianSquareMatrixLaw
      (fun n x => squareMatrixEnergy (normalizedShiftedGaussianMatrix 0 x) / n) := by
  have hEq : (fun n : ℕ => gaussianSingularSecondMoment (n := n) 0) =
      fun (n : ℕ) (x : GaussianSquareSample n) =>
        squareMatrixEnergy (normalizedShiftedGaussianMatrix 0 x) / (n : ℝ) := by
    funext n x
    exact gaussian_singular_second_moment_eq 0 x
  rw [← hEq]
  exact gaussian_second_moment_bounded_in_probability 0

theorem gaussian_singular_fourth_moment_eq_raw_trace {n : ℕ} (x : GaussianSquareSample n) :
    (∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure 0 x) =
      (((gaussianSquareMatrix x * (gaussianSquareMatrix x).conjTranspose) ^ 2).trace).re /
        (n : ℝ) ^ 3 := by
  have hMoment := square_singular_measure_even_moment
    ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x) 2
  norm_num only [Nat.reduceMul] at hMoment
  change (∫ t, (t : ℝ) ^ 4 ∂squareSingularMeasure
    ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x - (0 : ℂ) • 1)) = _
  rw [zero_smul, sub_zero, hMoment, square_gram_trace_pow_smul]
  rw [pow_mul, inverse_sqrt_dimension_norm_sq]
  simp only [div_eq_mul_inv, one_mul, inv_pow]
  ring

theorem gaussian_singular_fourth_moment_integrable (n : ℕ) :
    Integrable (fun x => ∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure 0 x)
      (gaussianSquareMatrixLaw n) := by
  simp only [gaussian_singular_fourth_moment_eq_raw_trace]
  exact (gaussian_gram_trace_square_real_integrable n).div_const _

theorem gaussian_singular_fourth_moment_integral {n : ℕ} (hn : 0 < n) :
    (∫ x, (∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure 0 x) ∂gaussianSquareMatrixLaw n) = 2 := by
  simp only [gaussian_singular_fourth_moment_eq_raw_trace]
  rw [integral_div, gaussian_gram_trace_square_real_integral]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end CircularLaw
