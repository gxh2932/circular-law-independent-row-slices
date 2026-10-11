import CircularLaw.GaussianAlternatingCatalan
import CircularLaw.GaussianShiftedLimitProperties

/-!
# Actual zero-shift Gaussian singular moments are Catalan moments

The Gram word is the actual alternating position word. At zero shift the
finite scalar expansion contributes only the full retained word. The
checked Catalan count therefore identifies every moment of the actual
Gaussian singular limiting law and every actual moment probability limit.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_alternating_list_pair (n : ℕ) :
    List.ofFn (gaussianAlternatingWord (n + 2)) =
      false :: true :: List.ofFn (gaussianAlternatingWord n) := by
  rw [List.ofFn_succ, List.ofFn_succ]
  change false :: true :: List.ofFn
    (fun a : Fin n => gaussianAlternatingWord (n + 2) a.succ.succ) = _
  have hWord : (fun a : Fin n => gaussianAlternatingWord (n + 2) a.succ.succ) =
      gaussianAlternatingWord n := by
    funext a
    simp only [gaussianAlternatingWord, Fin.val_succ]
    have hMod : (a.val + 1 + 1) % 2 = a.val % 2 := by omega
    simp only [hMod]
  rw [hWord]

theorem gram_matrix_word_eq_alternating_ofFn (k : ℕ) :
    gramMatrixWord k = List.ofFn (gaussianAlternatingWord (2 * k)) := by
  induction k with
  | zero => simp only [gramMatrixWord, Nat.mul_zero, List.ofFn_zero]
  | succ k ih =>
    rw [gramMatrixWord, ih]
    have hSize : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hSize, gaussian_alternating_list_pair]

theorem gaussian_gram_word_mean_count_catalan (k : ℕ) :
    gaussianWordMeanCount (gramMatrixWord k) = catalan k := by
  rw [gram_matrix_word_eq_alternating_ofFn, gaussian_alternating_word_mean_count_catalan]

theorem scalar_shift_zero_expansion_weighted_sum (F : List Bool → ℂ) (w : List Bool) :
    ((scalarShiftWordExpansion 0 w).map (fun p => p.1 * F p.2)).sum = F w := by
  induction w generalizing F with
  | nil => simp [scalarShiftWordExpansion]
  | cons b w ih =>
    simp only [scalarShiftWordExpansion, List.map_append, List.sum_append, List.map_map]
    change ((scalarShiftWordExpansion 0 w).map (fun p => p.1 * F (b :: p.2))).sum +
      ((scalarShiftWordExpansion 0 w).map
        (fun p => (scalarShiftWordFactor 0 b * p.1) * F p.2)).sum = F (b :: w)
    have hZero : ((scalarShiftWordExpansion 0 w).map
        (fun p => (scalarShiftWordFactor 0 b * p.1) * F p.2)).sum = 0 := by
      simp [scalarShiftWordFactor]
    rw [hZero, add_zero]
    exact ih (fun v => F (b :: v))

theorem gaussian_zero_shift_moment_mean_limit_catalan (k : ℕ) :
    gaussianShiftedMomentMeanLimit 0 k = (catalan k : ℂ) := by
  rw [gaussianShiftedMomentMeanLimit,
    scalar_shift_zero_expansion_weighted_sum (fun w => (gaussianWordMeanCount w : ℂ)) (gramMatrixWord k),
    gaussian_gram_word_mean_count_catalan]

theorem gaussian_zero_shift_squared_moment_limit_catalan (k : ℕ) :
    gaussianShiftedSquaredMomentLimit 0 k = (catalan k : ℝ) := by
  rw [gaussianShiftedSquaredMomentLimit, gaussian_zero_shift_moment_mean_limit_catalan]
  rfl

theorem gaussian_zero_shift_moments_converge_to_catalan (k : ℕ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianShiftedSingularMoment 0 k) (catalan k : ℝ) := by
  simpa only [gaussian_zero_shift_moment_mean_limit_catalan, Complex.natCast_re] using
    gaussian_shifted_singular_moment_converges_in_probability 0 k

theorem gaussian_zero_shift_catalan_mean_square_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x,
      (gaussianShiftedSingularMoment 0 k x - (catalan k : ℝ)) ^ 2
      ∂gaussianSquareMatrixLaw n) atTop (𝓝 0) := by
  simpa only [gaussian_zero_shift_moment_mean_limit_catalan, Complex.natCast_re] using
    gaussian_shifted_singular_moment_mean_square_tendsto 0 k

theorem gaussian_zero_shift_limit_catalan_even_moments (k : ℕ) :
    (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianShiftedSingularLimit 0) = (catalan k : ℝ) := by
  rw [gaussian_shifted_limit_even_moments, gaussian_zero_shift_squared_moment_limit_catalan]

theorem gaussian_previous_zero_limit_catalan_even_moments (k : ℕ) :
    (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianZeroShiftSingularLimit) = (catalan k : ℝ) := by
  rw [← gaussian_shifted_limit_at_zero]
  exact gaussian_zero_shift_limit_catalan_even_moments k

theorem gaussian_leading_moment_count_catalan (k : ℕ) :
    gaussianLeadingMomentCount k = catalan (k + 1) := by
  have h := gaussian_zero_shift_moment_converges_in_probability k
  change VaryingConvergesInProbability gaussianSquareMatrixLaw
    (fun _ => gaussianShiftedSingularMoment 0 (k + 1)) (gaussianLeadingMomentCount k : ℝ) at h
  exact_mod_cast varying_probability_limit_unique gaussianSquareMatrixLaw h
    (gaussian_zero_shift_moments_converge_to_catalan (k + 1))

end CircularLaw
