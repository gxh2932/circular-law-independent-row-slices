import CircularLaw.GaussianWordDerivative
import CircularLaw.ScalarShiftWordEvaluation
import CircularLaw.GaussianShiftedLimitProperties

/-!
# The actual shifted Gaussian limiting word functional

The finite scalar-shift expansion defines a functional on every ordered
direct/adjoint word. Its value is the limit of the actual normalized
Gaussian trace mean. The checked first-pair derivative gives its deformed
head identity, retaining all scalar factors and multiplicities. On Gram
words this functional gives the moments of the actual limiting singular
measure.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianShiftedWordMeanValue (z : ℂ) (w : List Bool) : ℂ :=
  ((scalarShiftWordExpansion z w).map
    (fun p => p.1 * (gaussianWordMeanCount p.2 : ℂ))).sum

def gaussianShiftedWordDerivativeValue (z : ℂ) (b : Bool) (w : List Bool) : ℂ :=
  ((scalarShiftWordExpansion z w).map (fun p => p.1 *
    ((gaussianWordDerivative b p.2).map
      (fun q => (gaussianWordMeanCount q.1 : ℂ) * gaussianWordMeanCount q.2)).sum)).sum

def gaussianShiftedWordComplexMean (n : ℕ) (z : ℂ) (w : List Bool) : ℂ :=
  ∫ x, (matrixAdjointWord (normalizedShiftedGaussianMatrix z x) w).trace / n
    ∂gaussianSquareMatrixLaw n

theorem gaussian_shifted_word_mean_value_nil (z : ℂ) :
    gaussianShiftedWordMeanValue z [] = 1 := by
  simp [gaussianShiftedWordMeanValue, scalarShiftWordExpansion,
    gaussian_word_mean_count_nil]

theorem gaussian_shifted_word_mean_value_head (z : ℂ) (b : Bool) (w : List Bool) :
    gaussianShiftedWordMeanValue z (b :: w) =
      scalarShiftWordFactor z b * gaussianShiftedWordMeanValue z w +
        gaussianShiftedWordDerivativeValue z b w := by
  simp only [gaussianShiftedWordMeanValue, gaussianShiftedWordDerivativeValue,
    scalarShiftWordExpansion, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, gaussian_word_mean_count_derivative, mul_assoc]
  rw [List.sum_map_mul_left]
  exact add_comm _ _

theorem gaussian_shifted_word_derivative_value_sum (z : ℂ) (b : Bool) (w : List Bool) :
    gaussianShiftedWordDerivativeValue z b w =
      ∑ q : Fin w.length, if w.get q ≠ b then
        gaussianShiftedWordMeanValue z (w.take q.val) *
          gaussianShiftedWordMeanValue z (w.drop (q.val + 1)) else 0 := by
  have hPair (u v : List Bool) :
      scalarShiftPairEvaluate z u v
        (fun p => (gaussianWordMeanCount p.1 : ℂ) * gaussianWordMeanCount p.2) =
      gaussianShiftedWordMeanValue z u * gaussianShiftedWordMeanValue z v :=
    scalar_shift_pair_evaluate_product z u v
      (fun l => (gaussianWordMeanCount l : ℂ)) (fun l => (gaussianWordMeanCount l : ℂ))
  simpa only [hPair] using
    scalar_shift_word_derivative_evaluate_sum z b w
      (fun p => (gaussianWordMeanCount p.1 : ℂ) * gaussianWordMeanCount p.2)

theorem gaussian_shifted_word_mean_value_first_sum (z : ℂ) (b : Bool) (w : List Bool) :
    gaussianShiftedWordMeanValue z (b :: w) =
      scalarShiftWordFactor z b * gaussianShiftedWordMeanValue z w +
        ∑ q : Fin w.length, if w.get q ≠ b then
          gaussianShiftedWordMeanValue z (w.take q.val) *
            gaussianShiftedWordMeanValue z (w.drop (q.val + 1)) else 0 := by
  rw [gaussian_shifted_word_mean_value_head, gaussian_shifted_word_derivative_value_sum]

theorem gaussian_shifted_word_mean_value_map_not_real (r : ℝ) (w : List Bool) :
    gaussianShiftedWordMeanValue (r : ℂ) (w.map Bool.not) =
      gaussianShiftedWordMeanValue (r : ℂ) w := by
  change scalarShiftWordEvaluate (r : ℂ) (w.map Bool.not)
    (fun u => (gaussianWordMeanCount u : ℂ)) =
      scalarShiftWordEvaluate (r : ℂ) w (fun u => (gaussianWordMeanCount u : ℂ))
  rw [scalar_shift_word_evaluate_map_not_real]
  simp only [gaussian_word_mean_count_eq_noncrossing_word_count,
    gaussian_noncrossing_word_count_map_not]

theorem gaussian_shifted_word_mean_value_gram (z : ℂ) (k : ℕ) :
    gaussianShiftedWordMeanValue z (gramMatrixWord k) =
      gaussianShiftedMomentMeanLimit z k := rfl

theorem gaussian_shifted_word_mean_value_even_moment (z : ℂ) (k : ℕ) :
    ∫ t, (t : ℝ) ^ (2 * k) ∂gaussianShiftedSingularLimit z =
      (gaussianShiftedWordMeanValue z (gramMatrixWord k)).re := by
  rw [gaussian_shifted_limit_even_moments]
  rfl

theorem gaussian_shifted_word_trace_expansion {n : ℕ} (z : ℂ) (w : List Bool)
    (x : GaussianSquareSample n) :
    (matrixAdjointWord (normalizedShiftedGaussianMatrix z x) w).trace =
      ((scalarShiftWordExpansion z w).map (fun p => p.1 *
        (gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ p.2 x).trace)).sum := by
  rw [normalizedShiftedGaussianMatrix, ← matrix_scalar_shifted_word_eq,
    matrix_scalar_shifted_word_expansion, Matrix.trace_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, Matrix.trace_smul, smul_eq_mul,
    gaussian_scaled_matrix_word_eq_adjoint_word]

theorem gaussian_shifted_normalized_word_trace_expansion {n : ℕ} (z : ℂ) (w : List Bool)
    (x : GaussianSquareSample n) :
    (matrixAdjointWord (normalizedShiftedGaussianMatrix z x) w).trace / n =
      ((scalarShiftWordExpansion z w).map (fun p => p.1 *
        ((gaussianScaledMatrixWord (Real.sqrt (n : ℝ) : ℂ)⁻¹ p.2 x).trace / n))).sum := by
  rw [gaussian_shifted_word_trace_expansion]
  simp only [div_eq_mul_inv]
  rw [← List.sum_map_mul_right]
  simp only [mul_assoc]

theorem gaussian_shifted_word_complex_mean_eq_word_sum (n : ℕ) (z : ℂ) (w : List Bool) :
    gaussianShiftedWordComplexMean n z w =
      ((scalarShiftWordExpansion z w).map
        (fun p => p.1 * gaussianNormalizedWordComplexMean n p.2)).sum := by
  rw [gaussianShiftedWordComplexMean]
  simp only [gaussian_shifted_normalized_word_trace_expansion]
  rw [finite_list_sum_integral]
  · simp only [integral_const_mul, gaussianNormalizedWordComplexMean]
  · intro p _
    exact ((gaussian_scaled_matrix_word_trace_integrable n _ p.2).div_const (n : ℂ)).const_mul p.1

theorem gaussian_shifted_word_complex_mean_tendsto (z : ℂ) (w : List Bool) :
    Tendsto (fun n : ℕ => gaussianShiftedWordComplexMean n z w) atTop
      (𝓝 (gaussianShiftedWordMeanValue z w)) := by
  simp only [gaussian_shifted_word_complex_mean_eq_word_sum, gaussianShiftedWordMeanValue]
  exact finite_list_sum_tendsto _ _ _ atTop (fun p _ =>
    tendsto_const_nhds.mul (gaussian_word_mean_count_tendsto p.2))

end CircularLaw
