import CircularLaw.BernoulliMatrixWordMeans
import CircularLaw.FiniteListIntegralLimits

/-!
# Sparse normalization and centering of actual Bernoulli word means

The actual centered matrix is the Boolean matrix minus its deterministic
constant-entry mean. Real scalar normalization preserves direct/adjoint
word order and supplies one factor per position. Exact normalized trace
integrals retain dimension, degree, every walk and every multiplicity.
The scalar-shift expansion also holds for the actual centered shifted
Gram powers. No moment limit or Bernoulli weak convergence is assumed.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

local instance bernoulliNormalizedWordBEq (n : ℕ) : BEq (Fin n × Fin n) := instBEqOfDecidableEq

theorem matrix_adjoint_word_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (w : List Bool) :
    matrixAdjointWord (c • A) w = gaussianMatrixWordScale c w • matrixAdjointWord A w := by
  induction w with
  | nil => simp [matrixAdjointWord, gaussianMatrixWordScale]
  | cons b w ih =>
    cases b <;>
      simp only [matrixAdjointWord, List.map_cons, List.prod_cons,
        gaussianMatrixWordScale, Bool.false_eq_true, if_false, if_true,
        Matrix.conjTranspose_smul] at ih ⊢
    · rw [ih, smul_mul_assoc, mul_smul_comm, smul_smul]
    · rw [ih, smul_mul_assoc, mul_smul_comm, smul_smul]

theorem matrix_word_scale_ofReal (c : ℝ) (w : List Bool) :
    gaussianMatrixWordScale (c : ℂ) w = (c ^ w.length : ℝ) := by
  simp [gaussianMatrixWordScale]

theorem matrix_adjoint_word_trace_re_real_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℝ) (w : List Bool) :
    (matrixAdjointWord ((c : ℂ) • A) w).trace.re =
      c ^ w.length * (matrixAdjointWord A w).trace.re := by
  rw [matrix_adjoint_word_smul, matrix_word_scale_ofReal, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

def bernoulliSquareMeanMatrix {n : ℕ} (p : ℝ≥0) : Matrix (Fin n) (Fin n) ℂ :=
  fun _ _ => (p : ℂ)

theorem bernoulli_centered_square_matrix_eq {n : ℕ} (p : ℝ≥0) (x : BernoulliSquareSample n) :
    bernoulliCenteredSquareMatrix p x = bernoulliSquareMatrix x - bernoulliSquareMeanMatrix p := by
  ext i j
  cases h : x (i, j) <;>
    simp [bernoulliCenteredSquareMatrix, bernoulliCenteredValue, bernoulliSquareMatrix,
      bernoulliSquareMeanMatrix, h]

def normalizedCenteredBernoulliMatrix {n : ℕ} (d : ℕ) (x : BernoulliSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (d : ℝ) : ℂ)⁻¹ • bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) x

theorem normalized_shifted_bernoulli_centered_decomposition {n : ℕ} (d : ℕ)
    (z : ℂ) (x : BernoulliSquareSample n) :
    normalizedShiftedBernoulliMatrix d z x = normalizedCenteredBernoulliMatrix d x - z • 1 +
      (Real.sqrt (d : ℝ) : ℂ)⁻¹ • bernoulliSquareMeanMatrix (rowBernoulliParameter n d) := by
  rw [normalizedCenteredBernoulliMatrix, bernoulli_centered_square_matrix_eq, smul_sub]
  unfold normalizedShiftedBernoulliMatrix
  abel

def bernoulliNormalizedWordMean (n d : ℕ) (w : List Bool) : ℝ :=
  ∫ x, (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace.re / n
    ∂sparseBernoulliMatrixLaw n d

theorem bernoulli_normalized_empty_word_mean {n : ℕ} (hn : 0 < n) (d : ℕ) :
    bernoulliNormalizedWordMean n d [] = 1 := by
  simp [bernoulliNormalizedWordMean, matrixAdjointWord, ne_of_gt hn]

theorem bernoulli_normalized_word_mean_formula {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (k : ℕ) (b : Fin (k + 1) → Bool) :
    bernoulliNormalizedWordMean n d (List.ofFn b) =
      ((Real.sqrt (d : ℝ))⁻¹ ^ (k + 1) / (n : ℝ)) *
        ∑ v : Fin (k + 1) → Fin n,
          ∏ e : Fin n × Fin n, bernoulliCenteredMoment (rowBernoulliParameter n d)
            (rowBernoulliParameter_le_one hn hdn) ((bernoulliWalkEntries b v).count e) := by
  unfold bernoulliNormalizedWordMean normalizedCenteredBernoulliMatrix
  simp_rw [← Complex.ofReal_inv, matrix_adjoint_word_trace_re_real_smul, List.length_ofFn]
  rw [integral_div, integral_const_mul, sparseBernoulliMatrixLaw_eq hn hdn,
    bernoulli_centered_matrix_word_trace_integral]
  ring

theorem bernoulli_centered_shifted_gram_trace_mean_expansion (n d : ℕ) (z : ℂ) (k : ℕ) :
    (∫ x, (((normalizedCenteredBernoulliMatrix d x - z • 1) *
        (normalizedCenteredBernoulliMatrix d x - z • 1).conjTranspose) ^ k).trace
      ∂sparseBernoulliMatrixLaw n d) =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map (fun q => q.1 *
        ∫ x, (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) q.2).trace
          ∂sparseBernoulliMatrixLaw n d)).sum := by
  have hPoint (x : BernoulliSquareSample n) :
      (((normalizedCenteredBernoulliMatrix d x - z • 1) *
        (normalizedCenteredBernoulliMatrix d x - z • 1).conjTranspose) ^ k).trace =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map (fun q => q.1 *
        (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) q.2).trace)).sum := by
    rw [matrix_shifted_gram_pow_word, matrix_scalar_shifted_word_expansion, Matrix.trace_list_sum]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, Matrix.trace_smul, smul_eq_mul]
  simp_rw [hPoint]
  rw [finite_list_sum_integral _ _ _ (fun _ _ => Integrable.of_finite)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  exact integral_const_mul q.1 _

end CircularLaw
