import CircularLaw.BernoulliGaussianWordCounts
import CircularLaw.SparseRealPatternPowerLimits

/-!
# Actual Bernoulli word means with arbitrary entry probability

The dimension and Bernoulli probability are independent parameters.
Normalization uses the real effective degree n*p. No integer degree or
asymptotic assertion is assumed in the finite trace formulas.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

local instance parameterBernoulliPatternBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

def bernoulliEffectiveDegree (n : ℕ) (p : ℝ≥0) : ℝ := (n : ℝ) * p

def parameterNormalizedCenteredBernoulliMatrix {n : ℕ} (p : ℝ≥0)
    (x : BernoulliSquareSample n) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (bernoulliEffectiveDegree n p) : ℂ)⁻¹ • bernoulliCenteredSquareMatrix p x

def parameterBernoulliWordTrace {n : ℕ} (p : ℝ≥0) (w : List Bool)
    (x : BernoulliSquareSample n) : ℝ :=
  (matrixAdjointWord (parameterNormalizedCenteredBernoulliMatrix p x) w).trace.re / n

def parameterBernoulliWordMean (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (w : List Bool) : ℝ :=
  ∫ x, parameterBernoulliWordTrace p w x ∂bernoulliSquareMatrixLaw n p hp

theorem bernoulli_effective_degree_nonneg (n : ℕ) (p : ℝ≥0) :
    0 ≤ bernoulliEffectiveDegree n p := by
  unfold bernoulliEffectiveDegree
  positivity

theorem bernoulli_parameter_eq_effective_degree_div {n : ℕ} (hn : 0 < n) (p : ℝ≥0) :
    (p : ℝ) = bernoulliEffectiveDegree n p / n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [bernoulliEffectiveDegree, mul_div_cancel_left₀ _ hnR]

theorem parameter_bernoulli_word_trace_scale {n : ℕ} (p : ℝ≥0) (w : List Bool)
    (x : BernoulliSquareSample n) :
    parameterBernoulliWordTrace p w x =
      ((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ w.length / n) *
        (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) w).trace.re := by
  unfold parameterBernoulliWordTrace parameterNormalizedCenteredBernoulliMatrix
  rw [← Complex.ofReal_inv, matrix_adjoint_word_trace_re_real_smul]
  ring

theorem parameter_bernoulli_empty_word_mean {n : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) : parameterBernoulliWordMean n p hp [] = 1 := by
  simp [parameterBernoulliWordMean, parameterBernoulliWordTrace, matrixAdjointWord, ne_of_gt hn]

def parameterBernoulliPatternContribution {k : ℕ} (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) : ℝ :=
  ((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + 1) / n) *
    (n.descFactorial (bernoulliPatternVertexCount s) : ℝ) * bernoulliWalkPatternWeight p hp b s

theorem parameter_bernoulli_word_mean_pattern_sum (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (k : ℕ) (b : Fin (k + 1) → Bool) :
    parameterBernoulliWordMean n p hp (List.ofFn b) =
      ∑ s : Setoid (Fin (k + 1)), parameterBernoulliPatternContribution n p hp b s := by
  unfold parameterBernoulliWordMean
  simp_rw [parameter_bernoulli_word_trace_scale, List.length_ofFn]
  rw [integral_const_mul, bernoulli_matrix_word_pattern_integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold parameterBernoulliPatternContribution bernoulliPatternVertexCount
  ring

theorem parameter_bernoulli_nonsurviving_pattern_zero {k : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hNot : ¬ BernoulliSurvivingPattern b s) :
    parameterBernoulliPatternContribution n p hp b s = 0 := by
  unfold BernoulliSurvivingPattern at hNot
  push_neg at hNot
  obtain ⟨e, he⟩ := hNot
  unfold parameterBernoulliPatternContribution
  rw [bernoulli_pattern_weight_singleton_zero p hp b s e he, mul_zero]

theorem parameter_bernoulli_pattern_abs_bound {k : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hSurvive : BernoulliSurvivingPattern b s) :
    |parameterBernoulliPatternContribution n p hp b s| ≤
      (((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + 1) / n) *
        (n.descFactorial (bernoulliPatternVertexCount s) : ℝ)) *
          (p : ℝ) ^ bernoulliPatternEntryCount b s := by
  unfold parameterBernoulliPatternContribution
  rw [abs_mul, abs_of_nonneg (show 0 ≤
    ((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + 1) / n) *
      (n.descFactorial (bernoulliPatternVertexCount s) : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left (bernoulli_pattern_weight_abs_bound p hp b s hSurvive)
    (by positivity)

theorem parameter_bernoulli_even_pattern_abs_bound {n k m : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) (hD : 0 < bernoulliEffectiveDegree n p)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hLength : k + 1 = 2 * m) (hSurvive : BernoulliSurvivingPattern b s) :
    |parameterBernoulliPatternContribution n p hp b s| ≤
      sparseRealEvenPatternBudget n (bernoulliPatternVertexCount s)
        (bernoulliPatternEntryCount b s) m (bernoulliEffectiveDegree n p) := by
  have h := parameter_bernoulli_pattern_abs_bound n p hp b s hSurvive
  rwa [hLength, bernoulli_parameter_eq_effective_degree_div hn p,
    sparse_real_even_pattern_scale_identity hn hD] at h

theorem parameter_bernoulli_even_leading_pattern_formula {n k m : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) (hD : 0 < bernoulliEffectiveDegree n p)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hLength : k + 1 = 2 * m) (hLeading : BernoulliLeadingPattern b s) :
    parameterBernoulliPatternContribution n p hp b s =
      sparseRealEvenPatternBudget n (bernoulliPatternVertexCount s) m m
        (bernoulliEffectiveDegree n p) * (1 - (p : ℝ)) ^ m := by
  have hE : bernoulliPatternEntryCount b s = m := by
    have h := hLeading.2.2
    omega
  have hPaired := bernoulli_maximal_entry_pattern_paired b s hLeading.1 hLeading.2.2
  have hWeight : bernoulliWalkPatternWeight p hp b s =
      ((p : ℝ) * (1 - (p : ℝ))) ^ m := by
    rw [bernoulli_paired_pattern_weight p hp b s hPaired, ← bernoulliPatternEntryCount, hE]
  unfold parameterBernoulliPatternContribution
  rw [hWeight, hLength, mul_pow, ← mul_assoc]
  congr 1
  rw [bernoulli_parameter_eq_effective_degree_div hn p,
    sparse_real_even_pattern_scale_identity hn hD]

end CircularLaw
