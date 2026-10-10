import CircularLaw.BernoulliTwoWalkPatterns
import CircularLaw.FiniteKernelPartition

/-!
# Exact finite pattern formula for actual Bernoulli trace covariance

The actual joint trace integral minus the product of its actual means
is the sum of entry-word covariance weights. Pair colorings combine
into one coloring on both position blocks. Grouping its exact kernel
gives a finite pattern sum with falling-factorial coefficients, retaining
every shared vertex and ordered entry.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

local instance bernoulliRawCovarianceBEq (n : ℕ) : BEq (Fin n × Fin n) := instBEqOfDecidableEq

def bernoulliTwoWordRawCovariance {k l : ℕ} (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) : ℝ :=
  (∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re *
    (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn c)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp) -
    (∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp) *
    (∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn c)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp)

theorem bernoulli_two_word_raw_covariance_walk_sum {k l : ℕ} (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    bernoulliTwoWordRawCovariance n p hp b c =
      ∑ v : Fin (k + 1) → Fin n, ∑ u : Fin (l + 1) → Fin n,
        bernoulliWordCovarianceWeight p hp (bernoulliWalkEntries b v) (bernoulliWalkEntries c u) := by
  rw [bernoulliTwoWordRawCovariance, bernoulli_centered_two_trace_integral,
    bernoulli_centered_matrix_word_trace_integral, bernoulli_centered_matrix_word_trace_integral]
  simp_rw [← bernoulli_word_weight_eq_full_product]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, bernoulliWordCovarianceWeight]

theorem bernoulli_two_word_raw_covariance_sum_coloring {k l : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    bernoulliTwoWordRawCovariance n p hp b c =
      ∑ v : BernoulliTwoWalkPositions k l → Fin n,
        bernoulliWordCovarianceWeight p hp (bernoulliWalkEntries b (fun a => v (Sum.inl a)))
          (bernoulliWalkEntries c (fun a => v (Sum.inr a))) := by
  rw [bernoulli_two_word_raw_covariance_walk_sum]
  calc
    _ = ∑ v : (Fin (k + 1) → Fin n) × (Fin (l + 1) → Fin n),
        bernoulliWordCovarianceWeight p hp (bernoulliWalkEntries b v.1)
          (bernoulliWalkEntries c v.2) := (Fintype.sum_prod_type _).symm
    _ = _ := ?_
  exact (Fintype.sum_equiv
    (Equiv.sumArrowEquivProdArrow (Fin (k + 1)) (Fin (l + 1)) (Fin n))
    (fun v => bernoulliWordCovarianceWeight p hp (bernoulliWalkEntries b (fun a => v (Sum.inl a)))
      (bernoulliWalkEntries c (fun a => v (Sum.inr a))))
    (fun v => bernoulliWordCovarianceWeight p hp (bernoulliWalkEntries b v.1)
      (bernoulliWalkEntries c v.2)) (fun _ => rfl)).symm

theorem bernoulli_two_word_raw_covariance_pattern_sum {k l : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    bernoulliTwoWordRawCovariance n p hp b c =
      ∑ s : Setoid (BernoulliTwoWalkPositions k l),
        (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ) *
          bernoulliTwoPatternCovarianceWeight p hp b c s := by
  rw [bernoulli_two_word_raw_covariance_sum_coloring]
  exact sum_kernel_constant_fin_colorings n _ _
    (fun s v h => bernoulli_two_walk_covariance_constant_on_kernel p hp b c s v h)

end CircularLaw
