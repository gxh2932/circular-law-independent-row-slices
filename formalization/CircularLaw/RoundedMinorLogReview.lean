import CircularLaw.ScalarSquareSingularValues
import CircularLaw.SquareLogPrefixComparison
import CircularLaw.BernoulliEmptyMatrix
import Mathlib.Order.Interval.Finset.Nat

/-!
# Review of the integer-rounded upper logarithmic comparison

The source definitions of `m`, `ell`, `a`, `b` and `c` give an inclusive
sum from `a` to `b` in `T2`. For `n=100`, `epsilon=1/10` and `H=2 I`,
that candidate has one more logarithmic term than `T`, so `T <= T2`
is false. This module proves the counterexample for actual matrices.
It changes no manuscript formula and proves no convergence theorem.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

def bernoulliSqueezeMinorDimension (n : ℕ) (ε : ℝ) : ℕ := ⌊(1 - ε) * n⌋₊

def bernoulliSqueezePrefixLength (n : ℕ) (ε : ℝ) : ℕ :=
  ⌊(1 - ε / 4) * bernoulliSqueezeMinorDimension n ε⌋₊

def bernoulliSqueezeUpperStart (n : ℕ) (ε : ℝ) : ℕ := ⌈2 * ε * n⌉₊

def bernoulliSqueezeUpperEnd (n : ℕ) (ε : ℝ) : ℕ := ⌊(1 - ε) * n⌋₊

def bernoulliSqueezeBaseCount (n : ℕ) (ε : ℝ) : ℕ := ⌊(1 - 3 * ε) * n⌋₊

def squarePrincipalMinor {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hmn : m ≤ n) :
    Matrix (Fin m) (Fin m) ℂ := A.submatrix (Fin.castLE hmn) (Fin.castLE hmn)

theorem squarePrincipalMinor_scalar {n m : ℕ} (hmn : m ≤ n) (c : ℂ) :
    squarePrincipalMinor (c • (1 : Matrix (Fin n) (Fin n) ℂ)) hmn =
      c • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  ext i j
  simp only [squarePrincipalMinor, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, (Fin.castLE_injective hmn).eq_iff]

def squareMinorNegativeLogPrefix {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hmn : m ≤ n) (ell : ℕ) : ℝ :=
  (∑ j ∈ Finset.range ell, squareNegativeLogAt (squarePrincipalMinor A hmn) j) / n

def squareMinorLogUpperCandidate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hmn : m ≤ n) (ell a b c : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc a b, squareNegativeLogAt A (j - 1)) / n +
    ((ell : ℝ) - c) / n * squareNegativeLogAt (squarePrincipalMinor A hmn) (ell - 1)

theorem scalar_square_negative_log_at {n j : ℕ} (hj : j < n) (c : ℂ) :
    squareNegativeLogAt (c • (1 : Matrix (Fin n) (Fin n) ℂ)) j = -Real.log ‖c‖ := by
  rw [squareNegativeLogAt, dif_pos hj, scalar_square_singular_values]

theorem squeeze_rounding_example :
    bernoulliSqueezeMinorDimension 100 (1 / 10) = 90 ∧
    bernoulliSqueezePrefixLength 100 (1 / 10) = 87 ∧
    bernoulliSqueezeUpperStart 100 (1 / 10) = 20 ∧
    bernoulliSqueezeUpperEnd 100 (1 / 10) = 90 ∧
    bernoulliSqueezeBaseCount 100 (1 / 10) = 70 := by
  norm_num [bernoulliSqueezeMinorDimension, bernoulliSqueezePrefixLength,
    bernoulliSqueezeUpperStart, bernoulliSqueezeUpperEnd, bernoulliSqueezeBaseCount]

theorem scalar_minor_prefix_example :
    squareMinorNegativeLogPrefix ((2 : ℂ) • (1 : Matrix (Fin 100) (Fin 100) ℂ))
      (show 90 ≤ 100 by decide) 87 = -(87 / 100 : ℝ) * Real.log 2 := by
  unfold squareMinorNegativeLogPrefix
  rw [squarePrincipalMinor_scalar]
  have hSum : (∑ j ∈ Finset.range 87,
      squareNegativeLogAt ((2 : ℂ) • (1 : Matrix (Fin 90) (Fin 90) ℂ)) j) =
      (87 : ℝ) * (-Real.log 2) := by
    calc
      _ = ∑ j ∈ Finset.range 87, -Real.log 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [scalar_square_negative_log_at (by have := Finset.mem_range.mp hj; omega)]
        norm_num
      _ = _ := by simp
  rw [hSum]
  ring

theorem scalar_minor_upper_example :
    squareMinorLogUpperCandidate ((2 : ℂ) • (1 : Matrix (Fin 100) (Fin 100) ℂ))
      (show 90 ≤ 100 by decide) 87 20 90 70 = -(88 / 100 : ℝ) * Real.log 2 := by
  unfold squareMinorLogUpperCandidate
  rw [squarePrincipalMinor_scalar,
    scalar_square_negative_log_at (show 87 - 1 < 90 by decide)]
  have hSum : (∑ j ∈ Finset.Icc 20 90,
      squareNegativeLogAt ((2 : ℂ) • (1 : Matrix (Fin 100) (Fin 100) ℂ)) (j - 1)) =
      (71 : ℝ) * (-Real.log 2) := by
    calc
      _ = ∑ j ∈ Finset.Icc 20 90, -Real.log 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjBounds := Finset.mem_Icc.mp hj
        rw [scalar_square_negative_log_at (by omega)]
        norm_num
      _ = _ := by simp
  rw [hSum]
  norm_num
  ring

theorem rounded_minor_log_upper_counterexample :
    ¬squareMinorNegativeLogPrefix ((2 : ℂ) • (1 : Matrix (Fin 100) (Fin 100) ℂ))
        (show 90 ≤ 100 by decide) 87 ≤
      squareMinorLogUpperCandidate ((2 : ℂ) • (1 : Matrix (Fin 100) (Fin 100) ℂ))
        (show 90 ≤ 100 by decide) 87 20 90 70 := by
  rw [scalar_minor_prefix_example, scalar_minor_upper_example]
  have hLog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem bernoulli_empty_rounded_upper_counterexample :
    ¬squareMinorNegativeLogPrefix
        (normalizedShiftedBernoulliMatrix 10 (-2) (emptyBernoulliSquareSample 100))
        (show 90 ≤ 100 by decide) 87 ≤
      squareMinorLogUpperCandidate
        (normalizedShiftedBernoulliMatrix 10 (-2) (emptyBernoulliSquareSample 100))
        (show 90 ≤ 100 by decide) 87 20 90 70 := by
  rw [normalizedShiftedBernoulliMatrix_empty]
  norm_num only [neg_neg]
  exact rounded_minor_log_upper_counterexample

theorem bernoulli_empty_counterexample_positive_probability :
    0 < (sparseBernoulliMatrixLaw 100 10).real {emptyBernoulliSquareSample 100} := by
  rw [sparseBernoulliMatrixLaw_eq (by decide) (by decide)]
  exact emptyBernoulliSquareSample_probability_pos _ _ (by norm_num [rowBernoulliParameter])

end CircularLaw
