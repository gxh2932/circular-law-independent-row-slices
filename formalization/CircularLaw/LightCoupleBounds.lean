import CircularLaw.SignedMatrixConcentration

/-!
# The actual light coefficients and their deterministic mean bound

Clipping at the source threshold retains the coefficient cap and does
not increase squared mass. When the total coefficient sum is zero,
the omitted heavy coefficients bound the light mean by the reciprocal
threshold. Rank-one unit vectors with a zero-sum right vector satisfy
these finite hypotheses exactly.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def lightMatrixWeights {ι : Type*} {n : ℕ} (Q : ι → Fin n → ℝ) (K : ℝ) : ι → Fin n → ℝ :=
  fun i j => if |Q i j| ≤ K then Q i j else 0

def weightedSliceMatrixSum {ι : Type*} [Fintype ι] {n d : ℕ}
    (Q : ι → Fin n → ℝ) (rows : ι → RowSlice n d) : ℝ :=
  ∑ i, weightedSliceSum Finset.univ (Q i) (rows i)

theorem centeredWeightedSliceMatrixSum_eq {ι : Type*} [Fintype ι] {n d : ℕ}
    (Q : ι → Fin n → ℝ) (rows : ι → RowSlice n d) :
    centeredWeightedSliceMatrixSum Q rows = weightedSliceMatrixSum Q rows -
      ((d : ℝ) / n) * ∑ i, ∑ j, Q i j := by
  unfold centeredWeightedSliceMatrixSum weightedSliceMatrixSum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem lightMatrixWeights_abs_le {ι : Type*} {n : ℕ} (Q : ι → Fin n → ℝ) (K : ℝ)
    (i : ι) (j : Fin n) : |lightMatrixWeights Q K i j| ≤ |Q i j| := by
  unfold lightMatrixWeights
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (Q i j)

theorem lightMatrixWeights_cap {ι : Type*} {n : ℕ} (Q : ι → Fin n → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (i : ι) (j : Fin n) : |lightMatrixWeights Q K i j| ≤ K := by
  unfold lightMatrixWeights
  split_ifs with h
  · exact h
  · simpa only [abs_zero] using hK

theorem lightMatrixWeights_squared_sum_le {ι : Type*} [Fintype ι] {n : ℕ}
    (Q : ι → Fin n → ℝ) (K : ℝ) :
    (∑ i, ∑ j, lightMatrixWeights Q K i j ^ 2) ≤ ∑ i, ∑ j, Q i j ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (lightMatrixWeights Q K i j))
    (lightMatrixWeights_abs_le Q K i j) 2

theorem omitted_light_weight_abs_le_square_div {q K : ℝ} (hK : 0 < K) :
    |q - (if |q| ≤ K then q else 0)| ≤ q ^ 2 / K := by
  by_cases hq : |q| ≤ K
  · rw [if_pos hq, sub_self, abs_zero]
    positivity
  · rw [if_neg hq, sub_zero]
    apply (le_div_iff₀ hK).mpr
    have hLarge := le_of_not_ge hq
    have hScaled := mul_le_mul_of_nonneg_left hLarge (abs_nonneg q)
    simpa only [← pow_two, sq_abs] using hScaled

theorem abs_matrix_coefficient_sum_le {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → Fin n → ℝ) :
    |∑ i, ∑ j, Q i j| ≤ ∑ i, ∑ j, |Q i j| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact Finset.abs_sum_le_sum_abs _ _

theorem lightMatrixWeights_sum_abs_le {ι : Type*} [Fintype ι] {n : ℕ}
    (Q : ι → Fin n → ℝ) {K : ℝ} (hK : 0 < K)
    (hZero : (∑ i, ∑ j, Q i j) = 0) (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    |∑ i, ∑ j, lightMatrixWeights Q K i j| ≤ 1 / K := by
  have hBalance : (∑ i, ∑ j, (Q i j - lightMatrixWeights Q K i j)) =
      -(∑ i, ∑ j, lightMatrixWeights Q K i j) := by
    simp_rw [Finset.sum_sub_distrib]
    rw [hZero, zero_sub]
  have hOmitted := abs_matrix_coefficient_sum_le (fun i j => Q i j - lightMatrixWeights Q K i j)
  rw [hBalance, abs_neg] at hOmitted
  apply hOmitted.trans
  calc
    _ ≤ ∑ i, ∑ j, Q i j ^ 2 / K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact omitted_light_weight_abs_le_square_div hK
    _ = (∑ i, ∑ j, Q i j ^ 2) / K := by simp_rw [Finset.sum_div]
    _ ≤ 1 / K := div_le_div_of_nonneg_right hSquare hK.le

theorem rankOneWeights_squared_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (x : ι → ℝ) (y : Fin n → ℝ) :
    (∑ i, ∑ j, (x i * y j) ^ 2) = (∑ i, x i ^ 2) * ∑ j, y j ^ 2 := by
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [Finset.sum_mul]

theorem rankOneWeights_sum_zero {ι : Type*} [Fintype ι] {n : ℕ}
    (x : ι → ℝ) (y : Fin n → ℝ) (hy : (∑ j, y j) = 0) :
    (∑ i, ∑ j, x i * y j) = 0 := by
  simp_rw [← Finset.mul_sum, hy, mul_zero]
  exact Finset.sum_const_zero

end CircularLaw
