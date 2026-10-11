import CircularLaw.WeightedSliceLaplace

/-!
# Exponential moments of independent weighted slice rows

The actual finite row product law factors the row moments. Nonnegative
weights retain a Bernoulli exponential-defect bound for either sign of
the tilt. At bounded tilt this gives the squared-weight variance proxy
needed in the light part of the restricted-norm proof.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def centeredWeightedSliceMatrixSum {ι : Type*} [Fintype ι] {n d : ℕ}
    (w : ι → Fin n → ℝ) (rows : ι → RowSlice n d) : ℝ :=
  ∑ i, (weightedSliceSum Finset.univ (w i) (rows i) - ((d : ℝ) / n) * ∑ j, w i j)

def weightedSliceMatrixVariance {ι : Type*} [Fintype ι] (n d : ℕ) (w : ι → Fin n → ℝ) : ℝ :=
  ((d : ℝ) / n) * ∑ i, ∑ j, w i j ^ 2

theorem weightedSliceMatrixVariance_nonneg {ι : Type*} [Fintype ι]
    (n d : ℕ) (w : ι → Fin n → ℝ) : 0 ≤ weightedSliceMatrixVariance n d w := by
  unfold weightedSliceMatrixVariance
  positivity

theorem finiteMean_matrix_weighted_laplace_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (tilt : ℝ) :
    finiteMean (fun rows : ι → RowSlice n d => Real.exp (tilt * centeredWeightedSliceMatrixSum w rows)) ≤
      Real.exp (((d : ℝ) / n) * ∑ i, ∑ j, (Real.exp (tilt * w i j) - 1 - tilt * w i j)) := by
  have hPoint (rows : ι → RowSlice n d) :
      Real.exp (tilt * centeredWeightedSliceMatrixSum w rows) =
        ∏ i, Real.exp (tilt * (weightedSliceSum Finset.univ (w i) (rows i) -
          ((d : ℝ) / n) * ∑ j, w i j)) := by
    unfold centeredWeightedSliceMatrixSum
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hPoint]
  rw [finiteMean_pi_prod (fun i (s : RowSlice n d) =>
    Real.exp (tilt * (weightedSliceSum Finset.univ (w i) s - ((d : ℝ) / n) * ∑ j, w i j)))]
  calc
    _ ≤ ∏ i, Real.exp (((d : ℝ) / n) * ∑ j, (Real.exp (tilt * w i j) - 1 - tilt * w i j)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact finiteMean_nonneg (fun _ => Real.exp_nonneg _)
      · intro i _
        exact finiteMean_slice_centered_laplace_exp hn hd Finset.univ (w i) (fun j _ => hw i j) tilt
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

theorem real_exp_defect_le_square {x : ℝ} (hx : |x| ≤ 1) : Real.exp x - 1 - x ≤ x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hx)
  calc
    _ ≤ ‖Real.exp x - 1 - x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (Real.exp x - 1 - x)
    _ ≤ ‖x‖ ^ 2 := h
    _ = _ := by rw [Real.norm_eq_abs, sq_abs]

theorem finiteMean_matrix_weighted_laplace_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {K tilt : ℝ} (hK : ∀ i j, w i j ≤ K)
    (hScale : |tilt| * K ≤ 1) :
    finiteMean (fun rows : ι → RowSlice n d => Real.exp (tilt * centeredWeightedSliceMatrixSum w rows)) ≤
      Real.exp (tilt ^ 2 * weightedSliceMatrixVariance n d w) := by
  apply (finiteMean_matrix_weighted_laplace_exp hn hd w hw tilt).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ((d : ℝ) / n) * ∑ i, ∑ j, (tilt * w i j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply real_exp_defect_le_square
      rw [abs_mul, abs_of_nonneg (hw i j)]
      exact (mul_le_mul_of_nonneg_left (hK i j) (abs_nonneg tilt)).trans hScale
    _ = _ := by
      unfold weightedSliceMatrixVariance
      simp_rw [mul_pow, ← Finset.mul_sum]
      ring

end CircularLaw
