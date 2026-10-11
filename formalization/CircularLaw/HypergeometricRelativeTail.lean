import CircularLaw.WeightedSliceLaplace

/-!
# Lower tails at the actual hypergeometric mean

The exact-slice negative Laplace bound controls occupancy of a set of
arbitrary size. The exponent is proportional to its mean occupancy,
which is needed when the high-coordinate block has vanishing density.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem weightedSliceSum_one_eq_occupancy {n d : ℕ} (M : Finset (Fin n))
    (S : RowSlice n d) :
    weightedSliceSum M (fun _ => 1) S = ((S.val ∩ M).card : ℝ) := by
  simp only [weightedSliceSum, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.filter_mem_eq_inter, Finset.inter_comm]

theorem slice_occupancy_relative_lower_tail {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (M : Finset (Fin n)) :
    uniformProbability (fun S : RowSlice n d =>
      ((S.val ∩ M).card : ℝ) ≤ ((d : ℝ) / n) * M.card / 2) ≤
      Real.exp (-(((d : ℝ) / n) * M.card) / 12) := by
  let μ := ((d : ℝ) / n) * M.card
  let F := fun S : RowSlice n d => Real.exp (-(1 / 2 : ℝ) * ((S.val ∩ M).card : ℝ))
  have hExpHalf : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos (1 / 2))]
    linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have hMGF := finiteMean_slice_weighted_laplace_exp hn hdn M (fun _ => 1)
    (by intro _ _; norm_num) (-(1 / 2 : ℝ))
  simp only [weightedSliceSum_one_eq_occupancy, mul_one, Finset.sum_const, nsmul_eq_mul] at hMGF
  have hMean : finiteMean F ≤ Real.exp (-μ / 3) := by
    apply hMGF.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (show Real.exp (-(1 / 2 : ℝ)) - 1 ≤ -1 / 3 by linarith)
      (by positivity : 0 ≤ ((d : ℝ) / n) * M.card)
    dsimp only [μ]
    nlinarith only [h]
  have hMarkov := finite_uniform_markov
    (fun S : RowSlice n d => ((S.val ∩ M).card : ℝ) ≤ μ / 2)
    F (a := Real.exp (-μ / 4)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
    (by
      intro S hS
      apply Real.exp_le_exp.mpr
      linarith)
  apply hMarkov.trans
  apply (div_le_div_of_nonneg_right hMean (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

end CircularLaw
