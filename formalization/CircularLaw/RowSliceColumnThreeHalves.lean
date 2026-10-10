import CircularLaw.RowSliceColumnLowerBounds

/-!
# Sharp-enough actual column-degree upper bounds for first-steep action

The Poisson moment at log(3/2) bounds every column by 3d/2. This is the
column-degree budget needed for the six-degree adjoint jump estimate;
the previously proved bound 9d is too coarse for that use.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem square_rowSliceColumn_three_halves_upper_tail {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (j : Fin n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      3 * (d : ℝ) / 2 ≤ rowSliceColumnCount rows j) ≤ Real.exp (-2 * sliceTailRate * d) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := rowSliceEdge_upper_laplace_tail hn hd (Finset.univ : Finset (Fin n)) {j}
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)) (3 * (d : ℝ) / 2)
  have hMean : rowSliceEdgeMean d (Finset.univ : Finset (Fin n)) {j} = (d : ℝ) := by
    unfold rowSliceEdgeMean
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton, Nat.cast_one, mul_one]
    field_simp
  rw [hMean, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at h
  apply h.trans_eq
  congr 1
  unfold sliceTailRate
  ring

theorem square_rowSliceColumn_three_halves_failure {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬RowSliceColumnBound (3 * (d : ℝ) / 2) rows) ≤
      (n : ℝ) * Real.exp (-2 * sliceTailRate * d) := by
  apply (uniformProbability_mono ?_).trans
    ((uniformProbability_finset_exists_le (Finset.univ : Finset (Fin n))
      (fun (j : Fin n) (rows : RowSliceMatrix n d) => 3 * (d : ℝ) / 2 ≤ rowSliceColumnCount rows j)).trans ?_)
  · intro rows hBad
    unfold RowSliceColumnBound at hBad
    push_neg at hBad
    obtain ⟨j, hj⟩ := hBad
    exact ⟨j, Finset.mem_univ j, hj.le⟩
  · calc
      _ ≤ ∑ _j : Fin n, Real.exp (-2 * sliceTailRate * d) :=
        Finset.sum_le_sum (fun j _ => square_rowSliceColumn_three_halves_upper_tail hn hd j)
      _ = _ := by simp

theorem square_rowSliceColumn_three_halves_failure_polynomial {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (A : ℝ) (hDegree : (1 / (2 * sliceTailRate)) * (A + 1) * Real.log (n : ℝ) ≤ d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬RowSliceColumnBound (3 * (d : ℝ) / 2) rows) ≤
      (n : ℝ) ^ (-A) := by
  apply (square_rowSliceColumn_three_halves_failure hn hd).trans
  have hExponent : -2 * sliceTailRate * (d : ℝ) = -(d : ℝ) / (1 / (2 * sliceTailRate)) := by
    field_simp
  rw [hExponent]
  have hRate := sliceTailRate_pos
  exact dimension_exp_degree_le_rpow hn (by positivity : 0 < 1 / (2 * sliceTailRate)) hDegree

end CircularLaw
