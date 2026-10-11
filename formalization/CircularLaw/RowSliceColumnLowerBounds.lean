import CircularLaw.RowSliceEdgeLowerTail
import CircularLaw.RowSliceColumnBounds

/-!
# Uniform column-degree lower bounds, including a deleted row

These probabilities use the original ambient degree d/n in every
rectangular sample. The one-row-deleted estimate retains that parameter
and is supplied for the source almost-constant kernel argument.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def RowSliceColumnLowerBound {m n d : ℕ} (B : ℝ) (rows : Fin m → RowSlice n d) : Prop :=
  ∀ j : Fin n, B ≤ rowSliceColumnCount rows j

theorem rowSliceColumn_chernoff_lower_tail {m n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (j : Fin n) {θ : ℝ} (hθ : 0 ≤ θ) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      rowSliceColumnCount rows j ≤ (1 - θ) * ((d : ℝ) * m / n)) ≤
        Real.exp (-((d : ℝ) * m / n) * θ ^ 2 / 2) := by
  simpa only [rowSliceColumnCount, rowSliceEdgeMean, Finset.card_univ, Fintype.card_fin,
    Finset.card_singleton, Nat.cast_one, mul_one, div_mul_eq_mul_div] using
      rowSliceEdge_chernoff_lower_tail hn hdn (Finset.univ : Finset (Fin m)) {j} hθ

theorem rowSliceColumn_lower_failure_probability {m n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      ¬RowSliceColumnLowerBound ((1 - θ) * ((d : ℝ) * m / n)) rows) ≤
        (n : ℝ) * Real.exp (-((d : ℝ) * m / n) * θ ^ 2 / 2) := by
  apply (uniformProbability_mono ?_).trans
    (uniformProbability_finset_exists_le (Finset.univ : Finset (Fin n))
      (fun j rows => rowSliceColumnCount rows j ≤ (1 - θ) * ((d : ℝ) * m / n)))
    |>.trans ?_
  · intro rows hFail
    unfold RowSliceColumnLowerBound at hFail
    push_neg at hFail
    obtain ⟨j, hj⟩ := hFail
    exact ⟨j, Finset.mem_univ j, hj.le⟩
  · calc
      _ ≤ ∑ _j : Fin n, Real.exp (-((d : ℝ) * m / n) * θ ^ 2 / 2) := by
        exact Finset.sum_le_sum (fun j _ => rowSliceColumn_chernoff_lower_tail hn hdn j hθ)
      _ = _ := by simp

theorem square_rowSliceColumn_lower_failure {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RowSliceColumnLowerBound (5 * (d : ℝ) / 6) rows) ≤
        (n : ℝ) * Real.exp (-(d : ℝ) / 72) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := rowSliceColumn_lower_failure_probability (m := n) hn hdn
    (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hMean : (d : ℝ) * n / n = d := by field_simp
  rw [hMean] at h
  have hThreshold : (1 - (1 / 6 : ℝ)) * d = 5 * (d : ℝ) / 6 := by ring
  have hExponent : -(d : ℝ) * (1 / 6 : ℝ) ^ 2 / 2 = -(d : ℝ) / 72 := by ring
  simpa only [hThreshold, hExponent] using h

theorem one_row_deleted_column_lower_failure {n d : ℕ} (hn : 10 ≤ n) (hdn : d ≤ n) :
    uniformProbability (fun rows : Fin (n - 1) → RowSlice n d =>
      ¬RowSliceColumnLowerBound (3 * (d : ℝ) / 4) rows) ≤
        (n : ℝ) * Real.exp (-(d : ℝ) / 80) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hTen : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hMean : 9 * (d : ℝ) / 10 ≤ (d : ℝ) * (n - 1 : ℕ) / n := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    apply (le_div_iff₀ hnR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hThreshold : 3 * (d : ℝ) / 4 ≤
      (1 - 1 / 6) * ((d : ℝ) * (n - 1 : ℕ) / n) := by linarith
  apply (uniformProbability_mono ?_).trans
    ((rowSliceColumn_lower_failure_probability (m := n - 1) (by omega) hdn
      (by norm_num : (0 : ℝ) ≤ 1 / 6)).trans ?_)
  · intro rows hFail hGood
    apply hFail
    intro j
    exact hThreshold.trans (hGood j)
  · apply mul_le_mul_of_nonneg_left _ hnR.le
    apply Real.exp_le_exp.mpr
    nlinarith only [hMean]

theorem one_row_deleted_column_five_sixths_failure {n d : ℕ}
    (hn : 11 ≤ n) (hdn : d ≤ n) :
    uniformProbability (fun rows : Fin (n - 1) → RowSlice n d =>
      ¬RowSliceColumnLowerBound (5 * (d : ℝ) / 6) rows) ≤
        (n : ℝ) * Real.exp (-(d : ℝ) / 320) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEleven : (11 : ℝ) ≤ n := by exact_mod_cast hn
  have hMean : 10 * (d : ℝ) / 11 ≤ (d : ℝ) * (n - 1 : ℕ) / n := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    apply (le_div_iff₀ hnR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hThreshold : 5 * (d : ℝ) / 6 ≤
      (1 - 1 / 12) * ((d : ℝ) * (n - 1 : ℕ) / n) := by linarith
  apply (uniformProbability_mono ?_).trans
    ((rowSliceColumn_lower_failure_probability (m := n - 1) (by omega) hdn
      (by norm_num : (0 : ℝ) ≤ 1 / 12)).trans ?_)
  · intro rows hFail hGood
    apply hFail
    intro j
    exact hThreshold.trans (hGood j)
  · apply mul_le_mul_of_nonneg_left _ hnR.le
    apply Real.exp_le_exp.mpr
    nlinarith [hMean, Nat.cast_nonneg (α := ℝ) d]

theorem dimension_exp_degree_le_rpow {n d : ℕ} (hn : 0 < n) {c A : ℝ}
    (hc : 0 < c) (hDegree : c * (A + 1) * Real.log (n : ℝ) ≤ d) :
    (n : ℝ) * Real.exp (-(d : ℝ) / c) ≤ (n : ℝ) ^ (-A) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ) * Real.exp (-(A + 1) * Real.log (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hnR.le
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ hc).mpr
      nlinarith only [hDegree]
    _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-(A + 1) * Real.log (n : ℝ)) := by
      rw [Real.exp_log hnR]
    _ = Real.exp (-A * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = (n : ℝ) ^ (-A) := by
      rw [Real.rpow_def_of_pos hnR]
      congr 1
      ring

theorem square_rowSliceColumn_lower_failure_polynomial {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (A : ℝ)
    (hDegree : 72 * (A + 1) * Real.log (n : ℝ) ≤ d) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RowSliceColumnLowerBound (5 * (d : ℝ) / 6) rows) ≤ (n : ℝ) ^ (-A) :=
  (square_rowSliceColumn_lower_failure hn hdn).trans
    (dimension_exp_degree_le_rpow hn (by norm_num) hDegree)

theorem one_row_deleted_column_lower_failure_polynomial {n d : ℕ}
    (hn : 11 ≤ n) (hdn : d ≤ n) (A : ℝ)
    (hDegree : 320 * (A + 1) * Real.log (n : ℝ) ≤ d) :
    uniformProbability (fun rows : Fin (n - 1) → RowSlice n d =>
      ¬RowSliceColumnLowerBound (5 * (d : ℝ) / 6) rows) ≤ (n : ℝ) ^ (-A) :=
  (one_row_deleted_column_five_sixths_failure hn hdn).trans
    (dimension_exp_degree_le_rpow (by omega) (by norm_num) hDegree)

end CircularLaw
