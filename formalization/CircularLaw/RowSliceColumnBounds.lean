import CircularLaw.RowSliceDiscrepancyUnion

/-!
# Column loads in the rectangular row-slice model

A column is the actual edge count between all rows and one coordinate.
For at most `n` rows its mean is at most `d`. The Poisson tail therefore
puts all column loads below `9*d`, with failure at most `n*exp(-9*d)`.
The logarithmic degree condition converts this to any prescribed power.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceColumnCount {m n d : ℕ} (rows : Fin m → RowSlice n d) (j : Fin n) : ℝ :=
  rowSliceEdgeCount Finset.univ {j} rows

def RowSliceColumnBound {m n d : ℕ} (B : ℝ) (rows : Fin m → RowSlice n d) : Prop :=
  ∀ j : Fin n, rowSliceColumnCount rows j ≤ B

theorem real_exp_two_lt_nine : Real.exp (2 : ℝ) < 9 := by
  have h := Real.exp_one_lt_three
  have hPos := Real.exp_pos (1 : ℝ)
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith only [h, hPos]

theorem rowSliceColumn_mean_le {m n d : ℕ} (hn : 0 < n) (hmn : m ≤ n) (j : Fin n) :
    rowSliceEdgeMean d (Finset.univ : Finset (Fin m)) {j} ≤ d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simp only [rowSliceEdgeMean, Finset.card_univ, Fintype.card_fin,
    Finset.card_singleton, Nat.cast_one, mul_one]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hnR).mpr (mul_le_mul_of_nonneg_left hmnR (Nat.cast_nonneg d))

theorem rowSliceColumn_upper_tail {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    uniformProbability (fun rows : Fin m → RowSlice n d => 9 * (d : ℝ) ≤ rowSliceColumnCount rows j) ≤
      Real.exp (-9 * d) := by
  let S := (Finset.univ : Finset (Fin m))
  let T := ({j} : Finset (Fin n))
  have hS : S.Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hT : T.Nonempty := Finset.singleton_nonempty j
  have hMean := rowSliceEdgeMean_pos hn hd hS hT
  have hMeanLe := rowSliceColumn_mean_le (d := d) hn hmn j
  have hThreshold : Real.exp 2 * rowSliceEdgeMean d S T ≤ 9 * (d : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hMeanLe (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_right real_exp_two_lt_nine.le (Nat.cast_nonneg _))
  have hRatio := (le_div_iff₀ hMean).mpr hThreshold
  have hLog := Real.log_le_log (Real.exp_pos (2 : ℝ)) hRatio
  rw [Real.log_exp] at hLog
  have hRate := mul_le_mul_of_nonneg_left hLog (by positivity : (0 : ℝ) ≤ 9 * (d : ℝ) / 2)
  apply (rowSliceEdge_large_deviation_upper_tail hn hdn S T hMean hThreshold).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [hRate]

theorem rowSliceColumn_failure_probability {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceColumnBound (9 * d) rows) ≤
      (n : ℝ) * Real.exp (-9 * d) := by
  have hCover : ∀ rows : Fin m → RowSlice n d, ¬RowSliceColumnBound (9 * d) rows →
      ∃ j ∈ (Finset.univ : Finset (Fin n)), 9 * (d : ℝ) ≤ rowSliceColumnCount rows j := by
    intro rows hFail
    unfold RowSliceColumnBound at hFail
    push_neg at hFail
    obtain ⟨j, hj⟩ := hFail
    exact ⟨j, Finset.mem_univ j, hj.le⟩
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_finset_exists_le (Finset.univ : Finset (Fin n))
    (fun j (rows : Fin m → RowSlice n d) => 9 * (d : ℝ) ≤ rowSliceColumnCount rows j)).trans
  calc
    _ ≤ ∑ _j : Fin n, Real.exp (-9 * (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rowSliceColumn_upper_tail hm hn hmn hd hdn j
    _ = _ := by simp

theorem rowSliceColumn_failure_polynomial {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n) (A : ℝ)
    (hDegree : (A + 1) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    uniformProbability (fun rows : Fin m → RowSlice n d => ¬RowSliceColumnBound (9 * d) rows) ≤
      (n : ℝ) ^ (-A) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (rowSliceColumn_failure_probability hm hn hmn hd hdn).trans
  calc
    _ ≤ (n : ℝ) * Real.exp (-(A + 1) * Real.log (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hnR.le
      apply Real.exp_le_exp.mpr
      linarith only [hDegree]
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

end CircularLaw
