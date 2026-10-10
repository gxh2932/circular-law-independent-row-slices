import CircularLaw.LLYColumnBadMass
import CircularLaw.SupportAlmostConstantAction
import CircularLaw.RowSliceColumnLowerBounds
import CircularLaw.ShiftedSliceUnitNormal

/-!
# Lower action on the surviving actual column supports

The two rank budgets control the bad mass, and the actual five-sixths
column-degree condition supplies at least four-fifths close entries.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem rowSliceColumnSupport_card {m n d : ℕ} (rows : Fin m → RowSlice n d) (j : Fin n) :
    ((rowSliceColumnSupport rows j).card : ℝ) = rowSliceColumnCount rows j := by
  rw [rectangularSliceMatrixReal_columnCount]
  simp only [rectangularSliceMatrixReal, rowEntryReal, Finset.sum_boole, rowSliceColumnSupport]

theorem shifted_slice_adjoint_apply_eq_column_sum {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    (fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x j =
      (∑ i ∈ rowSliceColumnSupport rows j, x i) - star ζ * x j := by
  change (∑ i, star (fullShiftedSliceMatrix ζ rows i j) * x i) = _
  simp only [fullShiftedSliceMatrix_apply, star_sub, star_mul, sub_mul, Finset.sum_sub_distrib]
  have hEntry : (∑ i : Fin n, star (rowEntry (rows i) j) * x i) =
      ∑ i ∈ rowSliceColumnSupport rows j, x i := by
    simp [rowEntry, rowSliceColumnSupport, Finset.sum_filter]
  rw [hEntry]
  congr 1
  simp

theorem lly_column_large_load_rate {n d k : ℕ} (hn : 0 < n)
    (hScale : (k : ℝ) ≤ (n : ℝ) / 1000) :
    9 * (k : ℝ) * d / n ≤ 9 * (d : ℝ) / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).mpr
  have h := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg (α := ℝ) d)
  nlinarith only [h]

theorem lly_column_second_weighted_rate {n d k : ℕ} (hn : 0 < n)
    (hScale : (k : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000) :
    (d : ℝ) ^ (3 / 4 : ℝ) * (9 * (k : ℝ) * d / n) ≤ 9 * (d : ℝ) / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnR).mpr
  have h := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg (α := ℝ) d)
  nlinarith only [h]

theorem lly_surviving_column_close_count {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₂₃ : k₂ ≤ k₃)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n)) (j : Fin n)
    (hScale : (k₃ : ℝ) ≤ (n : ℝ) / 1000)
    (hColumn : 5 * (d : ℝ) / 6 ≤ rowSliceColumnCount rows j)
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    4 * (d : ℝ) / 5 ≤ (rowSliceColumnSupport rows j ∩ F).card := by
  have hLoads := llyColumnSurvivors_mem hj
  have hRate₃ := lly_column_large_load_rate (d := d) hn hScale
  have hScale₂ : (k₂ : ℝ) ≤ (n : ℝ) / 1000 := (by exact_mod_cast hk₂₃ : (k₂ : ℝ) ≤ k₃).trans hScale
  have hRate₂ := lly_column_large_load_rate (d := d) hn hScale₂
  have hCount := lly_surviving_column_bad_count hj
  have hPartition := Finset.card_sdiff_add_card_inter (rowSliceColumnSupport rows j) F
  have hPartitionR := congrArg (fun a : ℕ => (a : ℝ)) hPartition
  simp only [Nat.cast_add, rowSliceColumnSupport_card] at hPartitionR
  linarith [Nat.cast_nonneg (α := ℝ) d]

theorem lly_surviving_column_bad_mass_fifth {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n)) (c : ℂ) (j : Fin n)
    (hGap₁ : orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂)
    (hGap₂ : orderedNormAt x k₂ ≤ 4 * orderedNormAt x k₃)
    (hCenter : 4 / 5 * orderedNormAt x k₃ ≤ ‖c‖)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000)
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    (∑ i ∈ rowSliceColumnSupport rows j \ F, ‖x i‖) ≤ (d : ℝ) / 5 * ‖c‖ := by
  have hMass := lly_surviving_column_bad_mass hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    rows x F c j hGap₁ hGap₂ hCenter hj
  have hLoads := llyColumnSurvivors_mem hj
  have hRate₂ := lly_column_second_weighted_rate (d := d) hn hScale₂
  have hRate₃ := lly_column_large_load_rate (d := d) hn hScale₃
  have hWeighted₂ : (d : ℝ) ^ (3 / 4 : ℝ) *
      rowSliceColumnSubsetLoad rows (llyBadSecond x F k₁ k₂) j ≤ 9 * (d : ℝ) / 1000 :=
    (mul_le_mul_of_nonneg_left hLoads.2.2.1.le (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans hRate₂
  have h₂ := mul_le_mul_of_nonneg_left hWeighted₂ (show 0 ≤ 5 * ‖c‖ by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (hLoads.2.2.2.1.le.trans hRate₃)
    (show 0 ≤ 5 * ‖c‖ by positivity)
  have h₄ := mul_le_mul_of_nonneg_left (hLoads.2.2.2.2.le.trans hRate₃)
    (show 0 ≤ 5 / 4 * ‖c‖ by positivity)
  nlinarith only [hMass, h₂, h₃, h₄, mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (norm_nonneg c)]

theorem lly_surviving_column_adjoint_action {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (rows : RowSliceMatrix n d) (x : EuclideanSpace ℂ (Fin n))
    (F : Finset (Fin n)) (c ζ : ℂ) (j : Fin n)
    (hGap₁ : orderedNormAt (fun i => x i) k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt (fun i => x i) k₂)
    (hGap₂ : orderedNormAt (fun i => x i) k₂ ≤ 4 * orderedNormAt (fun i => x i) k₃)
    (hCenter : 4 / 5 * orderedNormAt (fun i => x i) k₃ ≤ ‖c‖)
    (hClose : ∀ i ∈ F, ‖x i - c‖ ≤ orderedNormAt (fun i => x i) k₃ / 5)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000)
    (hColumn : 5 * (d : ℝ) / 6 ≤ rowSliceColumnCount rows j)
    (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hj : j ∈ llyColumnSurvivors rows (fun i => x i) F k₁ k₂ k₃) :
    (d : ℝ) / 5 * ‖c‖ ≤ ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x j‖ := by
  rw [shifted_slice_adjoint_apply_eq_column_sum]
  apply support_almost_constant_fifth_lower (rowSliceColumnSupport rows j) F (fun i => x i) c (star ζ) j
  · intro i hi
    apply (hClose i (Finset.mem_inter.mp hi).2).trans
    linarith only [hCenter]
  · exact lly_surviving_column_close_count hn hk₂₃ rows (fun i => x i) F j hScale₃ hColumn hj
  · exact lly_surviving_column_bad_mass_fifth hn hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
      rows (fun i => x i) F c j hGap₁ hGap₂ hCenter hScale₂ hScale₃ hj
  · have hNot := (llyColumnSurvivors_mem hj).1
    have h := norm_le_orderedNormAt_notMem_prefix (fun i => x i) hk₃ hk₃n j hNot
    linarith only [h, hCenter]
  · simpa only [norm_star] using hShift

end CircularLaw
