import CircularLaw.LLYRowSurvivors
import CircularLaw.LLYColumnAction

/-!
# Actual shifted row action on the LLY surviving rows

The bad top block is avoided. The separate second and third rank loads
control both the bad coordinate count and its weighted modulus sum.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lly_row_selected_bad_cover {n d k₁ k₂ k₃ : ℕ} (S : RowSlice n d)
    (x : Fin n → ℂ) (F : Finset (Fin n))
    (hAvoid : ∀ j ∈ S.val, j ∉ llyBadTop x F k₁) :
    S.val \ F ⊆ llyBadSecond x F k₁ k₂ ∪ llyBadThird x F k₂ k₃ ∪ llyBadTail x F k₃ := by
  intro j hj
  have hAll : j ∈ Finset.univ \ F := Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
  rw [lly_bad_blocks_cover (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) x F] at hAll
  simp only [Finset.mem_union] at hAll ⊢
  rcases hAll with ((hTop | hSecond) | hThird) | hTail
  · exact False.elim (hAvoid j (Finset.mem_sdiff.mp hj).1 hTop)
  · exact Or.inl (Or.inl hSecond)
  · exact Or.inl (Or.inr hThird)
  · exact Or.inr hTail

theorem lly_row_selected_bad_count {n d k₁ k₂ k₃ : ℕ} (S : RowSlice n d)
    (x : Fin n → ℂ) (F : Finset (Fin n))
    (hAvoid : ∀ j ∈ S.val, j ∉ llyBadTop x F k₁) :
    ((S.val \ F).card : ℝ) ≤ (rowLoad S (llyBadSecond x F k₁ k₂) : ℝ) +
      rowLoad S (llyBadThird x F k₂ k₃) + rowLoad S (llyBadTail x F k₃) := by
  have h := finite_three_block_sum_bound (S.val \ F) (llyBadSecond x F k₁ k₂)
    (llyBadThird x F k₂ k₃) (llyBadTail x F k₃) (fun _ => (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (lly_row_selected_bad_cover S x F hAvoid)
    (fun _ _ => le_refl _) (fun _ _ => le_refl _) (fun _ _ => le_refl _)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hCount (J : Finset (Fin n)) : (((S.val \ F) ∩ J).card : ℝ) ≤ rowLoad S J := by
    have hSub : (S.val \ F) ∩ J ⊆ S.val ∩ J := by
      intro j hj
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hj).1).1,
        (Finset.mem_inter.mp hj).2⟩
    exact_mod_cast Finset.card_le_card hSub
  exact h.trans (add_le_add (add_le_add (hCount _) (hCount _)) (hCount _))

theorem lly_row_selected_bad_mass {n d k₁ k₂ k₃ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (S : RowSlice n d) (x : Fin n → ℂ) (F : Finset (Fin n)) (c : ℂ)
    (hGap₁ : orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂)
    (hGap₂ : orderedNormAt x k₂ ≤ 4 * orderedNormAt x k₃)
    (hCenter : 4 / 5 * orderedNormAt x k₃ ≤ ‖c‖)
    (hAvoid : ∀ j ∈ S.val, j ∉ llyBadTop x F k₁) :
    (∑ j ∈ S.val \ F, ‖x j‖) ≤
      5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖ * rowLoad S (llyBadSecond x F k₁ k₂) +
      5 * ‖c‖ * rowLoad S (llyBadThird x F k₂ k₃) +
      5 / 4 * ‖c‖ * rowLoad S (llyBadTail x F k₃) := by
  have hBounds := lly_almost_block_coordinate_bounds hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    x F c hGap₁ hGap₂ hCenter
  have h := finite_three_block_sum_bound (S.val \ F) (llyBadSecond x F k₁ k₂)
    (llyBadThird x F k₂ k₃) (llyBadTail x F k₃) (fun j => ‖x j‖)
    (by positivity) (by positivity) (by positivity) (lly_row_selected_bad_cover S x F hAvoid)
    (fun j hj => hBounds.1 j (Finset.mem_inter.mp hj).2)
    (fun j hj => hBounds.2.1 j (Finset.mem_inter.mp hj).2)
    (fun j hj => hBounds.2.2.1 j (Finset.mem_inter.mp hj).2)
  have hCount (J : Finset (Fin n)) : (((S.val \ F) ∩ J).card : ℝ) ≤ rowLoad S J := by
    have hSub : (S.val \ F) ∩ J ⊆ S.val ∩ J := by
      intro j hj
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hj).1).1,
        (Finset.mem_inter.mp hj).2⟩
    exact_mod_cast Finset.card_le_card hSub
  apply h.trans
  calc
    _ ≤ (rowLoad S (llyBadSecond x F k₁ k₂) : ℝ) * (5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖) +
        rowLoad S (llyBadThird x F k₂ k₃) * (5 * ‖c‖) +
        rowLoad S (llyBadTail x F k₃) * (5 / 4 * ‖c‖) := by
      gcongr <;> exact_mod_cast hCount _
    _ = _ := by ring

theorem lly_row_large_load_rate {n d k : ℕ} (hn : 0 < n)
    (hScale : (k : ℝ) ≤ (n : ℝ) / 1000) :
    16 * (k : ℝ) * d / n ≤ 16 * (d : ℝ) / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).mpr
  have h := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg (α := ℝ) d)
  nlinarith only [h]

theorem lly_row_second_weighted_rate {n d k : ℕ} (hn : 0 < n)
    (hScale : (k : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000) :
    (d : ℝ) ^ (3 / 4 : ℝ) * (16 * (k : ℝ) * d / n) ≤ 16 * (d : ℝ) / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnR).mpr
  have h := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg (α := ℝ) d)
  nlinarith only [h]

theorem lly_surviving_row_shifted_action {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (x : EuclideanSpace ℂ (Fin n))
    (F : Finset (Fin n)) (c ζ : ℂ) (i : I)
    (hGap₁ : orderedNormAt (fun j => x j) k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt (fun j => x j) k₂)
    (hGap₂ : orderedNormAt (fun j => x j) k₂ ≤ 4 * orderedNormAt (fun j => x j) k₃)
    (hCenter : 4 / 5 * orderedNormAt (fun j => x j) k₃ ≤ ‖c‖)
    (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ orderedNormAt (fun j => x j) k₃ / 5)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hi : i.val ∈ llyRowSurvivors I rows (fun j => x j) F k₁ k₂ k₃) :
    (d : ℝ) / 5 * ‖c‖ ≤ ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x i‖ := by
  have hLoads := llyRowSurvivors_mem hi
  have hAvoid := row_load_below_one_avoids (rows i.val) _ hLoads.2.2.1
  have hCount := lly_row_selected_bad_count (k₂ := k₂) (k₃ := k₃) (rows i.val) (fun j => x j) F hAvoid
  have hRate₃ := lly_row_large_load_rate (d := d) hn hScale₃
  have hScale₂' : (k₂ : ℝ) ≤ (n : ℝ) / 1000 :=
    (by exact_mod_cast hk₂₃ : (k₂ : ℝ) ≤ k₃).trans hScale₃
  have hRate₂ := lly_row_large_load_rate (d := d) hn hScale₂'
  have hCloseCount : 4 * (d : ℝ) / 5 ≤ ((rows i.val).val ∩ F).card := by
    have hPart := Finset.card_sdiff_add_card_inter (rows i.val).val F
    rw [(rows i.val).property] at hPart
    have hPartR := congrArg (fun a : ℕ => (a : ℝ)) hPart
    simp only [Nat.cast_add] at hPartR
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hMass := lly_row_selected_bad_mass hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    (rows i.val) (fun j => x j) F c hGap₁ hGap₂ hCenter hAvoid
  have hRateWeight := lly_row_second_weighted_rate (d := d) hn hScale₂
  have hWeighted₂ : (d : ℝ) ^ (3 / 4 : ℝ) *
      rowLoad (rows i.val) (llyBadSecond (fun j => x j) F k₁ k₂) ≤ 16 * (d : ℝ) / 1000 :=
    (mul_le_mul_of_nonneg_left hLoads.2.2.2.1.le (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans hRateWeight
  have h₂ := mul_le_mul_of_nonneg_left hWeighted₂ (show 0 ≤ 5 * ‖c‖ by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (hLoads.2.2.2.2.1.le.trans hRate₃)
    (show 0 ≤ 5 * ‖c‖ by positivity)
  have h₄ := mul_le_mul_of_nonneg_left (hLoads.2.2.2.2.2.le.trans hRate₃)
    (show 0 ≤ 5 / 4 * ‖c‖ by positivity)
  have hBad : (∑ j ∈ (rows i.val).val \ F, ‖x j‖) ≤ (d : ℝ) / 5 * ‖c‖ := by
    nlinarith only [hMass, h₂, h₃, h₄, mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (norm_nonneg c)]
  change (d : ℝ) / 5 * ‖c‖ ≤ ‖(retainedShiftedMatrix I ζ rows).mulVec (fun j => x j) i‖
  rw [retainedShiftedMatrix_mulVec, rowLinearForm_eq_support_sum]
  apply support_almost_constant_fifth_lower (rows i.val).val F (fun j => x j) c ζ i.val
  · intro j hj
    apply (hClose j (Finset.mem_inter.mp hj).2).trans
    linarith only [hCenter]
  · exact hCloseCount
  · exact hBad
  · have h := norm_le_orderedNormAt_notMem_prefix (fun j => x j) hk₃ hk₃n i.val hLoads.2.1
    linarith only [h, hCenter]
  · exact hShift

end CircularLaw
