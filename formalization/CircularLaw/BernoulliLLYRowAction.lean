import CircularLaw.BernoulliLLYRowSurvivors
import CircularLaw.LLYRowAction
import CircularLaw.ShiftedBernoulliUnitNormal

/-!
# Shifted Bernoulli action on the surviving rows

The actual support may have variable cardinality. A lower degree bound
and the two load thresholds supply the close-coordinate count and the
bad-coordinate mass required by the deterministic action estimate.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def retainedShiftedBernoulliMatrix {n : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (sample : BernoulliSquareSample n) : Matrix I (Fin n) ℂ :=
  (fullShiftedBernoulliMatrix ζ sample).submatrix Subtype.val id

theorem retained_shifted_bernoulli_apply_eq_full {n : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (x : EuclideanSpace ℂ (Fin n)) (i : I) :
    (retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x i =
      (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i.val := rfl

theorem shifted_bernoulli_apply_eq_support_sum {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i =
      (∑ j ∈ bernoulliSupport (fun j => sample (i, j)), x j) - ζ * x i := by
  rw [shifted_bernoulli_matrix_apply_eq_row_form]
  congr 1
  rw [bernoulliSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases sample (i, j) <;> simp [weightedBernoulliValue]

theorem lly_support_selected_bad_mass {n d k₁ k₂ k₃ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (S : Finset (Fin n)) (x : Fin n → ℂ) (F : Finset (Fin n)) (c : ℂ)
    (hGap₁ : orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂)
    (hGap₂ : orderedNormAt x k₂ ≤ 4 * orderedNormAt x k₃)
    (hCenter : 4 / 5 * orderedNormAt x k₃ ≤ ‖c‖)
    (hAvoid : ∀ j ∈ S, j ∉ llyBadTop x F k₁) :
    (∑ j ∈ S \ F, ‖x j‖) ≤
      5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖ * ((S ∩ llyBadSecond x F k₁ k₂).card : ℝ) +
      5 * ‖c‖ * (S ∩ llyBadThird x F k₂ k₃).card +
      5 / 4 * ‖c‖ * (S ∩ llyBadTail x F k₃).card := by
  have hBounds := lly_almost_block_coordinate_bounds hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    x F c hGap₁ hGap₂ hCenter
  have hCover := lly_row_selected_bad_cover (k₂ := k₂) (k₃ := k₃)
    (⟨S, rfl⟩ : RowSlice n S.card) x F hAvoid
  have h := finite_three_block_sum_bound (S \ F) (llyBadSecond x F k₁ k₂)
    (llyBadThird x F k₂ k₃) (llyBadTail x F k₃) (fun j => ‖x j‖)
    (by positivity) (by positivity) (by positivity) hCover
    (fun j hj => hBounds.1 j (Finset.mem_inter.mp hj).2)
    (fun j hj => hBounds.2.1 j (Finset.mem_inter.mp hj).2)
    (fun j hj => hBounds.2.2.1 j (Finset.mem_inter.mp hj).2)
  apply h.trans
  calc
    _ ≤ ((S ∩ llyBadSecond x F k₁ k₂).card : ℝ) * (5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖) +
        (S ∩ llyBadThird x F k₂ k₃).card * (5 * ‖c‖) +
        (S ∩ llyBadTail x F k₃).card * (5 / 4 * ‖c‖) := by
      gcongr <;> exact Finset.sdiff_subset
    _ = _ := by ring

theorem bernoulli_lly_surviving_row_shifted_action {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (x : EuclideanSpace ℂ (Fin n))
    (F : Finset (Fin n)) (c ζ : ℂ) (i : I)
    (hGap₁ : orderedNormAt (fun j => x j) k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt (fun j => x j) k₂)
    (hGap₂ : orderedNormAt (fun j => x j) k₂ ≤ 4 * orderedNormAt (fun j => x j) k₃)
    (hCenter : 4 / 5 * orderedNormAt (fun j => x j) k₃ ≤ ‖c‖)
    (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ orderedNormAt (fun j => x j) k₃ / 5)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000)
    (hDegree : BernoulliRowDegreeLowerBound (9 * (d : ℝ) / 10) sample)
    (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (hi : i.val ∈ bernoulliLLYRowSurvivors d I sample (fun j => x j) F k₁ k₂ k₃) :
    (d : ℝ) / 5 * ‖c‖ ≤ ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x i‖ := by
  let S := bernoulliSupport (fun j => sample (i.val, j))
  have hLoads := bernoulli_lly_row_survivors_mem hi
  have hAvoid := row_load_below_one_avoids (⟨S, rfl⟩ : RowSlice n S.card) _ hLoads.2.2.1
  have hCount := lly_row_selected_bad_count (k₂ := k₂) (k₃ := k₃)
    (⟨S, rfl⟩ : RowSlice n S.card) (fun j => x j) F hAvoid
  have hDegreeCard : 9 * (d : ℝ) / 10 ≤ (S.card : ℝ) := by
    have h := hDegree i.val
    rw [← bernoulli_row_load_eq_subset_count, bernoulliRowLoad, Finset.inter_univ] at h
    exact h
  have hRate₃ := lly_row_large_load_rate (d := d) hn hScale₃
  have hScale₂' : (k₂ : ℝ) ≤ (n : ℝ) / 1000 :=
    (by exact_mod_cast hk₂₃ : (k₂ : ℝ) ≤ k₃).trans hScale₃
  have hRate₂ := lly_row_large_load_rate (d := d) hn hScale₂'
  have hCloseCount : 4 * (d : ℝ) / 5 ≤ ((S ∩ F).card : ℝ) := by
    have hPart := Finset.card_sdiff_add_card_inter S F
    have hPartR := congrArg (fun a : ℕ => (a : ℝ)) hPart
    simp only [Nat.cast_add] at hPartR
    change ((S \ F).card : ℝ) ≤
      (bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadSecond (fun j => x j) F k₁ k₂) : ℝ) +
      bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadThird (fun j => x j) F k₂ k₃) +
      bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadTail (fun j => x j) F k₃) at hCount
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hMass := lly_support_selected_bad_mass hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    S (fun j => x j) F c hGap₁ hGap₂ hCenter hAvoid
  have hRateWeight := lly_row_second_weighted_rate (d := d) hn hScale₂
  have hWeighted₂ : (d : ℝ) ^ (3 / 4 : ℝ) *
      bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadSecond (fun j => x j) F k₁ k₂) ≤
        16 * (d : ℝ) / 1000 :=
    (mul_le_mul_of_nonneg_left hLoads.2.2.2.1.le (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans hRateWeight
  have h₂ := mul_le_mul_of_nonneg_left hWeighted₂ (show 0 ≤ 5 * ‖c‖ by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (hLoads.2.2.2.2.1.le.trans hRate₃)
    (show 0 ≤ 5 * ‖c‖ by positivity)
  have h₄ := mul_le_mul_of_nonneg_left (hLoads.2.2.2.2.2.le.trans hRate₃)
    (show 0 ≤ 5 / 4 * ‖c‖ by positivity)
  have hBad : (∑ j ∈ S \ F, ‖x j‖) ≤ (d : ℝ) / 5 * ‖c‖ := by
    change _ ≤ 5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖ *
      bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadSecond (fun j => x j) F k₁ k₂) +
      5 * ‖c‖ * bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadThird (fun j => x j) F k₂ k₃) +
      5 / 4 * ‖c‖ * bernoulliRowLoad (fun j => sample (i.val, j)) (llyBadTail (fun j => x j) F k₃) at hMass
    nlinarith only [hMass, h₂, h₃, h₄, mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (norm_nonneg c)]
  rw [retained_shifted_bernoulli_apply_eq_full, shifted_bernoulli_apply_eq_support_sum]
  apply support_almost_constant_fifth_lower S F (fun j => x j) c ζ i.val
  · intro j hj
    apply (hClose j (Finset.mem_inter.mp hj).2).trans
    linarith only [hCenter]
  · exact hCloseCount
  · exact hBad
  · have h := norm_le_orderedNormAt_notMem_prefix (fun j => x j) hk₃ hk₃n i.val hLoads.2.1
    linarith only [h, hCenter]
  · exact hShift

end CircularLaw
