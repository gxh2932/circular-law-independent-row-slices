import CircularLaw.LLYColumnSurvivors

/-!
# Actual bad-coordinate mass in each surviving column

The bad top block is avoided completely. The other three blocks retain
their different coordinate sizes and actual column loads.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceColumnSupport {m n d : ℕ} (rows : Fin m → RowSlice n d) (j : Fin n) :
    Finset (Fin m) := Finset.univ.filter (fun i => j ∈ (rows i).val)

theorem rowSliceColumnSupport_mem {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (j : Fin n) (i : Fin m) : i ∈ rowSliceColumnSupport rows j ↔ j ∈ (rows i).val := by
  simp only [rowSliceColumnSupport, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rowSliceColumnSubsetLoad_eq_inter_card {m n d : ℕ}
    (rows : Fin m → RowSlice n d) (J : Finset (Fin m)) (j : Fin n) :
    rowSliceColumnSubsetLoad rows J j = ((rowSliceColumnSupport rows j ∩ J).card : ℝ) := by
  rw [rowSliceColumnSubsetLoad_eq_card]
  have hEq : J.filter (fun i => j ∈ (rows i).val) = rowSliceColumnSupport rows j ∩ J := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_inter, rowSliceColumnSupport_mem, and_comm]
  rw [hEq]

theorem finite_three_block_sum_bound {ι : Type*} [DecidableEq ι]
    (S J₂ J₃ J₄ : Finset ι) (f : ι → ℝ) {b₂ b₃ b₄ : ℝ}
    (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄)
    (hCover : S ⊆ J₂ ∪ J₃ ∪ J₄)
    (h₂ : ∀ i ∈ S ∩ J₂, f i ≤ b₂) (h₃ : ∀ i ∈ S ∩ J₃, f i ≤ b₃)
    (h₄ : ∀ i ∈ S ∩ J₄, f i ≤ b₄) :
    (∑ i ∈ S, f i) ≤ ((S ∩ J₂).card : ℝ) * b₂ + ((S ∩ J₃).card : ℝ) * b₃ +
      ((S ∩ J₄).card : ℝ) * b₄ := by
  have hPoint : ∀ i ∈ S, f i ≤ (if i ∈ J₂ then b₂ else 0) +
      (if i ∈ J₃ then b₃ else 0) + (if i ∈ J₄ then b₄ else 0) := by
    intro i hi
    have h := hCover hi
    simp only [Finset.mem_union] at h
    rcases h with (hi₂ | hi₃) | hi₄
    · have hBound := h₂ i (Finset.mem_inter.mpr ⟨hi, hi₂⟩)
      simp only [if_pos hi₂]
      split_ifs <;> linarith
    · have hBound := h₃ i (Finset.mem_inter.mpr ⟨hi, hi₃⟩)
      simp only [if_pos hi₃]
      split_ifs <;> linarith
    · have hBound := h₄ i (Finset.mem_inter.mpr ⟨hi, hi₄⟩)
      simp only [if_pos hi₄]
      split_ifs <;> linarith
  apply (Finset.sum_le_sum hPoint).trans_eq
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]

theorem lly_surviving_column_bad_cover {n d k₁ k₂ k₃ : ℕ}
    {rows : RowSliceMatrix n d} {x : Fin n → ℂ} {F : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    rowSliceColumnSupport rows j \ F ⊆
      llyBadSecond x F k₁ k₂ ∪ llyBadThird x F k₂ k₃ ∪ llyBadTail x F k₃ := by
  intro i hi
  have hNotF := (Finset.mem_sdiff.mp hi).2
  have hRow := (rowSliceColumnSupport_mem rows j i).mp (Finset.mem_sdiff.mp hi).1
  have hAll : i ∈ Finset.univ \ F := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hNotF⟩
  rw [lly_bad_blocks_cover (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) x F] at hAll
  simp only [Finset.mem_union] at hAll ⊢
  rcases hAll with ((hTop | hSecond) | hThird) | hTail
  · exact False.elim (llyColumnSurvivors_top_avoided hj i hTop hRow)
  · exact Or.inl (Or.inl hSecond)
  · exact Or.inl (Or.inr hThird)
  · exact Or.inr hTail

theorem lly_surviving_column_bad_mass {n d k₁ k₂ k₃ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n)) (c : ℂ) (j : Fin n)
    (hGap₁ : orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂)
    (hGap₂ : orderedNormAt x k₂ ≤ 4 * orderedNormAt x k₃)
    (hCenter : 4 / 5 * orderedNormAt x k₃ ≤ ‖c‖)
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    (∑ i ∈ rowSliceColumnSupport rows j \ F, ‖x i‖) ≤
      5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖ * rowSliceColumnSubsetLoad rows (llyBadSecond x F k₁ k₂) j +
      5 * ‖c‖ * rowSliceColumnSubsetLoad rows (llyBadThird x F k₂ k₃) j +
      5 / 4 * ‖c‖ * rowSliceColumnSubsetLoad rows (llyBadTail x F k₃) j := by
  have hBounds := lly_almost_block_coordinate_bounds hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n
    x F c hGap₁ hGap₂ hCenter
  have h := finite_three_block_sum_bound (rowSliceColumnSupport rows j \ F)
    (llyBadSecond x F k₁ k₂) (llyBadThird x F k₂ k₃) (llyBadTail x F k₃) (fun i => ‖x i‖)
    (by positivity) (by positivity) (by positivity) (lly_surviving_column_bad_cover hj)
    (fun i hi => hBounds.1 i (Finset.mem_inter.mp hi).2)
    (fun i hi => hBounds.2.1 i (Finset.mem_inter.mp hi).2)
    (fun i hi => hBounds.2.2.1 i (Finset.mem_inter.mp hi).2)
  have hCount (J : Finset (Fin n)) :
      (((rowSliceColumnSupport rows j \ F) ∩ J).card : ℝ) ≤ rowSliceColumnSubsetLoad rows J j := by
    rw [rowSliceColumnSubsetLoad_eq_inter_card]
    have hSub : (rowSliceColumnSupport rows j \ F) ∩ J ⊆ rowSliceColumnSupport rows j ∩ J := by
      intro i hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).1).1,
        (Finset.mem_inter.mp hi).2⟩
    exact_mod_cast Finset.card_le_card hSub
  apply h.trans
  calc
    _ ≤ rowSliceColumnSubsetLoad rows (llyBadSecond x F k₁ k₂) j * (5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖) +
        rowSliceColumnSubsetLoad rows (llyBadThird x F k₂ k₃) j * (5 * ‖c‖) +
        rowSliceColumnSubsetLoad rows (llyBadTail x F k₃) j * (5 / 4 * ‖c‖) := by
      gcongr <;> exact hCount _
    _ = _ := by ring

theorem lly_surviving_column_bad_count {n d k₁ k₂ k₃ : ℕ}
    {rows : RowSliceMatrix n d} {x : Fin n → ℂ} {F : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    ((rowSliceColumnSupport rows j \ F).card : ℝ) ≤
      rowSliceColumnSubsetLoad rows (llyBadSecond x F k₁ k₂) j +
      rowSliceColumnSubsetLoad rows (llyBadThird x F k₂ k₃) j +
      rowSliceColumnSubsetLoad rows (llyBadTail x F k₃) j := by
  have h := finite_three_block_sum_bound (rowSliceColumnSupport rows j \ F)
    (llyBadSecond x F k₁ k₂) (llyBadThird x F k₂ k₃) (llyBadTail x F k₃) (fun _ => (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (lly_surviving_column_bad_cover hj)
    (fun _ _ => le_refl _) (fun _ _ => le_refl _) (fun _ _ => le_refl _)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hCount (J : Finset (Fin n)) :
      (((rowSliceColumnSupport rows j \ F) ∩ J).card : ℝ) ≤ rowSliceColumnSubsetLoad rows J j := by
    rw [rowSliceColumnSubsetLoad_eq_inter_card]
    have hSub : (rowSliceColumnSupport rows j \ F) ∩ J ⊆ rowSliceColumnSupport rows j ∩ J := by
      intro i hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).1).1,
        (Finset.mem_inter.mp hi).2⟩
    exact_mod_cast Finset.card_le_card hSub
  apply h.trans
  exact add_le_add (add_le_add (hCount _) (hCount _)) (hCount _)

end CircularLaw
