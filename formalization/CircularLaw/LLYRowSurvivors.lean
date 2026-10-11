import CircularLaw.LLYRowLoadProbability
import CircularLaw.LLYAlmostConstantBlocks
import CircularLaw.AlmostConstantRowSets

/-!
# Retained rows surviving all four LLY bad blocks

Both uniform load events are used, with the actual second and third
rank cutoffs. The retained set may omit rows before the vector is chosen.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyRowSurvivors {n d : ℕ} (I : Finset (Fin n)) (rows : RowSliceMatrix n d)
    (x : Fin n → ℂ) (F : Finset (Fin n)) (k₁ k₂ k₃ : ℕ) : Finset (Fin n) :=
  I \ (loadExceptionalRows I (llyBadTop x F k₁) 1 rows ∪
    loadExceptionalRows I (llyBadSecond x F k₁ k₂) (16 * (k₂ : ℝ) * d / n) rows ∪
    loadExceptionalRows I (llyBadThird x F k₂ k₃) (16 * (k₃ : ℝ) * d / n) rows ∪
    loadExceptionalRows I (llyBadTail x F k₃) (16 * (k₃ : ℝ) * d / n) rows ∪
    orderedPrefix x k₃)

theorem llyRowSurvivors_mem {n d k₁ k₂ k₃ : ℕ}
    {I : Finset (Fin n)} {rows : RowSliceMatrix n d} {x : Fin n → ℂ}
    {F : Finset (Fin n)} {i : Fin n} (hi : i ∈ llyRowSurvivors I rows x F k₁ k₂ k₃) :
    i ∈ I ∧ i ∉ orderedPrefix x k₃ ∧ (rowLoad (rows i) (llyBadTop x F k₁) : ℝ) < 1 ∧
      (rowLoad (rows i) (llyBadSecond x F k₁ k₂) : ℝ) < 16 * (k₂ : ℝ) * d / n ∧
      (rowLoad (rows i) (llyBadThird x F k₂ k₃) : ℝ) < 16 * (k₃ : ℝ) * d / n ∧
      (rowLoad (rows i) (llyBadTail x F k₃) : ℝ) < 16 * (k₃ : ℝ) * d / n := by
  obtain ⟨hiI, hBad⟩ := Finset.mem_sdiff.mp hi
  have hNotTop : i ∉ orderedPrefix x k₃ := by
    intro h
    exact hBad (Finset.mem_union_right _ h)
  have hNot₁ : ¬(1 : ℝ) ≤ rowLoad (rows i) (llyBadTop x F k₁) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiI, h⟩)))))
  have hNot₂ : ¬16 * (k₂ : ℝ) * d / n ≤ rowLoad (rows i) (llyBadSecond x F k₁ k₂) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiI, h⟩)))))
  have hNot₃ : ¬16 * (k₃ : ℝ) * d / n ≤ rowLoad (rows i) (llyBadThird x F k₂ k₃) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hiI, h⟩))))
  have hNot₄ : ¬16 * (k₃ : ℝ) * d / n ≤ rowLoad (rows i) (llyBadTail x F k₃) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiI, h⟩)))
  exact ⟨hiI, hNotTop, lt_of_not_ge hNot₁, lt_of_not_ge hNot₂, lt_of_not_ge hNot₃, lt_of_not_ge hNot₄⟩

theorem llyRowSurvivors_card_of_prefix {n d k₁ k₂ k₃ : ℕ}
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₁ : k₁ - 1 ≤ almostConstantRank n d)
    (hMany : n - k₃ < F.card) (hLoad : LLYRowLoad I k₂ k₃ rows) :
    (I.card : ℝ) / 2 - (orderedPrefix x k₃).card ≤ (llyRowSurvivors I rows x F k₁ k₂ k₃).card := by
  have hCards := lly_bad_blocks_card_bounds x F hk₁n hk₂n hMany
  have h₁ := hLoad.1.1 _ ((lly_bad_top_strict_prefix_card x F hk₁n).trans hk₁)
  have h₂ := hLoad.1.2 _ hCards.2.1
  have h₃ := hLoad.2.2 _ hCards.2.2.1
  have h₄ := hLoad.2.2 _ hCards.2.2.2
  rw [retainedEventCount_eq_filter] at h₁ h₂ h₃ h₄
  let B₁ := loadExceptionalRows I (llyBadTop x F k₁) 1 rows
  let B₂ := loadExceptionalRows I (llyBadSecond x F k₁ k₂) (16 * (k₂ : ℝ) * d / n) rows
  let B₃ := loadExceptionalRows I (llyBadThird x F k₂ k₃) (16 * (k₃ : ℝ) * d / n) rows
  let B₄ := loadExceptionalRows I (llyBadTail x F k₃) (16 * (k₃ : ℝ) * d / n) rows
  have hUnion : (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card ≤
      B₁.card + B₂.card + B₃.card + B₄.card + (orderedPrefix x k₃).card := by
    have h12 := Finset.card_union_le B₁ B₂
    have h123 := Finset.card_union_le (B₁ ∪ B₂) B₃
    have h1234 := Finset.card_union_le (B₁ ∪ B₂ ∪ B₃) B₄
    have hAll := Finset.card_union_le (B₁ ∪ B₂ ∪ B₃ ∪ B₄) (orderedPrefix x k₃)
    omega
  have hRemain := Finset.card_le_card_sdiff_add_card (s := I)
    (t := B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃)
  have hUnionR : ((B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card : ℝ) ≤
      (B₁.card : ℝ) + B₂.card + B₃.card + B₄.card + (orderedPrefix x k₃).card := by
    exact_mod_cast hUnion
  have hRemainR : (I.card : ℝ) ≤ (llyRowSurvivors I rows x F k₁ k₂ k₃).card +
      (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card := by exact_mod_cast hRemain
  change (B₁.card : ℝ) ≤ (I.card : ℝ) / 8 at h₁
  change (B₂.card : ℝ) ≤ (I.card : ℝ) / 8 at h₂
  change (B₃.card : ℝ) ≤ (I.card : ℝ) / 8 at h₃
  change (B₄.card : ℝ) ≤ (I.card : ℝ) / 8 at h₄
  linarith

theorem llyRowSurvivors_card {n d k₁ k₂ k₃ : ℕ}
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₁ : k₁ ≤ almostConstantRank n d)
    (hMany : n - k₃ < F.card) (hLoad : LLYRowLoad I k₂ k₃ rows) :
    (I.card : ℝ) / 2 - (orderedPrefix x k₃).card ≤ (llyRowSurvivors I rows x F k₁ k₂ k₃).card := by
  exact llyRowSurvivors_card_of_prefix I rows x F hk₁n hk₂n ((Nat.sub_le k₁ 1).trans hk₁) hMany hLoad

theorem llyRowSurvivors_third_of_prefix {n d k₁ k₂ k₃ : ℕ}
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₁ : k₁ - 1 ≤ almostConstantRank n d)
    (hMany : n - k₃ < F.card) (hLoad : LLYRowLoad I k₂ k₃ rows)
    (hRows : (99 / 100 : ℝ) * n ≤ I.card) (hTail : (k₃ : ℝ) ≤ (n : ℝ) / 1000) :
    (n : ℝ) / 3 ≤ (llyRowSurvivors I rows x F k₁ k₂ k₃).card := by
  have h := llyRowSurvivors_card_of_prefix I rows x F hk₁n hk₂n hk₁ hMany hLoad
  rw [orderedPrefix_card x hk₃n] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem llyRowSurvivors_third {n d k₁ k₂ k₃ : ℕ}
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₁ : k₁ ≤ almostConstantRank n d)
    (hMany : n - k₃ < F.card) (hLoad : LLYRowLoad I k₂ k₃ rows)
    (hRows : (99 / 100 : ℝ) * n ≤ I.card) (hTail : (k₃ : ℝ) ≤ (n : ℝ) / 1000) :
    (n : ℝ) / 3 ≤ (llyRowSurvivors I rows x F k₁ k₂ k₃).card := by
  exact llyRowSurvivors_third_of_prefix I rows x F hk₁n hk₂n hk₃n ((Nat.sub_le k₁ 1).trans hk₁)
    hMany hLoad hRows hTail

end CircularLaw
