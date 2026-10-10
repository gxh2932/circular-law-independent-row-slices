import CircularLaw.BernoulliUniformRowLoad
import CircularLaw.LLYRowSurvivors

/-!
# Bernoulli rows surviving the LLY bad-coordinate blocks

The uniform load events give the same retained-row count as the slice
geometry, with the ambient degree used only in the load thresholds.
-/

noncomputable section
open Classical

namespace CircularLaw

def bernoulliLoadExceptionalRows {n : ℕ} (I J : Finset (Fin n)) (t : ℝ)
    (sample : BernoulliSquareSample n) : Finset (Fin n) :=
  I.filter (fun i => t ≤ (bernoulliRowLoad (fun j => sample (i, j)) J : ℝ))

def bernoulliLLYRowSurvivors {n : ℕ} (d : ℕ) (I : Finset (Fin n))
    (sample : BernoulliSquareSample n) (x : Fin n → ℂ) (F : Finset (Fin n))
    (k₁ k₂ k₃ : ℕ) : Finset (Fin n) :=
  I \ (bernoulliLoadExceptionalRows I (llyBadTop x F k₁) 1 sample ∪
    bernoulliLoadExceptionalRows I (llyBadSecond x F k₁ k₂) (16 * (k₂ : ℝ) * d / n) sample ∪
    bernoulliLoadExceptionalRows I (llyBadThird x F k₂ k₃) (16 * (k₃ : ℝ) * d / n) sample ∪
    bernoulliLoadExceptionalRows I (llyBadTail x F k₃) (16 * (k₃ : ℝ) * d / n) sample ∪
    orderedPrefix x k₃)

theorem bernoulli_lly_row_survivors_mem {n d k₁ k₂ k₃ : ℕ}
    {I : Finset (Fin n)} {sample : BernoulliSquareSample n} {x : Fin n → ℂ}
    {F : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ bernoulliLLYRowSurvivors d I sample x F k₁ k₂ k₃) :
    i ∈ I ∧ i ∉ orderedPrefix x k₃ ∧
      (bernoulliRowLoad (fun j => sample (i, j)) (llyBadTop x F k₁) : ℝ) < 1 ∧
      (bernoulliRowLoad (fun j => sample (i, j)) (llyBadSecond x F k₁ k₂) : ℝ) < 16 * (k₂ : ℝ) * d / n ∧
      (bernoulliRowLoad (fun j => sample (i, j)) (llyBadThird x F k₂ k₃) : ℝ) < 16 * (k₃ : ℝ) * d / n ∧
      (bernoulliRowLoad (fun j => sample (i, j)) (llyBadTail x F k₃) : ℝ) < 16 * (k₃ : ℝ) * d / n := by
  obtain ⟨hiI, hBad⟩ := Finset.mem_sdiff.mp hi
  have hNotTop : i ∉ orderedPrefix x k₃ := fun h => hBad (Finset.mem_union_right _ h)
  have hNot₁ : ¬(1 : ℝ) ≤ bernoulliRowLoad (fun j => sample (i, j)) (llyBadTop x F k₁) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiI, h⟩)))))
  have hNot₂ : ¬16 * (k₂ : ℝ) * d / n ≤
      bernoulliRowLoad (fun j => sample (i, j)) (llyBadSecond x F k₁ k₂) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiI, h⟩)))))
  have hNot₃ : ¬16 * (k₃ : ℝ) * d / n ≤
      bernoulliRowLoad (fun j => sample (i, j)) (llyBadThird x F k₂ k₃) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hiI, h⟩))))
  have hNot₄ : ¬16 * (k₃ : ℝ) * d / n ≤
      bernoulliRowLoad (fun j => sample (i, j)) (llyBadTail x F k₃) := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiI, h⟩)))
  exact ⟨hiI, hNotTop, lt_of_not_ge hNot₁, lt_of_not_ge hNot₂, lt_of_not_ge hNot₃, lt_of_not_ge hNot₄⟩

theorem bernoulli_lly_row_survivors_card_of_prefix {n d k₁ k₂ k₃ : ℕ}
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₁ : k₁ - 1 ≤ almostConstantRank n d)
    (hMany : n - k₃ < F.card) (hLoad : BernoulliLLYRowLoad d I k₂ k₃ sample) :
    (I.card : ℝ) / 2 - (orderedPrefix x k₃).card ≤
      (bernoulliLLYRowSurvivors d I sample x F k₁ k₂ k₃).card := by
  have hCards := lly_bad_blocks_card_bounds x F hk₁n hk₂n hMany
  have h₁ := hLoad.1.1 _ ((lly_bad_top_strict_prefix_card x F hk₁n).trans hk₁)
  have h₂ := hLoad.1.2 _ hCards.2.1
  have h₃ := hLoad.2.2 _ hCards.2.2.1
  have h₄ := hLoad.2.2 _ hCards.2.2.2
  let B₁ := bernoulliLoadExceptionalRows I (llyBadTop x F k₁) 1 sample
  let B₂ := bernoulliLoadExceptionalRows I (llyBadSecond x F k₁ k₂) (16 * (k₂ : ℝ) * d / n) sample
  let B₃ := bernoulliLoadExceptionalRows I (llyBadThird x F k₂ k₃) (16 * (k₃ : ℝ) * d / n) sample
  let B₄ := bernoulliLoadExceptionalRows I (llyBadTail x F k₃) (16 * (k₃ : ℝ) * d / n) sample
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
  have hRemainR : (I.card : ℝ) ≤ (bernoulliLLYRowSurvivors d I sample x F k₁ k₂ k₃).card +
      (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card := by exact_mod_cast hRemain
  change (B₁.card : ℝ) ≤ (I.card : ℝ) / 8 at h₁
  change (B₂.card : ℝ) ≤ (I.card : ℝ) / 8 at h₂
  change (B₃.card : ℝ) ≤ (I.card : ℝ) / 8 at h₃
  change (B₄.card : ℝ) ≤ (I.card : ℝ) / 8 at h₄
  linarith

theorem bernoulli_lly_row_survivors_third_of_prefix {n d k₁ k₂ k₃ : ℕ}
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₁ : k₁ - 1 ≤ almostConstantRank n d)
    (hMany : n - k₃ < F.card) (hLoad : BernoulliLLYRowLoad d I k₂ k₃ sample)
    (hRows : (99 / 100 : ℝ) * n ≤ I.card) (hTail : (k₃ : ℝ) ≤ (n : ℝ) / 1000) :
    (n : ℝ) / 3 ≤ (bernoulliLLYRowSurvivors d I sample x F k₁ k₂ k₃).card := by
  have h := bernoulli_lly_row_survivors_card_of_prefix I sample x F hk₁n hk₂n hk₁ hMany hLoad
  rw [orderedPrefix_card x hk₃n] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

end CircularLaw
