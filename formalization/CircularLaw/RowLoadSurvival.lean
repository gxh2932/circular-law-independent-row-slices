import CircularLaw.RowLoadRates

/-!
# Surviving rows on the source row-load event

Remove the three actual exceptional row sets and the prescribed top
coordinate indices. The retained-row count is the source `K-3*K/8-n3`
bound, including a uniform lower bound of `n/2` in the required regime.
-/

noncomputable section
open Classical

namespace CircularLaw

def loadExceptionalRows {n d : ℕ} (I J : Finset (Fin n)) (t : ℝ)
    (rows : RowSliceMatrix n d) : Finset (Fin n) :=
  I.filter (fun i => t ≤ rowLoad (rows i) J)

def rowLoadSurvivors {n d : ℕ} (I top J₂ J₃ J₄ : Finset (Fin n)) (k : ℕ)
    (rows : RowSliceMatrix n d) : Finset (Fin n) :=
  I \ (loadExceptionalRows I J₂ 1 rows ∪
    loadExceptionalRows I J₃ (16 * (k : ℝ) * d / n) rows ∪
    loadExceptionalRows I J₄ (16 * (k : ℝ) * d / n) rows ∪ top)

theorem rowLoadSurvivors_mem {n d k : ℕ} {I top J₂ J₃ J₄ : Finset (Fin n)}
    {rows : RowSliceMatrix n d} {i : Fin n}
    (hi : i ∈ rowLoadSurvivors I top J₂ J₃ J₄ k rows) :
    i ∈ I ∧ i ∉ top ∧ (rowLoad (rows i) J₂ : ℝ) < 1 ∧
      (rowLoad (rows i) J₃ : ℝ) < 16 * (k : ℝ) * d / n ∧
      (rowLoad (rows i) J₄ : ℝ) < 16 * (k : ℝ) * d / n := by
  rcases Finset.mem_sdiff.mp hi with ⟨hiI, hBad⟩
  change i ∉ loadExceptionalRows I J₂ 1 rows ∪
    loadExceptionalRows I J₃ (16 * (k : ℝ) * d / n) rows ∪
    loadExceptionalRows I J₄ (16 * (k : ℝ) * d / n) rows ∪ top at hBad
  have hTop : i ∉ top := fun h => hBad (Finset.mem_union_right _ h)
  have h₂ : ¬(1 : ℝ) ≤ rowLoad (rows i) J₂ := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hiI, h⟩))))
  have h₃ : ¬16 * (k : ℝ) * d / n ≤ rowLoad (rows i) J₃ := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hiI, h⟩))))
  have h₄ : ¬16 * (k : ℝ) * d / n ≤ rowLoad (rows i) J₄ := by
    intro h
    exact hBad (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hiI, h⟩)))
  exact ⟨hiI, hTop, lt_of_not_ge h₂, lt_of_not_ge h₃, lt_of_not_ge h₄⟩

theorem source_row_load_survivors_card {n d k : ℕ} {I top J₂ J₃ J₄ : Finset (Fin n)}
    {rows : RowSliceMatrix n d} (hLoad : SourceRowLoad I k rows)
    (hJ₂ : J₂.card ≤ almostConstantRank n d) (hJ₃ : J₃.card ≤ k) (hJ₄ : J₄.card ≤ k) :
    (I.card : ℝ) - 3 * (I.card : ℝ) / 8 - top.card ≤
      (rowLoadSurvivors I top J₂ J₃ J₄ k rows).card := by
  have h₂ := hLoad.1 J₂ hJ₂
  have h₃ := hLoad.2 J₃ hJ₃
  have h₄ := hLoad.2 J₄ hJ₄
  rw [retainedEventCount_eq_filter] at h₂ h₃ h₄
  let B₂ := loadExceptionalRows I J₂ 1 rows
  let B₃ := loadExceptionalRows I J₃ (16 * (k : ℝ) * d / n) rows
  let B₄ := loadExceptionalRows I J₄ (16 * (k : ℝ) * d / n) rows
  have hUnion : (B₂ ∪ B₃ ∪ B₄ ∪ top).card ≤ B₂.card + B₃.card + B₄.card + top.card := by
    have h23 := Finset.card_union_le B₂ B₃
    have h234 := Finset.card_union_le (B₂ ∪ B₃) B₄
    have hAll := Finset.card_union_le (B₂ ∪ B₃ ∪ B₄) top
    omega
  have hRemain := Finset.card_le_card_sdiff_add_card (s := I) (t := B₂ ∪ B₃ ∪ B₄ ∪ top)
  have hUnionR : ((B₂ ∪ B₃ ∪ B₄ ∪ top).card : ℝ) ≤
      (B₂.card : ℝ) + B₃.card + B₄.card + top.card := by exact_mod_cast hUnion
  have hRemainR : (I.card : ℝ) ≤ (rowLoadSurvivors I top J₂ J₃ J₄ k rows).card +
      (B₂ ∪ B₃ ∪ B₄ ∪ top).card := by exact_mod_cast hRemain
  change (B₂.card : ℝ) ≤ (I.card : ℝ) / 8 at h₂
  change (B₃.card : ℝ) ≤ (I.card : ℝ) / 8 at h₃
  change (B₄.card : ℝ) ≤ (I.card : ℝ) / 8 at h₄
  linarith

theorem source_row_load_survivors_half {n d k : ℕ} {I top J₂ J₃ J₄ : Finset (Fin n)}
    {rows : RowSliceMatrix n d} (hLoad : SourceRowLoad I k rows)
    (hJ₂ : J₂.card ≤ almostConstantRank n d) (hJ₃ : J₃.card ≤ k) (hJ₄ : J₄.card ≤ k)
    (hRows : (99 / 100 : ℝ) * n ≤ I.card) (hTop : (top.card : ℝ) ≤ (n : ℝ) / 1000) :
    (n : ℝ) / 2 ≤ (rowLoadSurvivors I top J₂ J₃ J₄ k rows).card := by
  have h := source_row_load_survivors_card (top := top) hLoad hJ₂ hJ₃ hJ₄
  linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

end CircularLaw
