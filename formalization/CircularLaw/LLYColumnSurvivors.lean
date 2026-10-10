import CircularLaw.LLYAlmostConstantBlocks
import CircularLaw.RowSliceColumnSubsetLoads

/-!
# Columns surviving the four almost-constant exceptional blocks

All exceptional sets are counted deterministically, for every actual
fixed-degree sample and every vector. Empty blocks are permitted. The
second block retains its separate rank k2 in the load cutoff.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem rowSliceHeavySubsetColumns_fixed_rank_bound {m n d k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) (rows : Fin m → RowSlice n d)
    (J : Finset (Fin m)) (hJ : J.card ≤ k) :
    ((rowSliceHeavySubsetColumns rows J (9 * (k : ℝ) * d / n)).card : ℝ) ≤
      (n : ℝ) / 9 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDK : 0 < (d : ℝ) * k := mul_pos (by exact_mod_cast hd) (by exact_mod_cast hk)
  have h := rowSliceHeavySubsetColumns_mass_bound rows J (9 * (k : ℝ) * d / n)
  have hJR : (J.card : ℝ) ≤ k := by exact_mod_cast hJ
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 9)).mpr
  apply (mul_le_mul_iff_right₀ hDK).mp
  calc
    _ = (n : ℝ) * (((rowSliceHeavySubsetColumns rows J (9 * (k : ℝ) * d / n)).card : ℝ) *
        (9 * (k : ℝ) * d / n)) := by field_simp
    _ ≤ (n : ℝ) * ((d : ℝ) * J.card) := mul_le_mul_of_nonneg_left h hnR.le
    _ ≤ (n : ℝ) * ((d : ℝ) * k) := by gcongr
    _ = _ := by ring

theorem rowSliceHeavySubsetColumns_one_bound {m n d : ℕ}
    (rows : Fin m → RowSlice n d) (J : Finset (Fin m)) :
    ((rowSliceHeavySubsetColumns rows J 1).card : ℝ) ≤ (d : ℝ) * J.card := by
  simpa only [mul_one] using rowSliceHeavySubsetColumns_mass_bound rows J 1

def llyColumnSurvivors {n d : ℕ} (rows : RowSliceMatrix n d) (x : Fin n → ℂ)
    (F : Finset (Fin n)) (k₁ k₂ k₃ : ℕ) : Finset (Fin n) :=
  Finset.univ \ (rowSliceHeavySubsetColumns rows (llyBadTop x F k₁) 1 ∪
    rowSliceHeavySubsetColumns rows (llyBadSecond x F k₁ k₂) (9 * (k₂ : ℝ) * d / n) ∪
    rowSliceHeavySubsetColumns rows (llyBadThird x F k₂ k₃) (9 * (k₃ : ℝ) * d / n) ∪
    rowSliceHeavySubsetColumns rows (llyBadTail x F k₃) (9 * (k₃ : ℝ) * d / n) ∪
    orderedPrefix x k₃)

theorem llyColumnSurvivors_mem {n d k₁ k₂ k₃ : ℕ}
    {rows : RowSliceMatrix n d} {x : Fin n → ℂ} {F : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    j ∉ orderedPrefix x k₃ ∧ rowSliceColumnSubsetLoad rows (llyBadTop x F k₁) j < 1 ∧
      rowSliceColumnSubsetLoad rows (llyBadSecond x F k₁ k₂) j < 9 * (k₂ : ℝ) * d / n ∧
      rowSliceColumnSubsetLoad rows (llyBadThird x F k₂ k₃) j < 9 * (k₃ : ℝ) * d / n ∧
      rowSliceColumnSubsetLoad rows (llyBadTail x F k₃) j < 9 * (k₃ : ℝ) * d / n := by
  have hBad := (Finset.mem_sdiff.mp hj).2
  simp only [Finset.mem_union, rowSliceHeavySubsetColumns,
    Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hBad
  exact ⟨hBad.2, lt_of_not_ge hBad.1.1.1.1, lt_of_not_ge hBad.1.1.1.2,
    lt_of_not_ge hBad.1.1.2, lt_of_not_ge hBad.1.2⟩

theorem llyColumnSurvivors_half_of_prefix {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hMany : n - k₃ < F.card) (hTop : (d : ℝ) * (k₁ - 1 : ℕ) ≤ (n : ℝ) / 9)
    (hTail : (k₃ : ℝ) ≤ (n : ℝ) / 1000) :
    (n : ℝ) / 2 ≤ (llyColumnSurvivors rows x F k₁ k₂ k₃).card := by
  have hCards := lly_bad_blocks_card_bounds x F hk₁n hk₂n hMany
  let B₁ := rowSliceHeavySubsetColumns rows (llyBadTop x F k₁) 1
  let B₂ := rowSliceHeavySubsetColumns rows (llyBadSecond x F k₁ k₂) (9 * (k₂ : ℝ) * d / n)
  let B₃ := rowSliceHeavySubsetColumns rows (llyBadThird x F k₂ k₃) (9 * (k₃ : ℝ) * d / n)
  let B₄ := rowSliceHeavySubsetColumns rows (llyBadTail x F k₃) (9 * (k₃ : ℝ) * d / n)
  have h₁ : (B₁.card : ℝ) ≤ (n : ℝ) / 9 := by
    apply (rowSliceHeavySubsetColumns_one_bound rows (llyBadTop x F k₁)).trans
    have hCardR : ((llyBadTop x F k₁).card : ℝ) ≤ (k₁ - 1 : ℕ) := by
      exact_mod_cast lly_bad_top_strict_prefix_card x F hk₁n
    exact (mul_le_mul_of_nonneg_left hCardR (Nat.cast_nonneg d)).trans hTop
  have h₂ : (B₂.card : ℝ) ≤ (n : ℝ) / 9 :=
    rowSliceHeavySubsetColumns_fixed_rank_bound hn hd hk₂ rows _ hCards.2.1
  have h₃ : (B₃.card : ℝ) ≤ (n : ℝ) / 9 :=
    rowSliceHeavySubsetColumns_fixed_rank_bound hn hd hk₃ rows _ hCards.2.2.1
  have h₄ : (B₄.card : ℝ) ≤ (n : ℝ) / 9 :=
    rowSliceHeavySubsetColumns_fixed_rank_bound hn hd hk₃ rows _ hCards.2.2.2
  have hUnion : (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card ≤
      B₁.card + B₂.card + B₃.card + B₄.card + (orderedPrefix x k₃).card := by
    have h12 := Finset.card_union_le B₁ B₂
    have h123 := Finset.card_union_le (B₁ ∪ B₂) B₃
    have h1234 := Finset.card_union_le (B₁ ∪ B₂ ∪ B₃) B₄
    have hAll := Finset.card_union_le (B₁ ∪ B₂ ∪ B₃ ∪ B₄) (orderedPrefix x k₃)
    omega
  have hRemain := Finset.card_le_card_sdiff_add_card (s := (Finset.univ : Finset (Fin n)))
    (t := B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃)
  have hRemainR : (n : ℝ) ≤ (llyColumnSurvivors rows x F k₁ k₂ k₃).card +
      (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using (by exact_mod_cast hRemain :
      ((Finset.univ : Finset (Fin n)).card : ℝ) ≤
        (Finset.univ \ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃)).card +
          (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card)
  have hUnionR : ((B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ orderedPrefix x k₃).card : ℝ) ≤
      (B₁.card : ℝ) + B₂.card + B₃.card + B₄.card + k₃ := by
    rw [orderedPrefix_card x hk₃n] at hUnion
    exact_mod_cast hUnion
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem llyColumnSurvivors_half {n d k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (rows : RowSliceMatrix n d) (x : Fin n → ℂ) (F : Finset (Fin n))
    (hMany : n - k₃ < F.card) (hTop : (d : ℝ) * k₁ ≤ (n : ℝ) / 9)
    (hTail : (k₃ : ℝ) ≤ (n : ℝ) / 1000) :
    (n : ℝ) / 2 ≤ (llyColumnSurvivors rows x F k₁ k₂ k₃).card := by
  apply llyColumnSurvivors_half_of_prefix hn hd hk₂ hk₃ hk₁n hk₂n hk₃n rows x F hMany ?_ hTail
  have hRank : ((k₁ - 1 : ℕ) : ℝ) ≤ k₁ := by exact_mod_cast Nat.sub_le k₁ 1
  exact (mul_le_mul_of_nonneg_left hRank (Nat.cast_nonneg d)).trans hTop

theorem llyColumnSurvivors_top_avoided {n d k₁ k₂ k₃ : ℕ}
    {rows : RowSliceMatrix n d} {x : Fin n → ℂ} {F : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ llyColumnSurvivors rows x F k₁ k₂ k₃) :
    ∀ i ∈ llyBadTop x F k₁, j ∉ (rows i).val := by
  have h := (llyColumnSurvivors_mem hj).2.1
  rw [rowSliceColumnSubsetLoad_eq_card] at h
  have hNat : ((llyBadTop x F k₁).filter (fun i => j ∈ (rows i).val)).card < 1 := by
    exact_mod_cast h
  have hEmpty := Finset.card_eq_zero.mp (by omega :
    ((llyBadTop x F k₁).filter (fun i => j ∈ (rows i).val)).card = 0)
  intro i hi hRow
  have hMem : i ∈ (llyBadTop x F k₁).filter (fun i => j ∈ (rows i).val) :=
    Finset.mem_filter.mpr ⟨hi, hRow⟩
  rw [hEmpty] at hMem
  simp at hMem

end CircularLaw
