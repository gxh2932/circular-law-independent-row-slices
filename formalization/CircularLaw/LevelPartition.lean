import CircularLaw.LevelSlices

/-!
# Actual levels of a complex vector

The ordered level procedure partitions the original coordinates. Selected
levels are disjoint within and between orders. A part formed from any
family of represented values has the source size-height bounds and
balanced fibers, connecting the construction to regular-block concentration.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def initialLevel {n : ℕ} (y : Fin n → ℂ) (z : ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => y i = z)

def selectedLevelAt {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (z : ℂ) : Finset (Fin n) :=
  orderChunk (levelRemainder (initialLevel y z) j) j

def representedValues {n : ℕ} (y : Fin n → ℂ) (j : ℕ) : Finset ℂ :=
  (Finset.univ.image y).filter (fun z => (selectedLevelAt y j z).Nonempty)

def levelPart {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ) : Finset (Fin n) :=
  A.biUnion (selectedLevelAt y j)

theorem selectedLevelAt_value {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (z : ℂ)
    {i : Fin n} (hi : i ∈ selectedLevelAt y j z) : y i = z := by
  have h := levelRemainder_subset (initialLevel y z) j
    (orderChunk_subset _ _ hi)
  exact (Finset.mem_filter.mp h).2

theorem selectedLevelAt_disjoint_values {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    {z w : ℂ} (hzw : z ≠ w) : Disjoint (selectedLevelAt y j z) (selectedLevelAt y j w) := by
  apply Finset.disjoint_left.mpr
  intro i hiz hiw
  exact hzw ((selectedLevelAt_value y j z hiz).symm.trans (selectedLevelAt_value y j w hiw))

theorem selectedLevelAt_disjoint_orders {n : ℕ} (y : Fin n → ℂ) (z : ℂ)
    {j l : ℕ} (hjl : j < l) : Disjoint (selectedLevelAt y j z) (selectedLevelAt y l z) :=
  selectedLevels_disjoint _ hjl

theorem selectedLevelAt_nonempty_mem {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (z : ℂ) :
    (selectedLevelAt y j z).Nonempty ↔ z ∈ representedValues y j := by
  classical
  constructor
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    obtain ⟨i, hi⟩ := h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, selectedLevelAt_value y j z hi⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

theorem initialLevel_remainder_empty {n : ℕ} (y : Fin n → ℂ) (z : ℂ) :
    levelRemainder (initialLevel y z) (n + 2) = ∅ := by
  apply levelRemainder_empty_of_card_lt
  have hCard : (initialLevel y z).card ≤ n := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simp only [Finset.card_univ, Fintype.card_fin])
  have hPow : n < 2 ^ (n + 1) :=
    (Nat.lt_two_pow_self (n := n)).trans_le (by rw [pow_succ]; omega)
  have hIndex : n + 2 - 1 = n + 1 := by omega
  rw [hIndex]
  exact hCard.trans_lt hPow

theorem selectedLevelAt_cover {n : ℕ} (y : Fin n → ℂ) (z : ℂ) :
    (Finset.range (n + 2)).biUnion (fun j => selectedLevelAt y j z) = initialLevel y z :=
  selectedLevels_cover _ _ (initialLevel_remainder_empty y z)

theorem selectedLevelAt_coordinate {n : ℕ} (y : Fin n → ℂ) (i : Fin n) :
    ∃ j < n + 2, i ∈ selectedLevelAt y j (y i) := by
  classical
  have hi : i ∈ initialLevel y (y i) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩
  rw [← selectedLevelAt_cover] at hi
  obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hi
  exact ⟨j, Finset.mem_range.mp hj, hi⟩

theorem levelPart_card {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ) :
    (levelPart y j A).card = ∑ z ∈ A, (selectedLevelAt y j z).card := by
  classical
  apply Finset.card_biUnion
  intro z hz w hw hzw
  exact selectedLevelAt_disjoint_values y j hzw

theorem levelPart_size_height {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    (A : Finset ℂ) (hA : A ⊆ representedValues y j) :
    2 ^ (j - 1) * A.card ≤ (levelPart y j A).card ∧
      (levelPart y j A).card ≤ 2 ^ (j + 1) * A.card := by
  classical
  rw [levelPart_card]
  constructor
  · calc
      _ = ∑ _z ∈ A, (2 : ℕ) ^ (j - 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun z hz =>
        (selectedLevel_card_bounds _ _ ((selectedLevelAt_nonempty_mem y j z).mpr (hA hz))).1)
  · calc
      _ ≤ ∑ _z ∈ A, (2 : ℕ) ^ (j + 1) := Finset.sum_le_sum (fun z hz =>
        (selectedLevel_card_bounds _ _ ((selectedLevelAt_nonempty_mem y j z).mpr (hA hz))).2.le)
      _ = _ := by simp [mul_comm]

theorem levelPart_nonempty_iff {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    (A : Finset ℂ) (hA : A ⊆ representedValues y j) :
    (levelPart y j A).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    obtain ⟨z, hz, _⟩ := Finset.mem_biUnion.mp hi
    exact ⟨z, hz⟩
  · intro h
    obtain ⟨z, hz⟩ := h
    obtain ⟨i, hi⟩ := (selectedLevelAt_nonempty_mem y j z).mpr (hA hz)
    exact ⟨i, Finset.mem_biUnion.mpr ⟨z, hz, hi⟩⟩

/-- The literal source powers, including the negative exponent at order
zero. The natural-number lower bound above is stronger at that order. -/
theorem levelPart_size_height_source {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    (A : Finset ℂ) (hA : A ⊆ representedValues y j) :
    (2 : ℝ) ^ ((j : ℤ) - 1) * (A.card : ℝ) ≤ (levelPart y j A).card ∧
      ((levelPart y j A).card : ℝ) ≤ (2 : ℝ) ^ ((j : ℤ) + 1) * (A.card : ℝ) := by
  have hBounds := levelPart_size_height y j A hA
  cases j with
  | zero =>
    simp only [Nat.zero_sub, pow_zero, one_mul, zero_add, pow_one] at hBounds
    have hLow : (A.card : ℝ) ≤ (levelPart y 0 A).card := by
      exact_mod_cast hBounds.1
    have hHigh : ((levelPart y 0 A).card : ℝ) ≤ 2 * (A.card : ℝ) := by
      exact_mod_cast hBounds.2
    norm_num
    exact ⟨by linarith [Nat.cast_nonneg A.card (α := ℝ)], hHigh⟩
  | succ j =>
    have hIndexLow : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    have hIndexHigh : ((j + 1 : ℕ) : ℤ) + 1 = ((j + 2 : ℕ) : ℤ) := by omega
    rw [hIndexLow, hIndexHigh, zpow_natCast, zpow_natCast]
    have hLow : 2 ^ j * A.card ≤ (levelPart y (j + 1) A).card := by
      simpa only [Nat.add_sub_cancel] using hBounds.1
    have hHigh : (levelPart y (j + 1) A).card ≤ 2 ^ (j + 2) * A.card := by
      simpa only [Nat.add_assoc] using hBounds.2
    exact ⟨by exact_mod_cast hLow, by exact_mod_cast hHigh⟩

end CircularLaw
