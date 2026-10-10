import CircularLaw.LevelInvariants

/-!
# Exact counts and majority transfer for selected levels

The selected-level recursion has an explicit survival threshold. A level
with more than half the coordinates of another level survives through
at least the preceding creation order. These are the count facts used
in LLTTY19 Lemmas 5.2 and 5.9.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem levelRemainder_card_add_of_nonempty {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) (h : (levelRemainder s j).Nonempty) :
    (levelRemainder s j).card + (2 ^ j - 1) = s.card := by
  induction j with
  | zero => simp only [levelRemainder, pow_zero, Nat.sub_self, add_zero]
  | succ j ih =>
    have hPrev : (levelRemainder s j).Nonempty :=
      h.mono (Finset.sdiff_subset : levelRemainder s (j + 1) ⊆ levelRemainder s j)
    have hCount := levelRemainder_card_succ s j
    have hPos := Finset.card_pos.mpr h
    have hHigh : 2 ^ (j + 1) ≤ (levelRemainder s j).card := by
      by_contra hLow
      rw [if_pos (by omega)] at hCount
      omega
    rw [if_neg (by omega)] at hCount
    have hOld := ih hPrev
    have hPow : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) _
    rw [pow_succ] at hHigh ⊢
    omega

theorem levelRemainder_nonempty_succ_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) :
    (levelRemainder s (j + 1)).Nonempty ↔ 3 * 2 ^ j ≤ s.card + 1 := by
  induction j with
  | zero =>
    rw [← Finset.card_pos, levelRemainder_card_succ]
    simp only [levelRemainder, zero_add, pow_one, pow_zero]
    split_ifs <;> omega
  | succ j ih =>
    constructor
    · intro h
      have hPrev : (levelRemainder s (j + 1)).Nonempty :=
        h.mono (Finset.sdiff_subset : levelRemainder s (j + 1 + 1) ⊆
          levelRemainder s (j + 1))
      have hCount := levelRemainder_card_succ s (j + 1)
      have hPos := Finset.card_pos.mpr h
      have hHigh : 2 ^ (j + 1 + 1) ≤ (levelRemainder s (j + 1)).card := by
        by_contra hLow
        rw [if_pos (by omega)] at hCount
        omega
      have hOld := levelRemainder_card_add_of_nonempty s (j + 1) hPrev
      have hPow : 0 < (2 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
      rw [pow_succ] at hHigh
      omega
    · intro h
      have hPrev : (levelRemainder s (j + 1)).Nonempty := ih.mpr (by
        rw [pow_succ] at h
        omega)
      have hOld := levelRemainder_card_add_of_nonempty s (j + 1) hPrev
      have hPow : 0 < (2 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
      have hHigh : 2 ^ (j + 1 + 1) ≤ (levelRemainder s (j + 1)).card := by
        rw [pow_succ]
        omega
      rw [← Finset.card_pos, levelRemainder_card_succ, if_neg (by omega)]
      rw [pow_succ] at hHigh
      omega

theorem selectedLevel_nonempty_succ_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) :
    (orderChunk (levelRemainder s (j + 1)) (j + 1)).Nonempty ↔
      3 * 2 ^ j ≤ s.card + 1 := by
  rw [orderChunk_nonempty_iff, levelRemainder_nonempty_succ_iff]

theorem levelRemainder_card_formula {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) :
    (levelRemainder s (j + 1)).card =
      if 3 * 2 ^ j ≤ s.card + 1 then s.card + 1 - 2 ^ (j + 1) else 0 := by
  split_ifs with h
  · have hCount := levelRemainder_card_add_of_nonempty s (j + 1)
      ((levelRemainder_nonempty_succ_iff s j).mpr h)
    have hPow : 0 < (2 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
    omega
  · have hEmpty : levelRemainder s (j + 1) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (by
        rw [levelRemainder_nonempty_succ_iff]
        exact h)
    rw [hEmpty, Finset.card_empty]

theorem selectedLevel_majority_previous {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β) (j : ℕ) (hMajority : s.card < 2 * t.card)
    (h : (orderChunk (levelRemainder s j) j).Nonempty) :
    (orderChunk (levelRemainder t (j - 1)) (j - 1)).Nonempty := by
  rw [orderChunk_nonempty_iff] at h ⊢
  cases j with
  | zero =>
    simp only [levelRemainder, ← Finset.card_pos]
    omega
  | succ j =>
    simp only [Nat.add_sub_cancel]
    cases j with
    | zero =>
      simp only [levelRemainder, ← Finset.card_pos]
      omega
    | succ j =>
      rw [levelRemainder_nonempty_succ_iff]
      have hLow := (levelRemainder_nonempty_succ_iff s (j + 1)).mp h
      rw [pow_succ] at hLow
      omega

theorem selectedLevelAt_nonempty_succ_iff {n : ℕ} (y : Fin n → ℂ) (z : ℂ) (j : ℕ) :
    (selectedLevelAt y (j + 1) z).Nonempty ↔
      3 * 2 ^ j ≤ (initialLevel y z).card + 1 :=
  selectedLevel_nonempty_succ_iff (initialLevel y z) j

def selectedLevelPrefix {α : Type*} [LinearOrder α] (s : Finset α) (J : ℕ) : Finset α :=
  (Finset.range J).biUnion (fun j => orderChunk (levelRemainder s j) j)

theorem selectedLevelPrefix_disjoint_remainder {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) : Disjoint (levelRemainder s J) (selectedLevelPrefix s J) := by
  apply Finset.disjoint_left.mpr
  intro i hiR hiP
  obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hiP
  have hNext := levelRemainder_antitone s
    (Nat.succ_le_of_lt (Finset.mem_range.mp hj)) hiR
  exact (Finset.mem_sdiff.mp hNext).2 hi

theorem selectedLevelPrefix_card_add {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) :
    (levelRemainder s J).card + (selectedLevelPrefix s J).card = s.card := by
  rw [← Finset.card_union_of_disjoint (selectedLevelPrefix_disjoint_remainder s J)]
  exact congrArg Finset.card (selectedLevels_union_remainder s J)

theorem selectedLevelPrefix_card_of_survival {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) (h : (levelRemainder s J).Nonempty) :
    (selectedLevelPrefix s J).card = 2 ^ J - 1 := by
  have hAll := selectedLevelPrefix_card_add s J
  have hR := levelRemainder_card_add_of_nonempty s J h
  omega

theorem selectedLevelPrefix_card_of_exhaustion {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) (h : levelRemainder s J = ∅) :
    (selectedLevelPrefix s J).card = s.card := by
  simpa only [h, Finset.card_empty, zero_add] using selectedLevelPrefix_card_add s J

theorem selectedLevelPrefix_card_bounds {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) :
    min s.card (2 ^ J - 1) ≤ (selectedLevelPrefix s J).card ∧
      (selectedLevelPrefix s J).card ≤ min s.card (2 ^ (J + 1) - 1) := by
  have hAll := selectedLevelPrefix_card_add s J
  by_cases hR : (levelRemainder s J).Nonempty
  · have hCount := selectedLevelPrefix_card_of_survival s J hR
    rw [hCount] at hAll ⊢
    have hPow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (Nat.le_succ J)
    exact ⟨min_le_right _ _, le_min (by omega) (Nat.sub_le_sub_right hPow 1)⟩
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hR
    rw [selectedLevelPrefix_card_of_exhaustion s J hEmpty]
    constructor
    · exact min_le_left _ _
    · cases J with
      | zero =>
        have hZero : s.card = 0 := congrArg Finset.card hEmpty
        simp [hZero]
      | succ J =>
        have hSmall : ¬3 * 2 ^ J ≤ s.card + 1 := by
          rw [← levelRemainder_nonempty_succ_iff]
          exact hR
        have hPow : 0 < (2 : ℕ) ^ J := pow_pos (by norm_num) _
        simp only [pow_succ]
        omega

theorem selectedLevelPrefix_card_one {α : Type*} [LinearOrder α] (s : Finset α) :
    (selectedLevelPrefix s 1).card = min s.card 1 := by
  simp only [selectedLevelPrefix, Finset.range_one, Finset.singleton_biUnion,
    levelRemainder, orderChunk_card, zero_add, pow_one, pow_zero]
  split_ifs <;> omega

theorem selectedLevelPrefix_majority_card {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β) (J : ℕ) (hMajority : s.card < 2 * t.card) :
    (selectedLevelPrefix s (J + 1)).card ≤
      8 * (selectedLevelPrefix t (J - 1 + 1)).card := by
  cases J with
  | zero =>
    simp only [zero_add, Nat.zero_sub, selectedLevelPrefix_card_one]
    omega
  | succ J =>
    simp only [Nat.add_sub_cancel]
    by_cases hR : (levelRemainder t (J + 1)).Nonempty
    · rw [selectedLevelPrefix_card_of_survival t (J + 1) hR]
      have hUpper := (selectedLevelPrefix_card_bounds s (J + 1 + 1)).2
      have hPow : 0 < (2 : ℕ) ^ J := pow_pos (by norm_num) _
      simp only [pow_succ] at hUpper ⊢
      omega
    · rw [selectedLevelPrefix_card_of_exhaustion t (J + 1)
        (Finset.not_nonempty_iff_eq_empty.mp hR)]
      have hAll := selectedLevelPrefix_card_add s (J + 1 + 1)
      omega

end CircularLaw
