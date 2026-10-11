import CircularLaw.LevelSliceCounts

/-!
# A large final selected level

The last nonempty remainder is selected whole. Its coordinate count
is at least one fourth of the original level, while that original
count is at most eight times the lower size at its creation order.
These are the exact finite level facts needed for the low-weight bin.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem exhausting_level_chunk_whole {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) (hNext : levelRemainder s (j + 1) = ∅) :
    orderChunk (levelRemainder s j) j = levelRemainder s j := by
  have hCount := levelRemainder_card_succ s j
  have hEmpty : (levelRemainder s (j + 1)).card = 0 := by rw [hNext, Finset.card_empty]
  have hp : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) _
  have hSmall : (levelRemainder s j).card < 2 ^ (j + 1) := by
    by_contra h
    rw [if_neg h] at hCount
    have hLarge : 2 * 2 ^ j ≤ (levelRemainder s j).card := by
      simpa only [pow_succ, mul_comm] using Nat.le_of_not_gt h
    omega
  exact if_pos hSmall

theorem exhausting_level_chunk_bounds {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) (hR : (levelRemainder s j).Nonempty)
    (hNext : levelRemainder s (j + 1) = ∅) :
    s.card ≤ 4 * (orderChunk (levelRemainder s j) j).card ∧
      s.card ≤ 8 * 2 ^ (j - 1) := by
  rw [exhausting_level_chunk_whole s j hNext]
  have hAdd := levelRemainder_card_add_of_nonempty s j hR
  have hLow := levelRemainder_nonempty_lower s j hR
  have hHigh := (selectedLevel_card_bounds s j ((orderChunk_nonempty_iff _ _).mpr hR)).2
  rw [exhausting_level_chunk_whole s j hNext] at hHigh
  cases j with
  | zero => simp only [pow_zero, Nat.sub_self, add_zero, Nat.zero_sub, zero_add, pow_one] at *; omega
  | succ j => simp only [Nat.add_sub_cancel, pow_succ] at *; omega

theorem selectedLevel_large_final_chunk {α : Type*} [LinearOrder α]
    (s : Finset α) {J : ℕ} (hs : s.Nonempty) (hJ : levelRemainder s J = ∅) :
    ∃ j < J, (orderChunk (levelRemainder s j) j).Nonempty ∧
      s.card ≤ 4 * (orderChunk (levelRemainder s j) j).card ∧
      s.card ≤ 8 * 2 ^ (j - 1) := by
  have hExists : ∃ t : ℕ, levelRemainder s t = ∅ := ⟨J, hJ⟩
  let t := Nat.find hExists
  have ht : levelRemainder s t = ∅ := Nat.find_spec hExists
  have htJ : t ≤ J := Nat.find_min' hExists hJ
  have htPos : 0 < t := by
    by_contra h
    have hZero : t = 0 := by omega
    have hS : s = ∅ := by simpa only [hZero, levelRemainder] using ht
    exact Finset.not_nonempty_empty (hS ▸ hs)
  have hR : (levelRemainder s (t - 1)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    exact Nat.find_min hExists (show t - 1 < t by omega)
  have hNext : levelRemainder s (t - 1 + 1) = ∅ := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using ht
  have hBounds := exhausting_level_chunk_bounds s (t - 1) hR hNext
  exact ⟨t - 1, by omega, (orderChunk_nonempty_iff _ _).mpr hR, hBounds⟩

theorem selectedLevelAt_large_final_chunk {n : ℕ} (y : Fin n → ℂ) (z : ℂ)
    (hz : (initialLevel y z).Nonempty) :
    ∃ j < n + 2, (selectedLevelAt y j z).Nonempty ∧
      (initialLevel y z).card ≤ 4 * (selectedLevelAt y j z).card ∧
      (initialLevel y z).card ≤ 8 * 2 ^ (j - 1) :=
  selectedLevel_large_final_chunk (initialLevel y z) hz (initialLevel_remainder_empty y z)

end CircularLaw
