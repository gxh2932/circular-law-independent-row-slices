import CircularLaw.Discretization
import Mathlib.Data.Finset.Sort

/-!
# The ordered level-selection procedure

At order `j`, a remaining level smaller than `2^(j+1)` is taken whole;
otherwise its first `2^j` coordinates are taken. The remainder recursion
proves the source's level-size bounds, balance within an order, and
eventual exhaustion for the actual selected finite sets.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def orderedTake {α : Type*} [LinearOrder α] (s : Finset α) (m : ℕ) : Finset α :=
  (s.sort.take m).toFinset

theorem orderedTake_card {α : Type*} [LinearOrder α] (s : Finset α) (m : ℕ) :
    (orderedTake s m).card = min m s.card := by
  rw [orderedTake, List.toFinset_card_of_nodup ((Finset.sort_nodup s (· ≤ ·)).take (i := m)),
    List.length_take, Finset.length_sort]

theorem orderedTake_subset {α : Type*} [LinearOrder α] (s : Finset α) (m : ℕ) :
    orderedTake s m ⊆ s := by
  intro x hx
  rw [orderedTake, List.mem_toFinset] at hx
  exact (Finset.mem_sort (s := s) (· ≤ ·)).mp (List.mem_of_mem_take hx)

def orderChunk {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) : Finset α :=
  if s.card < 2 ^ (j + 1) then s else orderedTake s (2 ^ j)

theorem orderChunk_subset {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) :
    orderChunk s j ⊆ s := by
  unfold orderChunk
  split
  · exact Finset.Subset.refl _
  · exact orderedTake_subset _ _

theorem orderChunk_card {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) :
    (orderChunk s j).card = if s.card < 2 ^ (j + 1) then s.card else 2 ^ j := by
  unfold orderChunk
  split_ifs with h
  · rfl
  · rw [orderedTake_card, min_eq_left]
    have hHigh : 2 ^ (j + 1) ≤ s.card := by omega
    rw [pow_succ] at hHigh
    omega

def levelRemainder {α : Type*} [LinearOrder α] (s : Finset α) : ℕ → Finset α
  | 0 => s
  | j + 1 => levelRemainder s j \ orderChunk (levelRemainder s j) j

theorem levelRemainder_subset {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) :
    levelRemainder s j ⊆ s := by
  induction j with
  | zero => exact Finset.Subset.refl _
  | succ j ih => exact Finset.sdiff_subset.trans ih

theorem levelRemainder_card_le {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) :
    (levelRemainder s j).card ≤ s.card := Finset.card_le_card (levelRemainder_subset s j)

theorem levelRemainder_card_succ {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) :
    (levelRemainder s (j + 1)).card = (levelRemainder s j).card -
      (if (levelRemainder s j).card < 2 ^ (j + 1) then (levelRemainder s j).card else 2 ^ j) := by
  rw [levelRemainder, Finset.card_sdiff_of_subset (orderChunk_subset _ _), orderChunk_card]

theorem levelRemainder_nonempty_lower {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ)
    (h : (levelRemainder s j).Nonempty) :
    2 ^ (j - 1) ≤ (levelRemainder s j).card := by
  cases j with
  | zero => simpa only [Nat.zero_sub, pow_zero] using Finset.card_pos.mpr h
  | succ j =>
    have hPos := Finset.card_pos.mpr h
    have hCount := levelRemainder_card_succ s j
    by_cases hSmall : (levelRemainder s j).card < 2 ^ (j + 1)
    · rw [if_pos hSmall] at hCount
      rw [hCount, Nat.sub_self] at hPos
      omega
    · have hHigh : 2 ^ (j + 1) ≤ (levelRemainder s j).card := by omega
      rw [pow_succ] at hHigh
      rw [if_neg hSmall] at hCount
      rw [hCount]
      simp only [Nat.add_sub_cancel]
      omega

theorem orderChunk_nonempty_iff {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ) :
    (orderChunk s j).Nonempty ↔ s.Nonempty := by
  rw [← Finset.card_pos, ← Finset.card_pos, orderChunk_card]
  split_ifs
  · rfl
  · have hp : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) _
    constructor
    · intro _
      have hHigh : 2 ^ (j + 1) ≤ s.card := by omega
      exact (pow_pos (by norm_num : (0 : ℕ) < 2) _).trans_le hHigh
    · intro _
      exact hp

theorem selectedLevel_card_bounds {α : Type*} [LinearOrder α] (s : Finset α) (j : ℕ)
    (h : (orderChunk (levelRemainder s j) j).Nonempty) :
    2 ^ (j - 1) ≤ (orderChunk (levelRemainder s j) j).card ∧
      (orderChunk (levelRemainder s j) j).card < 2 ^ (j + 1) := by
  have hR := (orderChunk_nonempty_iff _ _).mp h
  have hLow := levelRemainder_nonempty_lower s j hR
  rw [orderChunk_card]
  split_ifs with hSmall
  · exact ⟨hLow, hSmall⟩
  · constructor
    · exact Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.sub_le j 1)
    · rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) _
      omega

theorem selectedLevels_factor_four {α : Type*} [LinearOrder α]
    (s t : Finset α) (j : ℕ)
    (hs : (orderChunk (levelRemainder s j) j).Nonempty)
    (ht : (orderChunk (levelRemainder t j) j).Nonempty) :
    (orderChunk (levelRemainder s j) j).card ≤
      4 * (orderChunk (levelRemainder t j) j).card := by
  obtain ⟨_, hsHigh⟩ := selectedLevel_card_bounds s j hs
  obtain ⟨htLow, _⟩ := selectedLevel_card_bounds t j ht
  cases j with
  | zero => simp only [Nat.zero_sub, pow_zero, zero_add, pow_one] at hsHigh htLow; omega
  | succ j =>
    simp only [Nat.add_sub_cancel, pow_succ] at hsHigh htLow
    omega

theorem levelRemainder_empty_of_card_lt {α : Type*} [LinearOrder α]
    (s : Finset α) (j : ℕ) (h : s.card < 2 ^ (j - 1)) : levelRemainder s j = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hPos
  exact (not_le_of_gt h) ((levelRemainder_nonempty_lower s j hPos).trans
    (levelRemainder_card_le s j))

theorem levelRemainder_antitone {α : Type*} [LinearOrder α] (s : Finset α) :
    Antitone (levelRemainder s) :=
  antitone_nat_of_succ_le (fun _ => Finset.sdiff_subset)

theorem selectedLevels_disjoint {α : Type*} [LinearOrder α] (s : Finset α)
    {j l : ℕ} (hjl : j < l) :
    Disjoint (orderChunk (levelRemainder s j) j) (orderChunk (levelRemainder s l) l) := by
  apply Finset.disjoint_left.mpr
  intro x hxj hxl
  have hxR := orderChunk_subset (levelRemainder s l) l hxl
  have hxNext := levelRemainder_antitone s (Nat.succ_le_of_lt hjl) hxR
  exact (Finset.mem_sdiff.mp hxNext).2 hxj

theorem selectedLevels_union_remainder {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) :
    levelRemainder s J ∪ (Finset.range J).biUnion
      (fun j => orderChunk (levelRemainder s j) j) = s := by
  induction J with
  | zero => simp only [levelRemainder, Finset.range_zero, Finset.biUnion_empty, Finset.union_empty]
  | succ J ih =>
    rw [levelRemainder, Finset.range_add_one, Finset.biUnion_insert, ← Finset.union_assoc,
      Finset.sdiff_union_of_subset (orderChunk_subset _ _)]
    exact ih

theorem selectedLevels_cover {α : Type*} [LinearOrder α]
    (s : Finset α) (J : ℕ) (h : levelRemainder s J = ∅) :
    (Finset.range J).biUnion (fun j => orderChunk (levelRemainder s j) j) = s := by
  simpa only [h, Finset.empty_union] using selectedLevels_union_remainder s J

end CircularLaw
