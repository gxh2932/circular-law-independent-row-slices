import CircularLaw.SteepNetGrid

/-!
# Exact finite cardinality bounds for the steep nets

The net size is bounded by the three actual small-set families and the
integer grid radii. The shifted family is the image of the Cartesian
product with the constant grid. `SteepNetCardinalityUniform` absorbs this
expression into the source `exp(7*n_next*log(d))` uniformly in the degree band.
-/

noncomputable section
open Classical

namespace CircularLaw

def steepNetGridCount (d : ℕ) (R : ℝ) : ℕ :=
  (2 * gridBoxRadius (steepNetResolution d) R + 1) ^ 2

def steepNetCountBound (n d next : ℕ) (cap : ℝ) : ℕ :=
  (smallCoordinateSets n (terminalSteepSize (steepStride d) (firstSteepScale n d) - 1)).card *
    (smallCoordinateSets n (firstSteepScale n d - 1)).card *
      (smallCoordinateSets n (next - 1)).card *
        (steepNetGridCount d ((n : ℝ) ^ 6 * cap) ^
          (terminalSteepSize (steepStride d) (firstSteepScale n d) - 1) *
            steepNetGridCount d (4 * (d : ℝ) * cap) ^ (firstSteepScale n d - 1) *
              steepNetGridCount d cap ^ (next - 1))

theorem steepRawNet_card_le (n d next : ℕ) (cap : ℝ) :
    (steepRawNet n d next cap).card ≤ steepNetCountBound n d next cap := by
  apply (threeRangeGridNet_card_le _ _ _ ⟨0, zero_mem_gridBox _ _⟩
    ⟨0, zero_mem_gridBox _ _⟩ ⟨0, zero_mem_gridBox _ _⟩).trans
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul (Nat.pow_le_pow_left (gridBox_card_le _ _) _)
      (Nat.pow_le_pow_left (gridBox_card_le _ _) _)
  · exact Nat.pow_le_pow_left (gridBox_card_le _ _) _

theorem steepNonconstantNet_card_le (n d rank next : ℕ) (cap : ℝ) :
    (steepNonconstantNet n d rank next cap).card ≤ steepNetCountBound n d next cap :=
  (Finset.card_filter_le _ _).trans (steepRawNet_card_le n d next cap)

theorem steepConstantNet_card_le (d : ℕ) (cap : ℝ) :
    (steepConstantNet d cap).card ≤ steepNetGridCount d cap := gridBox_card_le _ _

def shiftedSteepNet (n d rank next : ℕ) (cap : ℝ) : Finset (Fin n → ℂ) :=
  ((steepNonconstantNet n d rank next cap) ×ˢ (steepConstantNet d cap)).image
    (fun uw j => uw.1 j + uw.2)

theorem shiftedSteepNet_card_le (n d rank next : ℕ) (cap : ℝ) :
    (shiftedSteepNet n d rank next cap).card ≤
      steepNetCountBound n d next cap * steepNetGridCount d cap := by
  apply Finset.card_image_le.trans
  rw [Finset.card_product]
  exact Nat.mul_le_mul (steepNonconstantNet_card_le n d rank next cap)
    (steepConstantNet_card_le d cap)

theorem steepNonconstantNet_all_later_zero {n d rank next j : ℕ} {cap : ℝ}
    (hNext : 0 < next) (hNextJ : next ≤ j) (hJN : j ≤ n)
    (u : Fin n → ℂ) (hu : u ∈ steepNonconstantNet n d rank next cap) :
    orderedNormAt u j = 0 := by
  have hTail := (steepNonconstantNet_gap_and_tail u hu).2
  have h := orderedNormAt_antitone u hNext hNextJ hJN
  rw [hTail] at h
  exact le_antisymm h (orderedNormAt_nonneg u j)

end CircularLaw
