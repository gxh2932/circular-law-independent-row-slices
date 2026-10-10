import CircularLaw.LevelPartition

/-!
# Correspondence with the global remaining-coordinate procedure

Selecting independently within each initial value level gives exactly
the source's global remainder `I_j`. Its represented values are the
image of that remainder, and its next remainder deletes precisely all
selected levels at the current order.
-/

noncomputable section

namespace CircularLaw

def remainingCoordinates {n : ℕ} (y : Fin n → ℂ) (j : ℕ) : Finset (Fin n) :=
  (Finset.univ.image y).biUnion (fun z => levelRemainder (initialLevel y z) j)

theorem remainingCoordinates_mem {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (i : Fin n) :
    i ∈ remainingCoordinates y j ↔ i ∈ levelRemainder (initialLevel y (y i)) j := by
  classical
  constructor
  · intro hi
    obtain ⟨z, _, hiz⟩ := Finset.mem_biUnion.mp hi
    have hValue := (Finset.mem_filter.mp (levelRemainder_subset (initialLevel y z) j hiz)).2
    rw [hValue]
    exact hiz
  · intro hi
    exact Finset.mem_biUnion.mpr ⟨y i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩

theorem remainingCoordinates_zero {n : ℕ} (y : Fin n → ℂ) :
    remainingCoordinates y 0 = Finset.univ := by
  ext i
  rw [remainingCoordinates_mem]
  simp only [levelRemainder, initialLevel, Finset.mem_filter, Finset.mem_univ, and_self]

theorem levelPart_all_mem {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (i : Fin n) :
    i ∈ levelPart y j (representedValues y j) ↔ i ∈ selectedLevelAt y j (y i) := by
  constructor
  · intro hi
    obtain ⟨z, _, hiz⟩ := Finset.mem_biUnion.mp hi
    rw [selectedLevelAt_value y j z hiz]
    exact hiz
  · intro hi
    exact Finset.mem_biUnion.mpr ⟨y i,
      (selectedLevelAt_nonempty_mem y j (y i)).mp ⟨i, hi⟩, hi⟩

theorem remainingCoordinates_succ {n : ℕ} (y : Fin n → ℂ) (j : ℕ) :
    remainingCoordinates y (j + 1) =
      remainingCoordinates y j \ levelPart y j (representedValues y j) := by
  ext i
  rw [remainingCoordinates_mem, levelRemainder, Finset.mem_sdiff,
    Finset.mem_sdiff, remainingCoordinates_mem, levelPart_all_mem]
  rfl

theorem remainingLevel_eq_inter {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (z : ℂ) :
    levelRemainder (initialLevel y z) j = initialLevel y z ∩ remainingCoordinates y j := by
  ext i
  rw [Finset.mem_inter, remainingCoordinates_mem]
  constructor
  · intro hi
    have hiLevel := levelRemainder_subset (initialLevel y z) j hi
    refine ⟨hiLevel, ?_⟩
    rw [(Finset.mem_filter.mp hiLevel).2]
    exact hi
  · rintro ⟨hiLevel, hi⟩
    rw [(Finset.mem_filter.mp hiLevel).2] at hi
    exact hi

theorem representedValues_eq_remaining_image {n : ℕ} (y : Fin n → ℂ) (j : ℕ) :
    representedValues y j = (remainingCoordinates y j).image y := by
  classical
  ext z
  rw [← selectedLevelAt_nonempty_mem]
  constructor
  · rintro ⟨i, hi⟩
    have hValue := selectedLevelAt_value y j z hi
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hValue⟩
    rw [remainingCoordinates_mem, hValue]
    exact orderChunk_subset _ _ hi
  · intro hz
    obtain ⟨i, hi, hValue⟩ := Finset.mem_image.mp hz
    rw [remainingCoordinates_mem, hValue] at hi
    exact (orderChunk_nonempty_iff _ _).mpr ⟨i, hi⟩

theorem selectedLevelAt_eq_global {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (z : ℂ) :
    selectedLevelAt y j z = orderChunk (initialLevel y z ∩ remainingCoordinates y j) j := by
  rw [selectedLevelAt, remainingLevel_eq_inter]

end CircularLaw
