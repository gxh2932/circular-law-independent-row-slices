import CircularLaw.LevelRefinement
import CircularLaw.FloorGridCover
import CircularLaw.CanonicalPartition

/-!
# Coordinate mass in the refinement dichotomy

The majority-value grid estimate applies to the actual canonical spread
parts. It controls coordinate mass with factor 36, using their checked
level-size balance. Orders of combined height at least ten which have
fewer than ten majority levels instead have mass at most forty times
their shrinking-coordinate mass. These deterministic estimates are
inputs to the source one-step dichotomy.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def creationOrderCoordinates {n : ℕ} (y : Fin n → ℂ) (j : ℕ) : Finset (Fin n) :=
  levelPart y j (representedValues y j)

def spreadCoordinates {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) : Finset (Fin n) :=
  (Finset.range (n + 2)).biUnion (fun j => spreadPart y j δ)

theorem creationOrderCoordinates_eq_parts {n : ℕ} (y : Fin n → ℂ) (j : ℕ) (δ : ℝ) :
    creationOrderCoordinates y j = spreadPart y j δ ∪ regularPart y j δ := by
  ext i
  constructor
  · intro hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hi
    by_cases hS : z ∈ spreadValueSet y j δ
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨z, hS, hiz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨z, Finset.mem_sdiff.mpr ⟨hz, hS⟩, hiz⟩)
  · intro hi
    rcases Finset.mem_union.mp hi with hS | hR
    · obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hS
      exact Finset.mem_biUnion.mpr ⟨z, spreadValueSet_subset y j δ hz, hiz⟩
    · obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hR
      exact Finset.mem_biUnion.mpr ⟨z, regularValueSet_subset y j δ hz, hiz⟩

theorem selectedOrderCoordinates_card {n : ℕ} (y : Fin n → ℂ)
    (J : Finset ℕ) (A : ℕ → Finset ℂ) :
    (J.biUnion (fun j => levelPart y j (A j))).card =
      ∑ j ∈ J, (levelPart y j (A j)).card := by
  apply Finset.card_biUnion
  intro j hj l hl hjl
  exact levelPart_disjoint_orders y _ _ hjl

theorem spreadCoordinates_card {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    (spreadCoordinates y δ).card =
      ∑ j ∈ Finset.range (n + 2), (spreadPart y j δ).card :=
  selectedOrderCoordinates_card y _ (fun j => spreadValueSet y j δ)

theorem selected_order_power_balance (j : ℕ) :
    (2 : ℕ) ^ (j + 1) ≤ 4 * 2 ^ (j - 1) := by
  cases j with
  | zero => norm_num
  | succ j => simp only [Nat.add_sub_cancel, pow_succ]; omega

theorem coarse_injective_levelPart_mass_le_spread {n k : ℕ} (hk : 0 < k)
    (y : Fin n → ℂ) (j : ℕ) (A : Finset ℂ) (hA : A ⊆ representedValues y j)
    (hInj : Set.InjOn (canonicalApprox k) A) (hTen : 10 ≤ A.card) :
    (levelPart y j A).card ≤ 36 * (spreadPart y j (1 / (k : ℝ))).card := by
  have hHeight : A.card ≤ 9 * (spreadValueSet y j (1 / (k : ℝ))).card :=
    coarse_injective_spreadSelection_height hk _ A hA hInj hTen
  have hUpper := (levelPart_size_height y j A hA).2
  have hLower := (source_parts_size_height y j (1 / (k : ℝ))).1.1
  calc
    (levelPart y j A).card ≤ 2 ^ (j + 1) * A.card := hUpper
    _ ≤ 2 ^ (j + 1) * (9 * (spreadValueSet y j (1 / (k : ℝ))).card) :=
      Nat.mul_le_mul_left _ hHeight
    _ ≤ (4 * 2 ^ (j - 1)) * (9 * (spreadValueSet y j (1 / (k : ℝ))).card) :=
      Nat.mul_le_mul_right _ (selected_order_power_balance j)
    _ = 36 * (2 ^ (j - 1) * (spreadValueSet y j (1 / (k : ℝ))).card) := by ring
    _ ≤ 36 * (spreadPart y j (1 / (k : ℝ))).card := Nat.mul_le_mul_left 36 hLower

theorem nonshrinking_levelPart_mass_le_spread {n k : ℕ} (hk : 0 < k)
    (fine coarse : Fin n → ℂ) (h : ∀ i, coarse i = canonicalApprox k (fine i)) (j : ℕ)
    (hTen : 10 ≤ ((nonshrinkingFineValues fine coarse) ∩ representedValues fine j).card) :
    (levelPart fine j ((nonshrinkingFineValues fine coarse) ∩ representedValues fine j)).card ≤
      36 * (spreadPart fine j (1 / (k : ℝ))).card :=
  coarse_injective_levelPart_mass_le_spread hk fine j _ Finset.inter_subset_right
    ((nonshrinkingValueMap_injective fine coarse (canonicalApprox k) h).mono
      (by
        intro z hz
        change z ∈ (nonshrinkingFineValues fine coarse) ∩ representedValues fine j at hz
        exact (Finset.mem_inter.mp hz).1)) hTen

theorem nonshrinking_orders_mass_le_spread {n k : ℕ} (hk : 0 < k)
    (fine coarse : Fin n → ℂ) (h : ∀ i, coarse i = canonicalApprox k (fine i))
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (n + 2))
    (hTen : ∀ j ∈ J, 10 ≤ ((nonshrinkingFineValues fine coarse) ∩ representedValues fine j).card) :
    (J.biUnion (fun j => levelPart fine j
      ((nonshrinkingFineValues fine coarse) ∩ representedValues fine j))).card ≤
      36 * (spreadCoordinates fine (1 / (k : ℝ))).card := by
  rw [selectedOrderCoordinates_card, spreadCoordinates_card, Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ J, 36 * (spreadPart fine j (1 / (k : ℝ))).card :=
      Finset.sum_le_sum (fun j hj => nonshrinking_levelPart_mass_le_spread hk fine coarse h j
        (hTen j hj))
    _ ≤ _ := Finset.sum_le_sum_of_subset hJ

theorem nonmajority_coarse_levelPart_subset_shrinking {n : ℕ} (fine coarse : Fin n → ℂ)
    (j : ℕ) :
    levelPart coarse j ((representedValues coarse j) \ nonshrinkingCoarseValues fine coarse) ⊆
      shrinkingCoordinates fine coarse := by
  intro i hi
  have hValue := levelPart_value_mem coarse j _ hi
  have hNot := (Finset.mem_sdiff.mp hValue).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  by_contra hLarge
  apply hNot
  exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩, rfl⟩

theorem creationOrderCoordinates_small_majority_mass {n : ℕ} (fine coarse : Fin n → ℂ)
    (j : ℕ) (hHeight : 10 ≤ (representedValues coarse j).card)
    (hSmall : ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j).card < 10) :
    (creationOrderCoordinates coarse j).card ≤
      40 * ((creationOrderCoordinates coarse j) ∩ shrinkingCoordinates fine coarse).card := by
  let B := (representedValues coarse j) \ nonshrinkingCoarseValues fine coarse
  have hSplit : (representedValues coarse j).card =
      ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j).card + B.card := by
    have h := Finset.card_sdiff_add_card_inter (representedValues coarse j)
      (nonshrinkingCoarseValues fine coarse)
    simpa only [Finset.inter_comm, B, Nat.add_comm] using h.symm
  have hHeightBad : (representedValues coarse j).card ≤ 10 * B.card := by omega
  have hUpper := (levelPart_size_height coarse j (representedValues coarse j)
    (Finset.Subset.refl _)).2
  have hLower := (levelPart_size_height coarse j B Finset.sdiff_subset).1
  have hBSub : levelPart coarse j B ⊆
      (creationOrderCoordinates coarse j) ∩ shrinkingCoordinates fine coarse := by
    intro i hi
    refine Finset.mem_inter.mpr ⟨?_, nonmajority_coarse_levelPart_subset_shrinking fine coarse j hi⟩
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨z, (Finset.mem_sdiff.mp hz).1, hiz⟩
  calc
    (creationOrderCoordinates coarse j).card ≤ 2 ^ (j + 1) * (representedValues coarse j).card := hUpper
    _ ≤ 2 ^ (j + 1) * (10 * B.card) := Nat.mul_le_mul_left _ hHeightBad
    _ ≤ (4 * 2 ^ (j - 1)) * (10 * B.card) :=
      Nat.mul_le_mul_right _ (selected_order_power_balance j)
    _ = 40 * (2 ^ (j - 1) * B.card) := by ring
    _ ≤ 40 * (levelPart coarse j B).card := Nat.mul_le_mul_left 40 hLower
    _ ≤ _ := Nat.mul_le_mul_left 40 (Finset.card_le_card hBSub)

theorem creationOrderCoordinates_inter_card_sum {n : ℕ} (y : Fin n → ℂ)
    (J : Finset ℕ) (I : Finset (Fin n)) :
    (J.biUnion (fun j => (creationOrderCoordinates y j) ∩ I)).card =
      ∑ j ∈ J, ((creationOrderCoordinates y j) ∩ I).card := by
  apply Finset.card_biUnion
  intro j hj l hl hjl
  exact (levelPart_disjoint_orders y _ _ hjl).mono Finset.inter_subset_left Finset.inter_subset_left

theorem small_majority_orders_mass_le_shrinking {n : ℕ} (fine coarse : Fin n → ℂ)
    (J : Finset ℕ) (hHeight : ∀ j ∈ J, 10 ≤ (representedValues coarse j).card)
    (hSmall : ∀ j ∈ J,
      ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j).card < 10) :
    (J.biUnion (creationOrderCoordinates coarse)).card ≤
      40 * (shrinkingCoordinates fine coarse).card := by
  change ((J.biUnion (fun j => levelPart coarse j (representedValues coarse j))).card) ≤ _
  rw [selectedOrderCoordinates_card]
  calc
    _ ≤ ∑ j ∈ J, 40 * ((creationOrderCoordinates coarse j) ∩
        shrinkingCoordinates fine coarse).card := Finset.sum_le_sum (fun j hj =>
      creationOrderCoordinates_small_majority_mass fine coarse j (hHeight j hj) (hSmall j hj))
    _ = 40 * (J.biUnion (fun j => (creationOrderCoordinates coarse j) ∩
        shrinkingCoordinates fine coarse)).card := by
      rw [creationOrderCoordinates_inter_card_sum, Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left 40 (Finset.card_le_card (by
      intro i hi
      obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_inter.mp hij).2))

end CircularLaw
