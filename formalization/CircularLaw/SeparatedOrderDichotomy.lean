import CircularLaw.RefinementMassDichotomy

/-!
# Separated coordinate cohorts force high or spread mass

Two large coordinate cohorts separated at the canonical spread scale
force either large combined-height mass or large spread mass. The proof
uses an actual last creation order, nested represented values, and the
source greedy parts. This is the deterministic argument of LLTTY19
Lemma 5.8; constructing the two cohorts for the gradual class remains
a separate step.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def coordinateLevelOrder {n : ℕ} (y : Fin n → ℂ) (i : Fin n) : ℕ :=
  Classical.choose (selectedLevelAt_coordinate y i)

theorem coordinateLevelOrder_spec {n : ℕ} (y : Fin n → ℂ) (i : Fin n) :
    coordinateLevelOrder y i < n + 2 ∧
      i ∈ selectedLevelAt y (coordinateLevelOrder y i) (y i) :=
  Classical.choose_spec (selectedLevelAt_coordinate y i)

theorem low_combined_order_mass_le_spread {n : ℕ} (y : Fin n → ℂ) (j : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hLow : (representedValues y j).card < 10)
    (hPair : ∃ a ∈ representedValues y j, ∃ b ∈ representedValues y j, δ ≤ dist a b) :
    (creationOrderCoordinates y j).card ≤ 15 * (spreadPart y j δ).card := by
  obtain ⟨a, ha, b, hb, hab⟩ := hPair
  have hS : (spreadValueSet y j δ).Nonempty := by
    by_contra hNo
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hNo
    have haR : a ∈ regularValueSet y j δ := by
      rw [regularValueSet, hEmpty, Finset.sdiff_empty]
      exact ha
    have hbR : b ∈ regularValueSet y j δ := by
      rw [regularValueSet, hEmpty, Finset.sdiff_empty]
      exact hb
    exact (not_lt_of_ge hab) ((source_regular_value_geometry y j δ).1 hEmpty a haR b hbR)
  have hSHeight := spreadPart_height_ge_two y j hδ
    ((levelPart_nonempty_iff y j _ (spreadValueSet_subset y j δ)).mpr hS)
  have hRCount : (regularValueSet y j δ).card =
      (representedValues y j).card - (spreadValueSet y j δ).card :=
    Finset.card_sdiff_of_subset (spreadValueSet_subset y j δ)
  have hRHeight : (regularValueSet y j δ).card ≤ 7 := by omega
  have hLower := (source_parts_size_height y j δ).1.1
  have hUpper := (source_parts_size_height y j δ).2.2
  have hTwo := Nat.mul_le_mul_left (2 ^ (j - 1)) hSHeight
  have hSeven := Nat.mul_le_mul_left (2 ^ (j + 1)) hRHeight
  have hBalance := selected_order_power_balance j
  have hRMass : (regularPart y j δ).card ≤ 14 * (spreadPart y j δ).card := by
    nlinarith
  have hTotal : (creationOrderCoordinates y j).card ≤
      (spreadPart y j δ).card + (regularPart y j δ).card := by
    rw [creationOrderCoordinates_eq_parts y j δ]
    exact Finset.card_union_le _ _
  omega

theorem separated_anchored_cohort_mass {n : ℕ} (y : Fin n → ℂ) (J : Finset (Fin n))
    (a : Fin n) {δ : ℝ} (hδ : 0 < δ)
    (hSep : ∀ i ∈ J, δ ≤ dist (y a) (y i))
    (hLast : ∀ i ∈ J, coordinateLevelOrder y i ≤ coordinateLevelOrder y a) :
    J.card ≤ (highCombinedHeightCoordinates y).card + 15 * (spreadCoordinates y δ).card := by
  let Q := (Finset.range (n + 2)).filter (fun j =>
    (representedValues y j).card < 10 ∧ ∃ i ∈ J, coordinateLevelOrder y i = j)
  have hSmall : ∀ j ∈ Q,
      (creationOrderCoordinates y j).card ≤ 15 * (spreadPart y j δ).card := by
    intro j hj
    have hLow := (Finset.mem_filter.mp hj).2.1
    obtain ⟨i, hi, hOrder⟩ := (Finset.mem_filter.mp hj).2.2
    have hiLevel := (coordinateLevelOrder_spec y i).2
    rw [hOrder] at hiLevel
    have hiRep := (selectedLevelAt_nonempty_mem y j (y i)).mp ⟨i, hiLevel⟩
    have haRep := (selectedLevelAt_nonempty_mem y (coordinateLevelOrder y a) (y a)).mp
      ⟨a, (coordinateLevelOrder_spec y a).2⟩
    have hjLast : j ≤ coordinateLevelOrder y a := by rw [← hOrder]; exact hLast i hi
    exact low_combined_order_mass_le_spread y j hδ hLow
      ⟨y a, representedValues_antitone y hjLast haRep, y i, hiRep, hSep i hi⟩
  have hSmallMass : (Q.biUnion (creationOrderCoordinates y)).card ≤
      15 * (spreadCoordinates y δ).card := by
    change ((Q.biUnion (fun j => levelPart y j (representedValues y j))).card) ≤ _
    rw [selectedOrderCoordinates_card, spreadCoordinates_card, Finset.mul_sum]
    exact (Finset.sum_le_sum hSmall).trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  have hSub : J ⊆ highCombinedHeightCoordinates y ∪ Q.biUnion (creationOrderCoordinates y) := by
    intro i hi
    have hiLevel := (coordinateLevelOrder_spec y i).2
    have hiPart : i ∈ creationOrderCoordinates y (coordinateLevelOrder y i) :=
      Finset.mem_biUnion.mpr ⟨y i, (selectedLevelAt_nonempty_mem y _ _).mp ⟨i, hiLevel⟩, hiLevel⟩
    by_cases hHigh : 10 ≤ (representedValues y (coordinateLevelOrder y i)).card
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨coordinateLevelOrder y i, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (coordinateLevelOrder_spec y i).1, hHigh⟩, hiPart⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨coordinateLevelOrder y i, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (coordinateLevelOrder_spec y i).1, by omega, i, hi, rfl⟩, hiPart⟩)
  exact ((Finset.card_le_card hSub).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add_left hSmallMass _)

theorem separated_cohorts_mass_bound {n : ℕ} (y : Fin n → ℂ)
    (I J : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ)
    (hSep : ∀ i ∈ I, ∀ j ∈ J, δ ≤ dist (y i) (y j)) :
    min I.card J.card ≤
      (highCombinedHeightCoordinates y).card + 15 * (spreadCoordinates y δ).card := by
  by_cases hI : I.Nonempty
  · by_cases hJ : J.Nonempty
    · have hUnion : (I ∪ J).Nonempty := hI.mono Finset.subset_union_left
      have hImage : ((I ∪ J).image (coordinateLevelOrder y)).Nonempty := hUnion.image _
      obtain ⟨a, ha, hOrder⟩ := Finset.mem_image.mp
        (Finset.max'_mem ((I ∪ J).image (coordinateLevelOrder y)) hImage)
      have hLast : ∀ i ∈ I ∪ J, coordinateLevelOrder y i ≤ coordinateLevelOrder y a := by
        intro i hi
        rw [hOrder]
        exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      rcases Finset.mem_union.mp ha with haI | haJ
      · exact (min_le_right I.card J.card).trans (separated_anchored_cohort_mass y J a hδ
          (fun j hj => hSep a haI j hj) (fun j hj => hLast j (Finset.mem_union_right _ hj)))
      · exact (min_le_left I.card J.card).trans (separated_anchored_cohort_mass y I a hδ
          (fun i hi => by rw [dist_comm]; exact hSep i hi a haJ)
          (fun i hi => hLast i (Finset.mem_union_left _ hi)))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hJ, Finset.card_empty, min_zero]
      exact Nat.zero_le _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.card_empty, zero_min]
    exact Nat.zero_le _

theorem separated_cohorts_high_or_spread {n : ℕ} (y : Fin n → ℂ)
    (I J : Finset (Fin n)) {δ M : ℝ} (hδ : 0 < δ)
    (hSep : ∀ i ∈ I, ∀ j ∈ J, δ ≤ dist (y i) (y j))
    (hI : M / 4 ≤ I.card) (hJ : M / 4 ≤ J.card) :
    M / 8 ≤ (highCombinedHeightCoordinates y).card ∨
      M / 120 ≤ (spreadCoordinates y δ).card := by
  have hCount := separated_cohorts_mass_bound y I J hδ hSep
  have hCountR : ((min I.card J.card : ℕ) : ℝ) ≤
      (highCombinedHeightCoordinates y).card + 15 * (spreadCoordinates y δ).card := by
    exact_mod_cast hCount
  have hMin : M / 4 ≤ ((min I.card J.card : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min hI hJ
  by_contra hNo
  push_neg at hNo
  linarith

theorem canonicalApprox_pow_cohorts_spread_or_shrinking {n d : ℕ} (hd : 0 < d)
    (u : ℕ) (x : Fin n → ℂ) (I J : Finset (Fin n)) {M : ℝ}
    (hSep : ∀ i ∈ I, ∀ j ∈ J,
      (d : ℝ) / (d ^ u : ℕ) ≤
        dist (canonicalApprox (d ^ u) (x i)) (canonicalApprox (d ^ u) (x j)))
    (hI : M / 4 ≤ I.card) (hJ : M / 4 ≤ J.card) :
    M / 120 ≤ (spreadCoordinates (fun i => canonicalApprox (d ^ u) (x i))
      ((d : ℝ) / (d ^ u : ℕ))).card ∨
    M / 4608 ≤ (spreadCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      ((d : ℝ) / (d ^ (u + 1) : ℕ))).card ∨
    M / 656 ≤ (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      (fun i => canonicalApprox (d ^ u) (x i))).card := by
  have hδ : 0 < (d : ℝ) / (d ^ u : ℕ) := div_pos
    (by exact_mod_cast hd) (by exact_mod_cast pow_pos hd u)
  rcases separated_cohorts_high_or_spread (fun i => canonicalApprox (d ^ u) (x i))
      I J hδ hSep hI hJ with hHigh | hSpread
  · apply Or.inr
    rw [canonicalApprox_pow_spread_separation hd u]
    exact refinement_spread_or_shrinking (pow_pos hd u) _ _
      (fun i => (canonicalApprox_pow_refinement hd u (x i)).symm) hHigh
  · exact Or.inl hSpread

theorem canonicalApprox_pow_shrinking_lower_of_small_spread {n d : ℕ} (hd : 0 < d)
    (u : ℕ) (x : Fin n → ℂ) (I J : Finset (Fin n)) {M : ℝ}
    (hSep : ∀ i ∈ I, ∀ j ∈ J,
      (d : ℝ) / (d ^ u : ℕ) ≤
        dist (canonicalApprox (d ^ u) (x i)) (canonicalApprox (d ^ u) (x j)))
    (hI : M / 4 ≤ I.card) (hJ : M / 4 ≤ J.card)
    (hCoarse : ((spreadCoordinates (fun i => canonicalApprox (d ^ u) (x i))
      ((d : ℝ) / (d ^ u : ℕ))).card : ℝ) < M / 4608)
    (hFine : ((spreadCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      ((d : ℝ) / (d ^ (u + 1) : ℕ))).card : ℝ) < M / 4608) :
    M / 656 ≤ (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
      (fun i => canonicalApprox (d ^ u) (x i))).card := by
  rcases canonicalApprox_pow_cohorts_spread_or_shrinking hd u x I J hSep hI hJ with
    hLarge | hLarge | hShrink
  · linarith
  · linarith
  · exact hShrink

end CircularLaw
