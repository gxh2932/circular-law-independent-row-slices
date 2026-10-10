import CircularLaw.SourceRefinementFamilies

/-!
# Small initial levels force high-height coordinate mass

For a coordinate family whose original value levels all have size at
most `M`, its mass outside the actual high-height parts is at most
`16*M*H`. The proof sums the literal spread and regular parts over their
creation orders, retaining the source geometric-series estimate.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def lowHeightOrderCoordinates {n : ℕ} (y : Fin n → ℂ) (δ H : ℝ) (j : ℕ) : Finset (Fin n) :=
  (if ((spreadValueSet y j δ).card : ℝ) < H then spreadPart y j δ else ∅) ∪
  (if ((regularValueSet y j δ).card : ℝ) < H then regularPart y j δ else ∅)

theorem lowHeightOrderCoordinates_card_le {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (j : ℕ) :
    ((lowHeightOrderCoordinates y δ H j).card : ℝ) ≤ (2 : ℝ) ^ (j + 2) * H := by
  have hS : ((if ((spreadValueSet y j δ).card : ℝ) < H then spreadPart y j δ else ∅).card : ℝ) ≤
      (2 : ℝ) ^ (j + 1) * H := by
    split_ifs with h
    · have hUpper : ((spreadPart y j δ).card : ℝ) ≤
          (2 : ℝ) ^ (j + 1) * (spreadValueSet y j δ).card := by
        exact_mod_cast (source_parts_size_height y j δ).1.2
      exact hUpper.trans (mul_le_mul_of_nonneg_left h.le (by positivity))
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hR : ((if ((regularValueSet y j δ).card : ℝ) < H then regularPart y j δ else ∅).card : ℝ) ≤
      (2 : ℝ) ^ (j + 1) * H := by
    split_ifs with h
    · have hUpper : ((regularPart y j δ).card : ℝ) ≤
          (2 : ℝ) ^ (j + 1) * (regularValueSet y j δ).card := by
        exact_mod_cast (source_parts_size_height y j δ).2.2
      exact hUpper.trans (mul_le_mul_of_nonneg_left h.le (by positivity))
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hUnion := Finset.card_union_le
    (if ((spreadValueSet y j δ).card : ℝ) < H then spreadPart y j δ else ∅)
    (if ((regularValueSet y j δ).card : ℝ) < H then regularPart y j δ else ∅)
  have hUnionR : ((lowHeightOrderCoordinates y δ H j).card : ℝ) ≤
      (if ((spreadValueSet y j δ).card : ℝ) < H then spreadPart y j δ else ∅).card +
      (if ((regularValueSet y j δ).card : ℝ) < H then regularPart y j δ else ∅).card := by
    exact_mod_cast hUnion
  rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
  linarith

theorem creation_order_power_sum (J : ℕ) :
    ∑ j ∈ Finset.range J, (2 : ℝ) ^ (j + 2) = 4 * ((2 : ℝ) ^ J - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_succ]
    ring

theorem lowHeight_prefix_mass_le {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) {H : ℝ}
    (hH : 0 ≤ H) (J : ℕ) :
    (((Finset.range (J + 1)).biUnion (lowHeightOrderCoordinates y δ H)).card : ℝ) ≤
      (2 : ℝ) ^ (J + 3) * H := by
  have hCard := Finset.card_biUnion_le (s := Finset.range (J + 1))
    (t := lowHeightOrderCoordinates y δ H)
  have hCardR : (((Finset.range (J + 1)).biUnion (lowHeightOrderCoordinates y δ H)).card : ℝ) ≤
      ∑ j ∈ Finset.range (J + 1), ((lowHeightOrderCoordinates y δ H j).card : ℝ) := by
    exact_mod_cast hCard
  apply hCardR.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ (j + 2) * H :=
      Finset.sum_le_sum (fun j _ => lowHeightOrderCoordinates_card_le y δ hH j)
    _ = 4 * ((2 : ℝ) ^ (J + 1) - 1) * H := by
      rw [← Finset.sum_mul, creation_order_power_sum]
    _ ≤ (2 : ℝ) ^ (J + 3) * H := by
      have hPower : (2 : ℝ) ^ (J + 3) = 4 * (2 : ℝ) ^ (J + 1) := by
        simp only [pow_succ]
        ring
      rw [hPower]
      nlinarith

theorem taggedPart_order_eq_coordinateLevelOrder {n : ℕ} (y : Fin n → ℂ)
    (δ : ℝ) (q : Bool × Fin (n + 2)) (i : Fin n) (hi : i ∈ taggedPart y δ q) :
    q.2.val = coordinateLevelOrder y i := by
  by_contra hNe
  have hiChosen := (coordinateLevelOrder_spec y i).2
  have hiPart : i ∈ creationOrderCoordinates y (coordinateLevelOrder y i) :=
    Finset.mem_biUnion.mpr ⟨y i, (selectedLevelAt_nonempty_mem y _ _).mp ⟨i, hiChosen⟩, hiChosen⟩
  exact Finset.disjoint_left.mp (levelPart_disjoint_orders y _ _ hNe) hi hiPart

theorem coordinates_mass_le_highHeight_add {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (G : Finset (Fin n)) {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hLevels : ∀ i ∈ G, ((initialLevel y (y i)).card : ℝ) ≤ M) :
    (G.card : ℝ) ≤ (highHeightCoordinates y δ H).card + 16 * M * H := by
  by_cases hG : G.Nonempty
  · have hImage : (G.image (coordinateLevelOrder y)).Nonempty := hG.image _
    let J := (G.image (coordinateLevelOrder y)).max' hImage
    obtain ⟨a, ha, haJ⟩ := Finset.mem_image.mp (Finset.max'_mem _ hImage)
    have hSelected := (coordinateLevelOrder_spec y a).2
    have hInitial : 2 ^ (J - 1) ≤ (initialLevel y (y a)).card := by
      have hBound := (selectedLevel_card_bounds (initialLevel y (y a))
        (coordinateLevelOrder y a) ⟨a, hSelected⟩).1
      rw [haJ] at hBound
      exact hBound.trans (Finset.card_le_card (by
        intro i hi
        exact levelRemainder_subset _ _ (orderChunk_subset _ _ hi)))
    have hInitialR : (2 : ℝ) ^ (J - 1) ≤ M :=
      (by exact_mod_cast hInitial : (2 : ℝ) ^ (J - 1) ≤ (initialLevel y (y a)).card).trans
        (hLevels a ha)
    have hPowerNat : 2 ^ (J + 3) ≤ 16 * 2 ^ (J - 1) := by
      have h := selected_order_power_balance J
      have hPow : (2 : ℕ) ^ (J + 3) = 4 * 2 ^ (J + 1) := by
        simp only [pow_succ]
        ring
      rw [hPow]
      omega
    have hPower : (2 : ℝ) ^ (J + 3) ≤ 16 * M := by
      have h : (2 : ℝ) ^ (J + 3) ≤ 16 * (2 : ℝ) ^ (J - 1) := by exact_mod_cast hPowerNat
      exact h.trans (mul_le_mul_of_nonneg_left hInitialR (by norm_num))
    have hLow := lowHeight_prefix_mass_le y δ hH J
    have hSub : G ⊆ (highHeightCoordinates y δ H) ∪
        (Finset.range (J + 1)).biUnion (lowHeightOrderCoordinates y δ H) := by
      intro i hi
      obtain ⟨q, hiq⟩ := taggedParts_cover y δ i
      by_cases hHigh : H ≤ ((taggedValues y δ q).card : ℝ)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hHigh⟩, hiq⟩)
      · have hOrder : q.2.val ≤ J := by
          rw [taggedPart_order_eq_coordinateLevelOrder y δ q i hiq]
          exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨q.2.val, Finset.mem_range.mpr (by omega), ?_⟩
        cases hKind : q.1
        · have hSmall : ((regularValueSet y q.2.val δ).card : ℝ) < H := by
            simpa only [taggedValues, hKind, Bool.false_eq_true, ↓reduceIte] using lt_of_not_ge hHigh
          apply Finset.mem_union_right
          rw [if_pos hSmall]
          simpa only [taggedPart, taggedValues, hKind, Bool.false_eq_true, ↓reduceIte] using hiq
        · have hSmall : ((spreadValueSet y q.2.val δ).card : ℝ) < H := by
            simpa only [taggedValues, hKind, ↓reduceIte] using lt_of_not_ge hHigh
          apply Finset.mem_union_left
          rw [if_pos hSmall]
          simpa only [taggedPart, taggedValues, hKind, ↓reduceIte] using hiq
    have hCard : (G.card : ℝ) ≤ (highHeightCoordinates y δ H).card +
        (((Finset.range (J + 1)).biUnion (lowHeightOrderCoordinates y δ H)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)
    have hFinal := mul_le_mul_of_nonneg_right hPower hH
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hG, Finset.card_empty, Nat.cast_zero]
    positivity

end CircularLaw
