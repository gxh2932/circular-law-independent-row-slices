import CircularLaw.RefinementSpread

/-!
# The deterministic mass inequality between consecutive scales

The high-combined-height coordinate mass of the coarse approximation is
at most 288 times the spread mass of the finer approximation, plus 41
times the shrinking-coordinate count. All three quantities come from
the actual selected levels. This closes the geometric and combinatorial
step of the refinement dichotomy; its gradual-class input is a separate
obligation.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def highCombinedHeightOrders {n : ℕ} (y : Fin n → ℂ) : Finset ℕ :=
  (Finset.range (n + 2)).filter (fun j => 10 ≤ (representedValues y j).card)

def majorityCoarseOrders {n : ℕ} (fine coarse : Fin n → ℂ) : Finset ℕ :=
  (Finset.range (n + 2)).filter (fun j =>
    10 ≤ ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j).card)

def highCombinedHeightCoordinates {n : ℕ} (y : Fin n → ℂ) : Finset (Fin n) :=
  (highCombinedHeightOrders y).biUnion (creationOrderCoordinates y)

theorem inter_representedValues_card_antitone {n : ℕ} (y : Fin n → ℂ) (A : Finset ℂ) :
    Antitone (fun j => (A ∩ representedValues y j).card) := by
  intro j l hjl
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
    representedValues_antitone y hjl (Finset.mem_inter.mp hz).2⟩

theorem majorityCoarseOrders_eq_range_max {n : ℕ} (fine coarse : Fin n → ℂ)
    (hV : (majorityCoarseOrders fine coarse).Nonempty) :
    majorityCoarseOrders fine coarse =
      Finset.range ((majorityCoarseOrders fine coarse).max' hV + 1) := by
  let J := (majorityCoarseOrders fine coarse).max' hV
  have hJ := Finset.max'_mem (majorityCoarseOrders fine coarse) hV
  have hJRange := (Finset.mem_filter.mp hJ).1
  have hJHeight := (Finset.mem_filter.mp hJ).2
  ext j
  constructor
  · intro hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ j hj))
  · intro hj
    have hjJ : j ≤ J := by have h' := Finset.mem_range.mp hj; omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hjJ.trans_lt (Finset.mem_range.mp hJRange)), ?_⟩
    exact hJHeight.trans (inter_representedValues_card_antitone coarse
      (nonshrinkingCoarseValues fine coarse) hjJ)

theorem levelPrefixCoordinates_eq_order_union {n : ℕ} (y : Fin n → ℂ)
    (A : Finset ℂ) (J : ℕ) :
    levelPrefixCoordinates y A J = (Finset.range J).biUnion
      (fun j => levelPart y j (A ∩ representedValues y j)) := by
  ext i
  constructor
  · intro hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hiz
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_biUnion.mpr
      ⟨z, Finset.mem_inter.mpr ⟨hz, (selectedLevelAt_nonempty_mem y j z).mp ⟨i, hij⟩⟩, hij⟩⟩
  · intro hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hij
    exact Finset.mem_biUnion.mpr ⟨z, (Finset.mem_inter.mp hz).1,
      Finset.mem_biUnion.mpr ⟨j, hj, hiz⟩⟩

theorem creationOrder_union_mass_le_majority_add_shrinking {n : ℕ}
    (fine coarse : Fin n → ℂ) (J : Finset ℕ) :
    (J.biUnion (creationOrderCoordinates coarse)).card ≤
      (J.biUnion (fun j => levelPart coarse j
        ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j))).card +
      (shrinkingCoordinates fine coarse).card := by
  have hSub : J.biUnion (creationOrderCoordinates coarse) ⊆
      (J.biUnion (fun j => levelPart coarse j
        ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j))) ∪
      shrinkingCoordinates fine coarse := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hij
    by_cases hGood : z ∈ nonshrinkingCoarseValues fine coarse
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj,
        Finset.mem_biUnion.mpr ⟨z, Finset.mem_inter.mpr ⟨hGood, hz⟩, hiz⟩⟩)
    · exact Finset.mem_union_right _ (nonmajority_coarse_levelPart_subset_shrinking fine coarse j
        (Finset.mem_biUnion.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hGood⟩, hiz⟩))
  exact (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)

theorem highCombinedHeight_mass_le_majority_add {n : ℕ} (fine coarse : Fin n → ℂ) :
    (highCombinedHeightCoordinates coarse).card ≤
      ((majorityCoarseOrders fine coarse).biUnion (creationOrderCoordinates coarse)).card +
      40 * (shrinkingCoordinates fine coarse).card := by
  let B := (highCombinedHeightOrders coarse) \ majorityCoarseOrders fine coarse
  have hHeight : ∀ j ∈ B, 10 ≤ (representedValues coarse j).card := by
    intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
  have hSmall : ∀ j ∈ B,
      ((nonshrinkingCoarseValues fine coarse) ∩ representedValues coarse j).card < 10 := by
    intro j hj
    have hRange := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).1
    have hNot := (Finset.mem_sdiff.mp hj).2
    by_contra h
    exact hNot (Finset.mem_filter.mpr ⟨hRange, by omega⟩)
  have hBad := small_majority_orders_mass_le_shrinking fine coarse B hHeight hSmall
  have hSub : highCombinedHeightCoordinates coarse ⊆
      ((majorityCoarseOrders fine coarse).biUnion (creationOrderCoordinates coarse)) ∪
      (B.biUnion (creationOrderCoordinates coarse)) := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    by_cases hjV : j ∈ majorityCoarseOrders fine coarse
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hjV, hij⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_sdiff.mpr ⟨hj, hjV⟩, hij⟩)
  exact ((Finset.card_le_card hSub).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add_left hBad _)

theorem majority_orders_mass_le_fine_spread_add {n k : ℕ} (hk : 0 < k)
    (fine coarse : Fin n → ℂ) (h : ∀ i, coarse i = canonicalApprox k (fine i)) :
    ((majorityCoarseOrders fine coarse).biUnion (creationOrderCoordinates coarse)).card ≤
      288 * (spreadCoordinates fine (1 / (k : ℝ))).card +
        (shrinkingCoordinates fine coarse).card := by
  by_cases hV : (majorityCoarseOrders fine coarse).Nonempty
  · let J := (majorityCoarseOrders fine coarse).max' hV
    have hJ := Finset.max'_mem (majorityCoarseOrders fine coarse) hV
    have hJRange : J < n + 2 := Finset.mem_range.mp (Finset.mem_filter.mp hJ).1
    have hJHeight := (Finset.mem_filter.mp hJ).2
    have hFineHeight : 10 ≤
        ((nonshrinkingFineValues fine coarse) ∩ representedValues fine (J - 1)).card :=
      hJHeight.trans (nonshrinkingRepresentedValues_card_le fine coarse (canonicalApprox k) h J)
    have hFine : (levelPrefixCoordinates fine (nonshrinkingFineValues fine coarse)
        (J - 1 + 1)).card ≤ 36 * (spreadCoordinates fine (1 / (k : ℝ))).card := by
      rw [levelPrefixCoordinates_eq_order_union]
      apply nonshrinking_orders_mass_le_spread hk fine coarse h
      · intro j hj
        apply Finset.mem_range.mpr
        have h' := Finset.mem_range.mp hj
        omega
      · intro j hj
        have hjJ : j ≤ J - 1 := by have h' := Finset.mem_range.mp hj; omega
        exact hFineHeight.trans (inter_representedValues_card_antitone fine
          (nonshrinkingFineValues fine coarse) hjJ)
    have hTransfer := nonshrinkingPrefix_mass_transfer fine coarse (canonicalApprox k) h J
    have hCoarse : (levelPrefixCoordinates coarse (nonshrinkingCoarseValues fine coarse)
        (J + 1)).card ≤ 288 * (spreadCoordinates fine (1 / (k : ℝ))).card :=
      hTransfer.trans (by omega)
    have hMass := creationOrder_union_mass_le_majority_add_shrinking fine coarse
      (majorityCoarseOrders fine coarse)
    rw [majorityCoarseOrders_eq_range_max fine coarse hV,
      ← levelPrefixCoordinates_eq_order_union] at hMass
    rw [majorityCoarseOrders_eq_range_max fine coarse hV]
    exact hMass.trans (Nat.add_le_add_right hCoarse _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hV, Finset.biUnion_empty, Finset.card_empty]
    exact Nat.zero_le _

theorem refinement_high_order_mass_le {n k : ℕ} (hk : 0 < k)
    (fine coarse : Fin n → ℂ) (h : ∀ i, coarse i = canonicalApprox k (fine i)) :
    (highCombinedHeightCoordinates coarse).card ≤
      288 * (spreadCoordinates fine (1 / (k : ℝ))).card +
        41 * (shrinkingCoordinates fine coarse).card := by
  have hHigh := highCombinedHeight_mass_le_majority_add fine coarse
  have hMajority := majority_orders_mass_le_fine_spread_add hk fine coarse h
  omega

theorem canonicalApprox_pow_high_order_mass_le {n d : ℕ} (hd : 0 < d)
    (u : ℕ) (x : Fin n → ℂ) :
    (highCombinedHeightCoordinates (fun i => canonicalApprox (d ^ u) (x i))).card ≤
      288 * (spreadCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        (1 / (d ^ u : ℕ))).card +
      41 * (shrinkingCoordinates (fun i => canonicalApprox (d ^ (u + 1)) (x i))
        (fun i => canonicalApprox (d ^ u) (x i))).card :=
  refinement_high_order_mass_le (pow_pos hd u) _ _
    (fun i => (canonicalApprox_pow_refinement hd u (x i)).symm)

theorem refinement_spread_or_shrinking {n k : ℕ} (hk : 0 < k)
    (fine coarse : Fin n → ℂ) (h : ∀ i, coarse i = canonicalApprox k (fine i))
    {M : ℝ} (hMass : M / 8 ≤ (highCombinedHeightCoordinates coarse).card) :
    M / 4608 ≤ (spreadCoordinates fine (1 / (k : ℝ))).card ∨
      M / 656 ≤ (shrinkingCoordinates fine coarse).card := by
  have hCount := refinement_high_order_mass_le hk fine coarse h
  have hCountR : ((highCombinedHeightCoordinates coarse).card : ℝ) ≤
      288 * (spreadCoordinates fine (1 / (k : ℝ))).card +
        41 * (shrinkingCoordinates fine coarse).card := by exact_mod_cast hCount
  by_contra hNo
  push_neg at hNo
  linarith

theorem canonicalApprox_pow_spread_separation {d : ℕ} (hd : 0 < d) (u : ℕ) :
    (d : ℝ) / (d ^ (u + 1) : ℕ) = 1 / (d ^ u : ℕ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpR : (d ^ u : ℕ) ≠ (0 : ℝ) := by exact_mod_cast (pow_pos hd u).ne'
  rw [pow_succ, Nat.cast_mul]
  field_simp

end CircularLaw
