import CircularLaw.LargeSelectedLevel
import CircularLaw.WeightHeightBounds
import CircularLaw.CanonicalBinCompression

/-!
# A low weight order from an actual repeated value

A value occurring at least `delta*n/9` times gives a canonical part
of size at least `delta*n/36` and height at most `72/delta`. Its actual
truncated weight is at most `72*sqrt(d)/delta`. The corresponding
coordinate probability tail uses the unchanged dyadic weight orders.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem canonical_part_containing_selected_level {n : ℕ} (y : Fin n → ℂ)
    (η : ℝ) (j : Fin (n + 2)) (z : ℂ) (hz : (selectedLevelAt y j.val z).Nonempty) :
    ∃ q : CanonicalLabel y η, q.val.2 = j ∧ selectedLevelAt y j.val z ⊆ taggedPart y η q.val := by
  have hRep := (selectedLevelAt_nonempty_mem y j.val z).mp hz
  by_cases hSpread : z ∈ spreadValueSet y j.val η
  · have hSubset : selectedLevelAt y j.val z ⊆ taggedPart y η (true, j) :=
      fun _ hi => Finset.mem_biUnion.mpr ⟨z, hSpread, hi⟩
    exact ⟨⟨(true, j), hz.mono hSubset⟩, rfl, hSubset⟩
  · have hSubset : selectedLevelAt y j.val z ⊆ taggedPart y η (false, j) :=
      fun _ hi => Finset.mem_biUnion.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hRep, hSpread⟩, hi⟩
    exact ⟨⟨(false, j), hz.mono hSubset⟩, rfl, hSubset⟩

theorem canonical_repeated_value_large_low_weight_part {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (y : Fin n → ℂ) (η : ℝ) (z : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hRepeat : δ * n / 9 ≤ (initialLevel y z).card) :
    ∃ q : CanonicalLabel y η, δ * n / 36 ≤ (profilePartSize (canonicalRowProfile y η) q : ℝ) ∧
      truncatedProfileWeight (canonicalRowProfile y η) d q ≤ 72 * Real.sqrt d / δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (0 : ℝ) < (initialLevel y z).card := lt_of_lt_of_le (by positivity) hRepeat
  have hz : (initialLevel y z).Nonempty := Finset.card_pos.mp (by exact_mod_cast hM)
  obtain ⟨j, hj, hNonempty, hChunk, hPower⟩ := selectedLevelAt_large_final_chunk y z hz
  obtain ⟨q, hOrder, hSubset⟩ := canonical_part_containing_selected_level y η ⟨j, hj⟩ z hNonempty
  have hSize : profilePartSize (canonicalRowProfile y η) q = (taggedPart y η q.val).card :=
    canonicalPart_card y η q
  have hPartN : profilePartSize (canonicalRowProfile y η) q ≤ n := by
    rw [hSize]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hLevel : (selectedLevelAt y j z).card ≤ profilePartSize (canonicalRowProfile y η) q := by
    rw [hSize]
    exact Finset.card_le_card hSubset
  have hLarge : δ * n / 36 ≤ (profilePartSize (canonicalRowProfile y η) q : ℝ) := by
    have hChunkR : ((initialLevel y z).card : ℝ) ≤ 4 * (selectedLevelAt y j z).card := by exact_mod_cast hChunk
    have hLevelR : ((selectedLevelAt y j z).card : ℝ) ≤ profilePartSize (canonicalRowProfile y η) q := by exact_mod_cast hLevel
    linarith
  have hLower := (canonicalPart_size_height y η q).1
  rw [hOrder] at hLower
  have hMassHeight : (initialLevel y z).card * (canonicalRowProfile y η).height q ≤ 8 * n := by
    have hMult := Nat.mul_le_mul_right ((canonicalRowProfile y η).height q) hPower
    change 2 ^ (j - 1) * (canonicalRowProfile y η).height q ≤ profilePartSize (canonicalRowProfile y η) q at hLower
    nlinarith
  have hHeight : ((canonicalRowProfile y η).height q : ℝ) ≤ 72 / δ := by
    have hMassHeightR : ((initialLevel y z).card : ℝ) * (canonicalRowProfile y η).height q ≤ 8 * n := by exact_mod_cast hMassHeight
    have hMult := mul_le_mul_of_nonneg_right hRepeat
      (Nat.cast_nonneg ((canonicalRowProfile y η).height q) : (0 : ℝ) ≤ _)
    have hN : (δ * ((canonicalRowProfile y η).height q : ℝ)) * n ≤ 72 * n := by nlinarith
    have h := (mul_le_mul_iff_left₀ hnR).mp hN
    exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using h)
  refine ⟨q, hLarge, ?_⟩
  calc
    _ ≤ ((canonicalRowProfile y η).height q : ℝ) * Real.sqrt d :=
      truncatedProfileWeight_le_height_sqrt_degree _ hd q
    _ ≤ (72 / δ) * Real.sqrt d := mul_le_mul_of_nonneg_right hHeight (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem orderedCanonical_truncatedProfileWeight_eq {n : ℕ} (y : Fin n → ℂ) (η : ℝ)
    (d : ℕ) (q : Fin (Fintype.card (CanonicalLabel y η))) :
    truncatedProfileWeight (orderedCanonicalRowProfile y η) d q =
      truncatedProfileWeight (canonicalRowProfile y η) d (canonicalEnumeration y η q) := by
  have hMass : partMass (orderedCanonicalRowProfile y η).part q =
      partMass (canonicalRowProfile y η).part (canonicalEnumeration y η q) := by
    rw [partMass_eq_profile_size, partMass_eq_profile_size, orderedCanonical_profilePartSize_eq]
  unfold truncatedProfileWeight
  rw [hMass]
  rfl

theorem orderedCanonical_repeated_value_large_low_weight_part {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (y : Fin n → ℂ) (η : ℝ) (z : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hRepeat : δ * n / 9 ≤ (initialLevel y z).card) :
    ∃ q : Fin (Fintype.card (CanonicalLabel y η)),
      δ * n / 36 ≤ (profilePartSize (orderedCanonicalRowProfile y η) q : ℝ) ∧
      truncatedProfileWeight (orderedCanonicalRowProfile y η) d q ≤ 72 * Real.sqrt d / δ := by
  obtain ⟨q, hMass, hWeight⟩ := canonical_repeated_value_large_low_weight_part hn hd y η z hδ hRepeat
  refine ⟨(canonicalEnumeration y η).symm q, ?_, ?_⟩
  · simpa only [orderedCanonical_profilePartSize_eq, Equiv.apply_symm_apply] using hMass
  · simpa only [orderedCanonical_truncatedProfileWeight_eq, Equiv.apply_symm_apply] using hWeight

theorem profile_part_probability_tail {n : ℕ} {ι : Type*}
    (P : RowProfile (Fin n) ι) (d : ℕ) (q : ι) (b : ℤ)
    (hb : dyadicProfilePartOrder P d q ≤ b) :
    (profilePartSize P q : ℝ) / n ≤
      uniformProbability (fun i => dyadicProfilePartOrder P d (P.part i) ≤ b) := by
  have hCard : profilePartSize P q ≤ (Finset.univ.filter
      (fun i => dyadicProfilePartOrder P d (P.part i) ≤ b)).card := by
    rw [profilePartSize, Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2 ▸ hb⟩
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hCard) (Nat.cast_nonneg n)

theorem orderedCanonical_repeated_value_low_tail {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (y : Fin n → ℂ) (η : ℝ) (z : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hRepeat : δ * n / 9 ≤ (initialLevel y z).card) :
    δ / 36 ≤ uniformProbability (fun i =>
      dyadicProfilePartOrder (orderedCanonicalRowProfile y η) d ((orderedCanonicalRowProfile y η).part i) ≤
        ⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋) := by
  obtain ⟨q, hMass, hWeight⟩ := orderedCanonical_repeated_value_large_low_weight_part hn hd y η z hδ hRepeat
  have hLog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (truncatedProfileWeight_pos _ hd q) hWeight
  have hOrder : dyadicProfilePartOrder (orderedCanonicalRowProfile y η) d q ≤
      ⌊Real.logb 2 (72 * Real.sqrt d / δ)⌋ := Int.floor_mono hLog
  have hTail := profile_part_probability_tail (orderedCanonicalRowProfile y η) d q _ hOrder
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (show δ / 36 ≤ (profilePartSize (orderedCanonicalRowProfile y η) q : ℝ) / n from
    (le_div_iff₀ hnR).mpr (by linarith)).trans hTail

end CircularLaw
