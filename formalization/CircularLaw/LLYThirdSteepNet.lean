import CircularLaw.LLYSteepGeometry
import CircularLaw.SparseGridNet

/-!
# Finite approximations of the actual LLY third steep class

The class uses the manuscript's factor-four jump. An almost-constant
center is subtracted before sparse truncation. The three grid ranges
retain the actual first and second LLY ranks, rather than replacing
this class with the distinct rectangular steep classes.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyThirdRawNet (n d r k₁ k₂ k₃ k : ℕ) : Finset (Fin n → ℂ) :=
  threeRangeGridNet n (k₁ - 1) (k₂ - 1) (k₃ - 1)
    (gridBox k (gridBoxRadius k ((6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)))
    (gridBox k (gridBoxRadius k ((d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)))
    (gridBox k (gridBoxRadius k (4 / 3)))

def llyThirdNonconstantNet (n d r k₁ k₂ k₃ k : ℕ) : Finset (Fin n → ℂ) :=
  (llyThirdRawNet n d r k₁ k₂ k₃ k).filter (fun u =>
    2 / 3 < orderedNormAt u k₂ ∧ orderedNormAt u k₃ = 0)

theorem lly_third_normalized_coordinate_ranges {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hFit : k₁ ≤ ℓ ^ (r + 1))
    (x : Fin n → ℂ) (hx : x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃)
    (hNormalized : orderedNormAt x k₂ = 1) :
    (∀ j, ‖x j‖ ≤ (6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ)) ∧
      orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) ∧ orderedNormAt x k₃ < 1 / 4 := by
  obtain ⟨hFirst, hSecond, hThird⟩ := hx
  have hMiddle : orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂ :=
    le_of_not_gt (fun h => hSecond ⟨hFirst, h⟩)
  rw [hNormalized, mul_one] at hMiddle
  rw [hNormalized] at hThird
  refine ⟨?_, hMiddle, by linarith⟩
  intro j
  exact (coordinate_norm_le_first_ordered hn x j).trans
    ((lly_not_first_steep_chain hk₁ hFit x hFirst).trans
      (mul_le_mul_of_nonneg_left hMiddle (by positivity)))

theorem center_upper_of_many_close {n k : ℕ} (hk : 0 < k) (hHalf : 2 * k ≤ n)
    (x : Fin n → ℂ) (c : ℂ) (F : Finset (Fin n)) {δ : ℝ}
    (hMany : n - k < F.card) (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ δ) :
    ‖c‖ ≤ orderedNormAt x k + δ := by
  have hkn : k ≤ n := by omega
  have hNotSub : ¬F ⊆ orderedPrefix x k := by
    intro hSub
    have hCard := Finset.card_le_card hSub
    rw [orderedPrefix_card x hkn] at hCard
    omega
  obtain ⟨j, hjF, hjNot⟩ := Finset.not_subset.mp hNotSub
  have hHigh := norm_le_orderedNormAt_notMem_prefix x hk hkn j hjNot
  have hTriangle := norm_sub_norm_le c (x j)
  rw [norm_sub_rev] at hTriangle
  linarith [hClose j hjF]

theorem lly_third_normalized_center_bound {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hk₃ : 0 < k₃) (hHalf : 2 * k₃ ≤ n) (x : Fin n → ℂ)
    (hx : x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) (hNormalized : orderedNormAt x k₂ = 1)
    (c : ℂ) (F : Finset (Fin n)) {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hMany : n - k₃ < F.card) (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ δ) : ‖c‖ ≤ 1 / 3 := by
  have hCenter := center_upper_of_many_close hk₃ hHalf x c F hMany hClose
  have hGap := hx.2.2
  rw [hNormalized] at hGap
  linarith

theorem lly_third_net_geometry {n d r k₁ k₂ k₃ k : ℕ} (u : Fin n → ℂ)
    (hu : u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k) :
    2 / 3 < orderedNormAt u k₂ ∧ orderedNormAt u k₃ = 0 := (Finset.mem_filter.mp hu).2

theorem lly_third_normalized_net_approximation {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hHalf : 2 * k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {δ : ℝ} (hδ : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (x : Fin n → ℂ) (hx : x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃)
    (hNormalized : orderedNormAt x k₂ = 1) (c : ℂ) (F : Finset (Fin n))
    (hMany : n - k₃ < F.card) (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ δ) :
    ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
      ∀ j, ‖(x j - c) - u j‖ ≤ δ := by
  have hn : 0 < n := by omega
  have hk₃n : k₃ ≤ n := by omega
  have hRanges := lly_third_normalized_coordinate_ranges hn hk₁ hFit x hx hNormalized
  have hCenter := lly_third_normalized_center_bound hk₃ hHalf x hx hNormalized c F hδ hMany hClose
  have hCenterSmall : ‖c‖ ≤ 1 / 4 + δ :=
    (center_upper_of_many_close hk₃ hHalf x c F hMany hClose).trans
      (add_le_add hRanges.2.2.le (le_refl δ))
  let y : Fin n → ℂ := fun j => x j - c
  have hTail : orderedNormAt y k₃ ≤ δ := orderedNormAt_le_of_many_small hk₃ hk₃n y δ F hMany hClose
  let u := truncatedCanonicalApprox k k₃ y
  have hApprox : ∀ j, ‖y j - u j‖ ≤ δ := truncatedCanonicalApprox_error hk hk₃ hk₃n hGrid y hTail
  have hTranslated (t : ℕ) (ht : 0 < t) (htn : t ≤ n) :
      orderedNormAt y t ≤ orderedNormAt x t + ‖c‖ :=
    orderedNormAt_le_of_pointwise x y ht htn ‖c‖ (fun j => norm_sub_le (x j) c)
  have hRaw : u ∈ llyThirdRawNet n d r k₁ k₂ k₃ k := by
    apply truncatedCanonicalApprox_mem_threeRangeGridNet hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n y
    · intro j
      exact (norm_sub_le _ _).trans (add_le_add (hRanges.1 j) hCenter)
    · exact (hTranslated k₁ hk₁ hk₁n).trans (add_le_add hRanges.2.1 hCenter)
    · have hBase := hTranslated k₂ hk₂ hk₂n
      rw [hNormalized] at hBase
      linarith
  have hLower : 1 - ‖c‖ ≤ orderedNormAt y k₂ := by
    have h := orderedNormAt_le_of_pointwise y x hk₂ hk₂n ‖c‖ (by
      intro j
      have hTriangle := norm_sub_norm_le (x j) (x j - c)
      simp only [sub_sub_cancel] at hTriangle
      linarith)
    rw [hNormalized] at h
    linarith
  have hPerturb := (orderedNormAt_perturbation y u hk₂ hk₂n δ
    (fun j => by simpa only [norm_sub_rev] using hApprox j)).2
  exact ⟨u, Finset.mem_filter.mpr ⟨hRaw,
    by refine ⟨by linarith, truncatedCanonicalApprox_tail_zero hk₃ hk₃n y⟩⟩, hApprox⟩

theorem lly_third_net_card_le (n d r k₁ k₂ k₃ k : ℕ) :
    (llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card ≤
      (smallCoordinateSets n (k₁ - 1)).card * (smallCoordinateSets n (k₂ - 1)).card *
        (smallCoordinateSets n (k₃ - 1)).card *
          ((2 * gridBoxRadius k ((6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3) + 1) ^ (2 * (k₁ - 1)) *
            (2 * gridBoxRadius k ((d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3) + 1) ^ (2 * (k₂ - 1)) *
              (2 * gridBoxRadius k (4 / 3) + 1) ^ (2 * (k₃ - 1))) := by
  apply (Finset.card_filter_le _ _).trans
  apply (threeRangeGridNet_card_le _ _ _
    ⟨0, zero_mem_gridBox _ _⟩ ⟨0, zero_mem_gridBox _ _⟩ ⟨0, zero_mem_gridBox _ _⟩).trans
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul <;> apply (Nat.pow_le_pow_left (gridBox_card_le _ _) _).trans_eq <;>
      rw [← pow_mul]
  · apply (Nat.pow_le_pow_left (gridBox_card_le _ _) _).trans_eq
    rw [← pow_mul]

end CircularLaw
