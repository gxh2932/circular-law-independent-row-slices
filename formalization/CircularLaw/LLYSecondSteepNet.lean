import CircularLaw.LayeredSparseGridNet
import CircularLaw.LLYFirstScaleCoordinateBounds

/-!
# A finite net covering the actual second LLY steep class

The normalized first rank has modulus one. Each first-jump scale gets
its own sparse grid and coordinate cap. Prefix increments telescope to
the high coordinates; the remaining truncated coordinates use the unit
cap. The count retains the product of these individual layer costs.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def llySecondLayerSize (ℓ r k₁ : ℕ) (i : Fin (r + 1)) : ℕ :=
  llyFirstRank ℓ k₁ (i.val + 1) - 1

def llySecondLayerGrid (d r k : ℕ) (i : Fin (r + 1)) : Finset ℂ :=
  gridBox k (gridBoxRadius k ((6 * (d : ℝ)) ^ (r + 1 - i.val)))

def llySecondRawNet (n d ℓ r k₁ k₂ k : ℕ) : Finset (Fin n → ℂ) :=
  layeredSparseGridNet n (llySecondLayerSize ℓ r k₁) (llySecondLayerGrid d r k)
    (k₂ - 1) (gridBox k (gridBoxRadius k 1))

def llySecondNonconstantNet (n d ℓ r k₁ k₂ k : ℕ) : Finset (Fin n → ℂ) :=
  (llySecondRawNet n d ℓ r k₁ k₂ k).filter (fun u =>
    2 / 3 < orderedNormAt u k₁ ∧ orderedNormAt u k₂ = 0)

theorem lly_second_truncation_mem_raw_net {n d ℓ r k₁ k₂ k : ℕ}
    (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (x : Fin n → ℂ)
    (hx : x ∈ llySecondSteep d ℓ r k₁ k₂) (hNormalized : orderedNormAt x k₁ = 1) :
    truncatedCanonicalApprox k k₂ x ∈ llySecondRawNet n d ℓ r k₁ k₂ k := by
  let u := truncatedCanonicalApprox k k₂ x
  let H : ℕ → Finset (Fin n) := fun t => orderedPrefix x (llyFirstRank ℓ k₁ t - 1)
  let P : ℕ → Fin n → ℂ := fun t j => if j ∈ H t then u j else 0
  let v : Fin (r + 1) → Fin n → ℂ := fun i j => P (i.val + 1) j - P i.val j
  let w : Fin n → ℂ := fun j => u j - P (r + 1) j
  have hNested (i : ℕ) : H i ⊆ H (i + 1) :=
    orderedPrefix_subset x (Nat.sub_le_sub_right (lly_first_rank_mono hℓ (by omega)) 1)
  have hLayer : ∀ i : Fin (r + 1), v i ∈ sparseGridFamily n
      (llySecondLayerSize ℓ r k₁ i) (llySecondLayerGrid d r k i) := by
    intro i
    apply (sparseGridFamily_mem _ _).mpr
    refine ⟨H (i.val + 1), ?_, ?_, ?_⟩
    · exact (orderedPrefix_card x
        ((Nat.sub_le _ _).trans ((min_le_right _ _).trans hk₁n))).le
    · intro j hj
      by_cases hOld : j ∈ H i.val
      · simp only [v, P, if_pos hj, if_pos hOld, sub_self]
        exact zero_mem_gridBox _ _
      · simp only [v, P, if_pos hj, if_neg hOld, sub_zero]
        by_cases hS : j ∈ orderedPrefix x (k₂ - 1)
        · simp only [u, truncatedCanonicalApprox, if_pos hS]
          exact canonicalApprox_mem_gridBox (x j)
            (lly_second_normalized_scale_coordinate_cap hℓ hk₁ hk₁n hFit x hx
              hNormalized i.val (by omega) j hOld)
        · simp only [u, truncatedCanonicalApprox, if_neg hS]
          exact zero_mem_gridBox _ _
    · intro j hj
      have hOld : j ∉ H i.val := fun h => hj (hNested i.val h)
      simp only [v, P, if_neg hj, if_neg hOld, sub_self]
  have hBase : w ∈ sparseGridFamily n (k₂ - 1) (gridBox k (gridBoxRadius k 1)) := by
    apply (sparseGridFamily_mem _ _).mpr
    refine ⟨orderedPrefix x (k₂ - 1), (orderedPrefix_card x (by omega)).le, ?_, ?_⟩
    · intro j hj
      by_cases hTop : j ∈ H (r + 1)
      · simp only [w, P, if_pos hTop, sub_self]
        exact zero_mem_gridBox _ _
      · simp only [w, P, if_neg hTop, sub_zero, u, truncatedCanonicalApprox, if_pos hj]
        have hNot : j ∉ orderedPrefix x (k₁ - 1) := by
          simpa only [H, lly_first_rank_terminal hFit] using hTop
        apply canonicalApprox_mem_gridBox (x j)
        simpa only [hNormalized] using norm_le_orderedNormAt_notMem_prev_prefix
          x hk₁ hk₁n j hNot
    · intro j hj
      have hU : u j = 0 := by simp only [u, truncatedCanonicalApprox, if_neg hj]
      simp only [w, P, hU, ite_self, sub_self]
  apply layeredSparseGridNet_mem _ _ _ v w u hLayer hBase
  intro j
  have hP0 : P 0 j = 0 := by
    have hj0 : j ∉ H 0 := by
      simp only [H, lly_first_rank_zero hk₁, Nat.sub_self, mem_orderedPrefix, not_lt_zero,
        not_false_eq_true]
    simp only [P, if_neg hj0]
  have hSum := Fin.sum_univ_eq_sum_range (fun i => P (i + 1) j - P i j) (r + 1)
  rw [Finset.sum_range_sub (fun t => P t j) (r + 1), hP0, sub_zero] at hSum
  change (∑ i : Fin (r + 1), (P (i.val + 1) j - P i.val j)) + (u j - P (r + 1) j) = u j
  rw [hSum]
  ring

theorem lly_second_net_geometry {n d ℓ r k₁ k₂ k : ℕ} (u : Fin n → ℂ)
    (hu : u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k) :
    2 / 3 < orderedNormAt u k₁ ∧ orderedNormAt u k₂ = 0 := (Finset.mem_filter.mp hu).2

theorem lly_second_normalized_net_approximation {n d ℓ r k₁ k₂ k : ℕ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {δ : ℝ} (hδ : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (x : Fin n → ℂ) (hx : x ∈ llySecondSteep d ℓ r k₁ k₂)
    (hNormalized : orderedNormAt x k₁ = 1) (hTail : orderedNormAt x k₂ ≤ δ) :
    ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∀ j, ‖x j - u j‖ ≤ δ := by
  let u := truncatedCanonicalApprox k k₂ x
  have hApprox : ∀ j, ‖x j - u j‖ ≤ δ :=
    truncatedCanonicalApprox_error hk hk₂ hk₂n hGrid x hTail
  have hLower := (orderedNormAt_perturbation x u hk₁ hk₁n δ
    (fun j => by simpa only [norm_sub_rev] using hApprox j)).2
  rw [hNormalized] at hLower
  refine ⟨u, Finset.mem_filter.mpr ⟨lly_second_truncation_mem_raw_net
    hℓ hk₁ hk₁n hk₂n hFit x hx hNormalized, ?_⟩, hApprox⟩
  exact ⟨by linarith, truncatedCanonicalApprox_tail_zero hk₂ hk₂n x⟩

theorem lly_second_normalized_net_approximation_degree {n d ℓ r k₁ k₂ k : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {δ : ℝ} (hδ : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (x : Fin n → ℂ) (hx : x ∈ llySecondSteep d ℓ r k₁ k₂)
    (hNormalized : orderedNormAt x k₁ = 1) :
    ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∀ j, ‖x j - u j‖ ≤ δ := by
  apply lly_second_normalized_net_approximation hℓ hk hk₁ hk₂ hk₁n hk₂n hFit
    hδ hGrid x hx hNormalized
  have hPow : 0 < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hGap := hx.2
  rw [hNormalized] at hGap
  exact ((lt_div_iff₀ hPow).mpr (by simpa only [mul_comm] using hGap)).le.trans hResolution

theorem lly_second_net_card_le (n d ℓ r k₁ k₂ k : ℕ) :
    (llySecondNonconstantNet n d ℓ r k₁ k₂ k).card ≤
      (∏ i : Fin (r + 1), (smallCoordinateSets n (llySecondLayerSize ℓ r k₁ i)).card *
        (llySecondLayerGrid d r k i).card ^ llySecondLayerSize ℓ r k₁ i) *
      ((smallCoordinateSets n (k₂ - 1)).card * (gridBox k (gridBoxRadius k 1)).card ^ (k₂ - 1)) := by
  exact (Finset.card_filter_le _ _).trans (layeredSparseGridNet_card_le _ _ _
    (fun _ => ⟨0, zero_mem_gridBox _ _⟩) ⟨0, zero_mem_gridBox _ _⟩)

end CircularLaw
