import CircularLaw.LLYSteepGeometry
import CircularLaw.InvertibilityDistanceGeometry

/-!
# The four bad-coordinate blocks in the LLY almost-constant argument

These blocks use the actual ordered prefixes. Their coordinate bounds
follow from the two gradual gaps and the proved constant-centre bound.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyBadTop {n : ℕ} (x : Fin n → ℂ) (F : Finset (Fin n)) (k₁ : ℕ) : Finset (Fin n) :=
  orderedPrefix x (k₁ - 1) \ F

def llyBadSecond {n : ℕ} (x : Fin n → ℂ) (F : Finset (Fin n)) (k₁ k₂ : ℕ) : Finset (Fin n) :=
  orderedPrefix x k₂ \ (F ∪ orderedPrefix x (k₁ - 1))

def llyBadThird {n : ℕ} (x : Fin n → ℂ) (F : Finset (Fin n)) (k₂ k₃ : ℕ) : Finset (Fin n) :=
  orderedPrefix x k₃ \ (F ∪ orderedPrefix x k₂)

def llyBadTail {n : ℕ} (x : Fin n → ℂ) (F : Finset (Fin n)) (k₃ : ℕ) : Finset (Fin n) :=
  Finset.univ \ (F ∪ orderedPrefix x k₃)

theorem lly_bad_blocks_cover {n k₁ k₂ k₃ : ℕ} (x : Fin n → ℂ) (F : Finset (Fin n)) :
    Finset.univ \ F = llyBadTop x F k₁ ∪ llyBadSecond x F k₁ k₂ ∪
      llyBadThird x F k₂ k₃ ∪ llyBadTail x F k₃ := by
  ext j
  simp only [llyBadTop, llyBadSecond, llyBadThird, llyBadTail, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_univ, true_and]
  tauto

theorem lly_bad_blocks_card_bounds {n k₁ k₂ k₃ : ℕ} (x : Fin n → ℂ)
    (F : Finset (Fin n)) (hk₁ : k₁ ≤ n) (hk₂ : k₂ ≤ n)
    (hMany : n - k₃ < F.card) :
    (llyBadTop x F k₁).card ≤ k₁ ∧ (llyBadSecond x F k₁ k₂).card ≤ k₂ ∧
      (llyBadThird x F k₂ k₃).card ≤ k₃ ∧ (llyBadTail x F k₃).card ≤ k₃ := by
  have hTop : (llyBadTop x F k₁).card ≤ k₁ :=
    ((Finset.card_le_card Finset.sdiff_subset).trans_eq
      (orderedPrefix_card x (show k₁ - 1 ≤ n by omega))).trans (Nat.sub_le k₁ 1)
  have hSecond : (llyBadSecond x F k₁ k₂).card ≤ k₂ :=
    (Finset.card_le_card Finset.sdiff_subset).trans_eq (orderedPrefix_card x hk₂)
  have hThird : (llyBadThird x F k₂ k₃).card ≤ k₃ := by
    by_cases hk₃ : k₃ ≤ n
    · exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (orderedPrefix_card x hk₃)
    · exact (Finset.card_le_univ _).trans (by simpa only [Fintype.card_fin] using (by omega : n ≤ k₃))
  have hTail : (llyBadTail x F k₃).card ≤ k₃ := by
    have hSub : llyBadTail x F k₃ ⊆ Finset.univ \ F := by
      intro j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j,
        fun hF => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ hF)⟩
    have h := Finset.card_le_card hSub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin] at h
    omega
  exact ⟨hTop, hSecond, hThird, hTail⟩

theorem lly_almost_center_bounds {n k₃ : ℕ} (hk₃ : 0 < k₃) (hHalf : 2 * k₃ ≤ n)
    (x : Fin n → ℂ) (F : Finset (Fin n)) (c : ℂ) (hMany : n - k₃ < F.card)
    (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ orderedNormAt x k₃ / 5) :
    4 / 5 * orderedNormAt x k₃ ≤ ‖c‖ ∧ ‖c‖ ≤ 6 / 5 * orderedNormAt x k₃ := by
  have h := center_bounds_of_many_close hk₃ hHalf x (1 / 5) c F hMany (by
    intro j hj
    simpa only [one_div_mul_eq_div] using hClose j hj)
  norm_num at h
  exact h

theorem lly_almost_block_coordinate_bounds {n d k₁ k₂ k₃ : ℕ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n)
    (x : Fin n → ℂ) (F : Finset (Fin n)) (c : ℂ)
    (hGap₁ : orderedNormAt x k₁ ≤ (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt x k₂)
    (hGap₂ : orderedNormAt x k₂ ≤ 4 * orderedNormAt x k₃)
    (hCenter : 4 / 5 * orderedNormAt x k₃ ≤ ‖c‖) :
    (∀ j ∈ llyBadSecond x F k₁ k₂, ‖x j‖ ≤ 5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖) ∧
      (∀ j ∈ llyBadThird x F k₂ k₃, ‖x j‖ ≤ 5 * ‖c‖) ∧
      (∀ j ∈ llyBadTail x F k₃, ‖x j‖ ≤ 5 / 4 * ‖c‖) ∧
      (∀ j ∉ orderedPrefix x k₃, ‖x j‖ ≤ 5 / 4 * ‖c‖) := by
  have hTail : orderedNormAt x k₃ ≤ 5 / 4 * ‖c‖ := by linarith
  have hSecond : orderedNormAt x k₁ ≤ 5 * (d : ℝ) ^ (3 / 4 : ℝ) * ‖c‖ := by
    have hScaled := mul_le_mul_of_nonneg_left hGap₂
      (Real.rpow_nonneg (Nat.cast_nonneg d) (3 / 4 : ℝ))
    have hScaledTail := mul_le_mul_of_nonneg_left hTail
      (show 0 ≤ 4 * (d : ℝ) ^ (3 / 4 : ℝ) by positivity)
    nlinarith only [hGap₁, hScaled, hScaledTail]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    apply (norm_le_orderedNormAt_notMem_strict_prefix x hk₁ hk₁n j ?_).trans hSecond
    exact fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_right _ h)
  · intro j hj
    have hNot : j ∉ orderedPrefix x k₂ := fun h =>
      (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_right _ h)
    have hNorm := (norm_le_orderedNormAt_notMem_prefix x hk₂ hk₂n j hNot).trans hGap₂
    linarith
  · intro j hj
    apply (norm_le_orderedNormAt_notMem_prefix x hk₃ hk₃n j ?_).trans hTail
    exact fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_right _ h)
  · intro j hj
    exact (norm_le_orderedNormAt_notMem_prefix x hk₃ hk₃n j hj).trans hTail

theorem lly_unit_almost_constant_center {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₃n : k₃ ≤ n)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    ∃ c : ℂ, ∃ F : Finset (Fin n), n - k₃ < F.card ∧
      ∀ j ∈ F, ‖x j - c‖ ≤ orderedNormAt (fun j => x j) k₃ / 5 := by
  unfold sourceNonAlmostConstant at hAlmost
  push_neg at hAlmost
  obtain ⟨c, hc⟩ := hAlmost
  let F := Finset.univ.filter (fun j => ‖x j - c‖ ≤ ρ / Real.sqrt n)
  have hMany : n - k₃ < F.card := by
    have hReal : ((n - k₃ : ℕ) : ℝ) < F.card := by
      rw [Nat.cast_sub hk₃n]
      change (n : ℝ) - k₃ < F.card
      dsimp only [F] at *
      nlinarith only [hc, hDensity]
    exact_mod_cast hReal
  have hB := lly_gradual_norm_constant_pos hn hd (r := r) (k₁ := k₁)
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hNorm := lly_gradual_norm_bound hn hk₁ hFit x hGradual
  rw [hUnit] at hNorm
  have hCloseRadius : ρ / Real.sqrt n ≤ orderedNormAt (fun j => x j) k₃ / 5 := by
    have hR := (le_div_iff₀ (by positivity : 0 < 5 * llyGradualNormConstant n d r k₁)).mp hRadius
    apply (div_le_iff₀ hRoot).mpr
    apply (mul_le_mul_iff_left₀
      (show 0 < 5 * llyGradualNormConstant n d r k₁ by positivity)).mp
    have hN := mul_le_mul_of_nonneg_right hNorm hRoot.le
    nlinarith only [hR, hN]
  refine ⟨c, F, hMany, ?_⟩
  intro j hj
  exact ((Finset.mem_filter.mp hj).2).trans hCloseRadius

theorem lly_bad_top_strict_prefix_card {n k₁ : ℕ} (x : Fin n → ℂ)
    (F : Finset (Fin n)) (hk₁ : k₁ ≤ n) : (llyBadTop x F k₁).card ≤ k₁ - 1 :=
  (Finset.card_le_card Finset.sdiff_subset).trans_eq
    (orderedPrefix_card x (show k₁ - 1 ≤ n by omega))

theorem lly_bad_top_rank_one_empty {n : ℕ} (x : Fin n → ℂ) (F : Finset (Fin n)) :
    llyBadTop x F 1 = ∅ := by
  simp [llyBadTop, orderedPrefix]

end CircularLaw
