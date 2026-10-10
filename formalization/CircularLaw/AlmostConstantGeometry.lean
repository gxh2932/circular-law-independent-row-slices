import CircularLaw.SourceRemainingClasses

/-!
# Geometry of the actual almost-constant coordinates

More than `n-k` small coordinates force the `k`th ordered modulus to
be small. The same count and `2*k <= n` give the manuscript's upper
and lower bounds on the constant center, including the zero-tail case.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem orderedNormAt_le_of_many_small {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (y : Fin n → ℂ) (B : ℝ) (F : Finset (Fin n)) (hMany : n - k < F.card)
    (hSmall : ∀ j ∈ F, ‖y j‖ ≤ B) : orderedNormAt y k ≤ B := by
  by_contra h
  have hStrict : B < orderedNormAt y k := lt_of_not_ge h
  have hSub : orderedPrefix y k ⊆ Finset.univ \ F := by
    intro j hj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩
    intro hjF
    have hNorm := orderedNormAt_le_norm_mem_prefix y hk hkn j hj
    exact (not_lt_of_ge ((hSmall j hjF).trans' hNorm)) hStrict
  have hCard := Finset.card_le_card hSub
  rw [orderedPrefix_card y hkn, Finset.card_sdiff_of_subset (Finset.subset_univ F),
    Finset.card_univ, Fintype.card_fin] at hCard
  have hF : F.card ≤ n := (Finset.card_le_univ F).trans_eq (Fintype.card_fin n)
  omega

theorem center_bounds_of_many_close {n k : ℕ} (hk : 0 < k) (hHalf : 2 * k ≤ n)
    (x : Fin n → ℂ) (θ : ℝ) (c : ℂ) (F : Finset (Fin n))
    (hMany : n - k < F.card)
    (hClose : ∀ j ∈ F, ‖x j - c‖ ≤ θ * orderedNormAt x k) :
    (1 - θ) * orderedNormAt x k ≤ ‖c‖ ∧
      ‖c‖ ≤ (1 + θ) * orderedNormAt x k := by
  have hkn : k ≤ n := by omega
  have hTopCard : (orderedPrefix x k).card = k := orderedPrefix_card x hkn
  have hSum : (Finset.univ : Finset (Fin n)).card < F.card + (orderedPrefix x k).card := by
    rw [Finset.card_univ, Fintype.card_fin, hTopCard]
    omega
  obtain ⟨j, hj⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ F) (Finset.subset_univ (orderedPrefix x k)) hSum
  have hLowNorm := orderedNormAt_le_norm_mem_prefix x hk hkn j (Finset.mem_inter.mp hj).2
  have hLowClose := hClose j (Finset.mem_inter.mp hj).1
  have hLowTriangle := norm_sub_norm_le (x j) c
  have hLower : (1 - θ) * orderedNormAt x k ≤ ‖c‖ := by nlinarith
  have hNotSub : ¬F ⊆ orderedPrefix x k := by
    intro hSub
    have hCard := Finset.card_le_card hSub
    rw [hTopCard] at hCard
    omega
  obtain ⟨j, hjF, hjNot⟩ := Finset.not_subset.mp hNotSub
  have hHighNorm := norm_le_orderedNormAt_notMem_prefix x hk hkn j hjNot
  have hHighClose := hClose j hjF
  have hHighTriangle := norm_sub_norm_le c (x j)
  rw [norm_sub_rev] at hHighTriangle
  exact ⟨hLower, by nlinarith⟩

theorem almost_constant_center_bounds {n k : ℕ} (hk : 0 < k) (hHalf : 2 * k ≤ n)
    (x : Fin n → ℂ) (θ : ℝ) (c : ℂ)
    (hMany : n - k < (almostConstantCoordinates x k θ c).card) :
    (1 - θ) * orderedNormAt x k ≤ ‖c‖ ∧
      ‖c‖ ≤ (1 + θ) * orderedNormAt x k := by
  apply center_bounds_of_many_close hk hHalf x θ c (almostConstantCoordinates x k θ c) hMany
  intro j hj
  exact (Finset.mem_filter.mp hj).2

theorem almost_constant_translated_tail {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (x : Fin n → ℂ) (θ : ℝ) (c : ℂ)
    (hMany : n - k < (almostConstantCoordinates x k θ c).card) :
    orderedNormAt (fun j => x j - c) k ≤ θ * orderedNormAt x k := by
  apply orderedNormAt_le_of_many_small hk hkn (fun j => x j - c)
    (θ * orderedNormAt x k) (almostConstantCoordinates x k θ c) hMany
  intro j hj
  exact (Finset.mem_filter.mp hj).2

end CircularLaw
