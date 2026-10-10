import CircularLaw.GaussianRepresentativeCombination
import CircularLaw.CopyClusterCounting
import CircularLaw.GreedyCorrelationOwners

/-!
# Transfer of representative closeness to a unit combination

The argument is uniform in the coefficient vector, so no measurable choice
of coefficients is needed. If fewer than half the coordinates are far in
any copy, every unit combination with equal representative values has a
disk containing more than half the retained coordinates.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem gaussianCopiesCombination_coordinate {n p : ℕ}
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ (Fin p)) (i : Fin n) :
    gaussianCopiesCombination Y x i = ∑ k, x k * Y k i := by
  rw [gaussianCopiesCombination_apply]
  have h := map_sum (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin n => ℂ) 2 i)
    (fun k => x k • Y k) Finset.univ
  exact h

theorem gaussianCopiesCombination_pair_bound {n p : ℕ}
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ (Fin p))
    (hx : ‖x‖ ≤ 1) (i j : Fin n) {α : ℝ}
    (hDiff : ∀ k, ‖Y k i - Y k j‖ ≤ α) :
    ‖gaussianCopiesCombination Y x i - gaussianCopiesCombination Y x j‖ ≤ (p : ℝ) * α := by
  rw [gaussianCopiesCombination_coordinate, gaussianCopiesCombination_coordinate,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k, ‖x k * Y k i - x k * Y k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin p, α := by
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_sub, norm_mul]
      have hX := (PiLp.norm_apply_le x k).trans hx
      simpa only [one_mul] using mul_le_mul hX (hDiff k) (norm_nonneg _) (by norm_num)
    _ = _ := by simp [mul_comm]

theorem gaussianCopiesCombination_large_cluster {n p : ℕ}
    (K : Finset (Fin n)) (r : Fin n → Fin n) (Y : Fin p → EuclideanSpace ℂ (Fin n))
    (x : EuclideanSpace ℂ (Fin p)) (hx : ‖x‖ ≤ 1) (w : ℂ) (α : ℝ)
    (hRep : ∀ j ∈ K, gaussianCopiesCombination Y x (r j) = w)
    (hFar : ((copyFarCoordinates K r (fun k j => Y k j) α).card : ℝ) < (K.card : ℝ) / 2) :
    (K.card : ℝ) / 2 <
      ((K.filter (fun j => ‖gaussianCopiesCombination Y x j - w‖ ≤ (p : ℝ) * α)).card : ℝ) := by
  let B := copyFarCoordinates K r (fun k j => Y k j) α
  have hBK : B ⊆ K := Finset.filter_subset _ _
  have hSum := Finset.card_sdiff_add_card_eq_card hBK
  have hSumR : ((K \ B).card : ℝ) + B.card = K.card := by exact_mod_cast hSum
  have hHalf : (K.card : ℝ) / 2 < (K \ B).card := by
    change (B.card : ℝ) < (K.card : ℝ) / 2 at hFar
    linarith only [hSumR, hFar]
  apply hHalf.trans_le
  have hSubset : K \ B ⊆ K.filter
      (fun j => ‖gaussianCopiesCombination Y x j - w‖ ≤ (p : ℝ) * α) := by
    intro j hj
    obtain ⟨hjK, hjB⟩ := Finset.mem_sdiff.mp hj
    have hClose : ∀ k, ‖Y k j - Y k (r j)‖ < α := by
      change j ∉ K.filter (fun j => ∃ k : Fin p, α ≤ ‖Y k j - Y k (r j)‖) at hjB
      simpa only [Finset.mem_filter, hjK, true_and, not_exists, not_le] using hjB
    refine Finset.mem_filter.mpr ⟨hjK, ?_⟩
    rw [← hRep j hjK]
    exact gaussianCopiesCombination_pair_bound Y x hx j (r j) (fun k => (hClose k).le)
  exact_mod_cast Finset.card_le_card hSubset

theorem gaussianRepresentative_unit_large_cluster {n p : ℕ}
    (K : Finset (Fin n)) (r : Fin n → Fin n)
    (Y : Fin (p + 1) → EuclideanSpace ℂ (Fin n)) (u : Fin (p + 1) → Fin n) (α : ℝ)
    (hRange : ∀ j ∈ K, ∃ k, r j = u k)
    (hFar : ((copyFarCoordinates K r (fun k j => Y k j) α).card : ℝ) < (K.card : ℝ) / 2) :
    ∃ x : EuclideanSpace ℂ (Fin (p + 1)), ‖x‖ = 1 ∧
      ∃ w : ℂ, (K.card : ℝ) / 2 <
        ((K.filter (fun j => ‖gaussianCopiesCombination Y x j - w‖ ≤
          ((p + 1 : ℕ) : ℝ) * α)).card : ℝ) := by
  obtain ⟨x, hx, hEqual⟩ := gaussianRepresentative_unit_combination Y u
  refine ⟨x, hx, gaussianCopiesCombination Y x (u (Fin.last p)), ?_⟩
  apply gaussianCopiesCombination_large_cluster K r Y x hx.le _ α _ hFar
  intro j hj
  obtain ⟨k, hk⟩ := hRange j hj
  rw [hk]
  exact hEqual k

end CircularLaw
