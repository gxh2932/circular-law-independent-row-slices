import CircularLaw.LLYFirstScaleEntropy
import CircularLaw.LLYFirstSteepGeometry
import CircularLaw.SparseGridNet

/-!
# Coordinate caps from every actual first-jump scale

Starting the exclusion chain at each scale gives its remaining power
of six times the degree. These caps are the input to the refined
second-class net whose grid costs use the geometric scale sum.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_not_first_steep_chain_from {n d ℓ r k : ℕ} (hFit : k ≤ ℓ ^ (r + 1))
    (x : Fin n → ℂ) (hx : x ∉ llyFirstSteep d ℓ r k) (i : ℕ) (hi : i ≤ r + 1) :
    orderedNormAt x (llyFirstRank ℓ k i) ≤
      (6 * (d : ℝ)) ^ (r + 1 - i) * orderedNormAt x k := by
  have hChain : ∀ j : ℕ, i + j ≤ r + 1 →
      orderedNormAt x (llyFirstRank ℓ k i) ≤
        (6 * (d : ℝ)) ^ j * orderedNormAt x (llyFirstRank ℓ k (i + j)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hStep : orderedNormAt x (llyFirstRank ℓ k (i + j)) ≤
          6 * (d : ℝ) * orderedNormAt x (llyFirstRank ℓ k (i + j + 1)) := by
        apply le_of_not_gt
        intro h
        exact hx ⟨i + j, Finset.mem_range.mpr (by omega), h⟩
      calc
        _ ≤ (6 * (d : ℝ)) ^ j * orderedNormAt x (llyFirstRank ℓ k (i + j)) := ih (by omega)
        _ ≤ (6 * (d : ℝ)) ^ j *
            (6 * d * orderedNormAt x (llyFirstRank ℓ k (i + j + 1))) :=
          mul_le_mul_of_nonneg_left hStep (by positivity)
        _ = _ := by
          rw [show i + j + 1 = i + (j + 1) by omega, pow_succ]
          ring
  have h := hChain (r + 1 - i) (by omega)
  rw [show i + (r + 1 - i) = r + 1 by omega, lly_first_rank_terminal hFit] at h
  exact h

theorem lly_not_first_steep_scale_coordinate_cap {n d ℓ r k : ℕ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n) (hFit : k ≤ ℓ ^ (r + 1))
    (x : Fin n → ℂ) (hx : x ∉ llyFirstSteep d ℓ r k)
    (i : ℕ) (hi : i ≤ r + 1) (j : Fin n)
    (hj : j ∉ orderedPrefix x (llyFirstRank ℓ k i - 1)) :
    ‖x j‖ ≤ (6 * (d : ℝ)) ^ (r + 1 - i) * orderedNormAt x k := by
  exact (norm_le_orderedNormAt_notMem_prev_prefix x (lly_first_rank_pos hℓ hk i)
    ((min_le_right _ _).trans hkn) j hj).trans (lly_not_first_steep_chain_from hFit x hx i hi)

theorem lly_second_normalized_scale_coordinate_cap {n d ℓ r k₁ k₂ : ℕ}
    (hℓ : 0 < ℓ) (hk₁ : 0 < k₁) (hk₁n : k₁ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    (x : Fin n → ℂ) (hx : x ∈ llySecondSteep d ℓ r k₁ k₂)
    (hNormalized : orderedNormAt x k₁ = 1) (i : ℕ) (hi : i ≤ r + 1)
    (j : Fin n) (hj : j ∉ orderedPrefix x (llyFirstRank ℓ k₁ i - 1)) :
    ‖x j‖ ≤ (6 * (d : ℝ)) ^ (r + 1 - i) := by
  simpa only [hNormalized, mul_one] using lly_not_first_steep_scale_coordinate_cap hℓ hk₁ hk₁n
    hFit x hx.1 i hi j hj

end CircularLaw
