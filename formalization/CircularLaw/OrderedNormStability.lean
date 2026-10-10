import CircularLaw.OrderedNormAt

/-!
# Stability of the actual order statistics

Coordinatewise perturbations bound the sorted moduli without assuming
that the sorting permutations agree. This supplies the stability used
by the source shifted-class inclusions and net arguments.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem orderedNormAt_le_of_pointwise {n k : ℕ} (x y : Fin n → ℂ)
    (hk : 0 < k) (hkn : k ≤ n) (a : ℝ) (hPointwise : ∀ j, ‖y j‖ ≤ ‖x j‖ + a) :
    orderedNormAt y k ≤ orderedNormAt x k + a := by
  by_contra h
  have hStrict : orderedNormAt x k + a < orderedNormAt y k := lt_of_not_ge h
  have hSub : orderedPrefix y k ⊆ orderedPrefix x (k - 1) := by
    intro j hj
    have hY := orderedNormAt_le_norm_mem_prefix y hk hkn j hj
    have hX : orderedNormAt x k < ‖x j‖ := by linarith [hPointwise j]
    apply (mem_orderedPrefix x (k - 1) j).mpr
    by_contra hRank
    have hLe : (⟨k - 1, by omega⟩ : Fin n) ≤ (normOrderPerm x).symm j := by
      apply Fin.le_iff_val_le_val.mpr
      change k - 1 ≤ ((normOrderPerm x).symm j).val
      omega
    have hNorm := orderedNorm_antitone x hLe
    rw [orderedNorm_of_rank, ← orderedNormAt_eq x hk hkn] at hNorm
    exact (not_lt_of_ge hNorm) hX
  have hCard := Finset.card_le_card hSub
  rw [orderedPrefix_card y hkn, orderedPrefix_card x (by omega : k - 1 ≤ n)] at hCard
  omega

theorem orderedNormAt_perturbation {n k : ℕ} (x y : Fin n → ℂ)
    (hk : 0 < k) (hkn : k ≤ n) (a : ℝ) (hPointwise : ∀ j, ‖y j - x j‖ ≤ a) :
    orderedNormAt y k ≤ orderedNormAt x k + a ∧
      orderedNormAt x k - a ≤ orderedNormAt y k := by
  constructor
  · apply orderedNormAt_le_of_pointwise x y hk hkn a
    intro j
    have h := norm_sub_norm_le (y j) (x j)
    linarith [hPointwise j]
  · have hUpper := orderedNormAt_le_of_pointwise y x hk hkn a (by
      intro j
      have h := norm_sub_norm_le (x j) (y j)
      rw [norm_sub_rev] at h
      linarith [hPointwise j])
    linarith

theorem orderedNormAt_constant_shift {n k : ℕ} (x : Fin n → ℂ) (c : ℂ)
    (hk : 0 < k) (hkn : k ≤ n) :
    orderedNormAt (fun j => x j + c) k ≤ orderedNormAt x k + ‖c‖ ∧
      orderedNormAt x k - ‖c‖ ≤ orderedNormAt (fun j => x j + c) k := by
  apply orderedNormAt_perturbation x (fun j => x j + c) hk hkn ‖c‖
  intro j
  simp only [add_sub_cancel_left, le_refl]

end CircularLaw
