import CircularLaw.OrderedPrefix

/-!
# One-based ordered moduli

This is the manuscript's `x_k^*` for `1 <= k <= n`. It is set to zero
outside that range solely to make the source class definitions total;
every use of a source rank proves that it is in the valid range.
-/

noncomputable section
open Classical

namespace CircularLaw

def orderedNormAt {n : ℕ} (x : Fin n → ℂ) (k : ℕ) : ℝ :=
  if h : 0 < k ∧ k ≤ n then orderedNorm x ⟨k - 1, by omega⟩ else 0

theorem orderedNormAt_eq {n k : ℕ} (x : Fin n → ℂ) (hk : 0 < k) (hkn : k ≤ n) :
    orderedNormAt x k = orderedNorm x ⟨k - 1, by omega⟩ := by
  simp only [orderedNormAt, dif_pos (show 0 < k ∧ k ≤ n from ⟨hk, hkn⟩)]

theorem orderedNormAt_nonneg {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    0 ≤ orderedNormAt x k := by
  unfold orderedNormAt
  split
  · exact orderedNorm_nonneg _ _
  · exact le_refl 0

theorem orderedNormAt_antitone {n s t : ℕ} (x : Fin n → ℂ)
    (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n) :
    orderedNormAt x t ≤ orderedNormAt x s := by
  rw [orderedNormAt_eq x (by omega : 0 < t) htn,
    orderedNormAt_eq x hs (by omega : s ≤ n)]
  apply orderedNorm_antitone x
  apply Fin.le_iff_val_le_val.mpr
  change s - 1 ≤ t - 1
  omega

theorem orderedNormAt_le_norm_mem_prefix {n s : ℕ} (x : Fin n → ℂ)
    (hs : 0 < s) (hsn : s ≤ n) (j : Fin n) (hj : j ∈ orderedPrefix x s) :
    orderedNormAt x s ≤ ‖x j‖ := by
  rw [orderedNormAt_eq x hs hsn]
  exact norm_mem_orderedPrefix x hs hsn j hj

theorem norm_le_orderedNormAt_notMem_prefix {n t : ℕ} (x : Fin n → ℂ)
    (ht : 0 < t) (htn : t ≤ n) (j : Fin n) (hj : j ∉ orderedPrefix x t) :
    ‖x j‖ ≤ orderedNormAt x t := by
  rw [orderedNormAt_eq x ht htn]
  exact norm_notMem_orderedPrefix x ht htn j hj

theorem norm_le_orderedNormAt_notMem_strict_prefix {n t : ℕ} (x : Fin n → ℂ)
    (ht : 0 < t) (htn : t ≤ n) (j : Fin n) (hj : j ∉ orderedPrefix x (t - 1)) :
    ‖x j‖ ≤ orderedNormAt x t := by
  rw [orderedNormAt_eq x ht htn]
  have hNot : ¬((normOrderPerm x).symm j).val < t - 1 := fun h =>
    hj ((mem_orderedPrefix x (t - 1) j).mpr h)
  have hRank : (⟨t - 1, by omega⟩ : Fin n) ≤ (normOrderPerm x).symm j :=
    Fin.le_iff_val_le_val.mpr (by change t - 1 ≤ ((normOrderPerm x).symm j).val; omega)
  simpa only [orderedNorm_of_rank] using orderedNorm_antitone x hRank

end CircularLaw
