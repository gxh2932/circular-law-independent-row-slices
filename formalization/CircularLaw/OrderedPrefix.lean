import CircularLaw.OrderedCoordinates

/-!
# Actual top coordinate sets

The prefix uses the decreasing-norm permutation, retaining tied
coordinates in its chosen order. Its cardinality and norm bounds apply
to the vector itself, without a separate rank data assumption.
-/

noncomputable section
open Classical

namespace CircularLaw

def orderedPrefix {n : ℕ} (x : Fin n → ℂ) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ((normOrderPerm x).symm j).val < t)

theorem mem_orderedPrefix {n : ℕ} (x : Fin n → ℂ) (t : ℕ) (j : Fin n) :
    j ∈ orderedPrefix x t ↔ ((normOrderPerm x).symm j).val < t := by
  simp only [orderedPrefix, Finset.mem_filter, Finset.mem_univ, true_and]

theorem orderedPrefix_subset {n s t : ℕ} (x : Fin n → ℂ) (hst : s ≤ t) :
    orderedPrefix x s ⊆ orderedPrefix x t := by
  intro j hj
  exact (mem_orderedPrefix x t j).mpr (lt_of_lt_of_le ((mem_orderedPrefix x s j).mp hj) hst)

def orderedPrefixEquiv {n t : ℕ} (x : Fin n → ℂ) (htn : t ≤ n) :
    ↥(orderedPrefix x t) ≃ Fin t where
  toFun j := ⟨((normOrderPerm x).symm j.val).val,
    (mem_orderedPrefix x t j.val).mp j.property⟩
  invFun k := ⟨normOrderPerm x ⟨k.val, lt_of_lt_of_le k.isLt htn⟩,
    (mem_orderedPrefix x t _).mpr (by simpa only [Equiv.symm_apply_apply] using k.isLt)⟩
  left_inv j := by
    apply Subtype.ext
    exact (normOrderPerm x).apply_symm_apply j.val
  right_inv k := by
    apply Fin.ext
    simp only [Equiv.symm_apply_apply]

theorem orderedPrefix_card {n t : ℕ} (x : Fin n → ℂ) (htn : t ≤ n) :
    (orderedPrefix x t).card = t := by
  rw [← Fintype.card_coe, Fintype.card_congr (orderedPrefixEquiv x htn), Fintype.card_fin]

theorem norm_mem_orderedPrefix {n s : ℕ} (x : Fin n → ℂ) (hs : 0 < s) (hsn : s ≤ n)
    (j : Fin n) (hj : j ∈ orderedPrefix x s) :
    orderedNorm x ⟨s - 1, by omega⟩ ≤ ‖x j‖ := by
  have hRank : (normOrderPerm x).symm j ≤ (⟨s - 1, by omega⟩ : Fin n) := by
    apply Fin.le_iff_val_le_val.mpr
    change ((normOrderPerm x).symm j).val ≤ s - 1
    have h := (mem_orderedPrefix x s j).mp hj
    omega
  have h := orderedNorm_antitone x hRank
  simpa only [orderedNorm_of_rank] using h

theorem norm_notMem_orderedPrefix {n t : ℕ} (x : Fin n → ℂ) (ht : 0 < t) (htn : t ≤ n)
    (j : Fin n) (hj : j ∉ orderedPrefix x t) :
    ‖x j‖ ≤ orderedNorm x ⟨t - 1, by omega⟩ := by
  have hRank : (⟨t - 1, by omega⟩ : Fin n) ≤ (normOrderPerm x).symm j := by
    apply Fin.le_iff_val_le_val.mpr
    change t - 1 ≤ ((normOrderPerm x).symm j).val
    have h : ¬((normOrderPerm x).symm j).val < t := fun h =>
      hj ((mem_orderedPrefix x t j).mpr h)
    omega
  have h := orderedNorm_antitone x hRank
  simpa only [orderedNorm_of_rank] using h

end CircularLaw
