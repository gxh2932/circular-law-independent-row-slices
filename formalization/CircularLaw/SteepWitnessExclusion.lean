import CircularLaw.UniqueWitnessFailure
import CircularLaw.UniqueWitnessAction
import CircularLaw.OrderedPrefix

/-!
# Kernel exclusion from an actual ordered-coordinate jump

The uniform witness event excludes every vector and constant shift with
the specified jump simultaneously. It is not a fixed-vector probability
that needs multiplication by a net size.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem steep_unique_witness_exclusion {n d s t : ℕ} (hd : 0 < d)
    (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n) (I : Finset (Fin n))
    (rows : RowSliceMatrix n d) (hWitness : UniformUniqueWitness I s t rows)
    (x : Fin n → ℂ) (c ζ : ℂ)
    (hJump : 4 * (d : ℝ) * orderedNorm x ⟨t - 1, by omega⟩ <
      orderedNorm x ⟨s - 1, by omega⟩)
    (hCenter : ‖c‖ ≤ orderedNorm x ⟨t - 1, by omega⟩ / 10)
    (hSpectral : ‖ζ‖ ≤ (d : ℝ) / 20) :
    (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) ≠ 0 := by
  let L := orderedPrefix x s
  let J := orderedPrefix x t
  let R := J \ L
  have hSub : L ⊆ J := orderedPrefix_subset x hst
  have hUnion : L ∪ R = J := Finset.union_sdiff_of_subset hSub
  have hL : L.card = s := orderedPrefix_card x (by omega : s ≤ n)
  have hJ : J.card = t := orderedPrefix_card x htn
  have hCount := hWitness L R Finset.disjoint_sdiff hL (by rw [hUnion]; exact hJ)
  rw [hUnion] at hCount
  have hPositive : (0 : ℝ) <
      (uniqueWitnessRows L J (fun i : ↥(I \ J) => rows i.val)).card := by
    have hScale : (0 : ℝ) < (d : ℝ) * s / 2 := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hsR : (0 : ℝ) < s := by exact_mod_cast hs
      positivity
    exact hScale.trans_le hCount
  have hNonempty : (uniqueWitnessRows L J (fun i : ↥(I \ J) => rows i.val)).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hPositive)
  obtain ⟨i, hi⟩ := hNonempty
  have hRow : uniqueRowWitness L J (rows i.val) := (Finset.mem_filter.mp hi).2
  obtain ⟨j, hjL, hUnique⟩ := hRow
  have hiJ : i.val ∉ J := (Finset.mem_sdiff.mp i.property).2
  have hAction := unique_witness_action_seven_tenths (rows i.val) J j i.val
    hUnique hiJ x c ζ
    (orderedNorm_nonneg x ⟨t - 1, by omega⟩)
    (fun k hk => norm_notMem_orderedPrefix x (by omega : 0 < t) htn k hk)
    (norm_mem_orderedPrefix x hs (by omega : s ≤ n) j hjL)
    hJump hCenter hSpectral
  intro hZero
  let retainedIndex : I := ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩
  have hAtZero := congrFun hZero retainedIndex
  rw [retainedShiftedMatrix_mulVec] at hAtZero
  change shiftedRowAction (rows i.val) x c ζ i.val = 0 at hAtZero
  have hNorm := hAction.2
  rw [hAtZero, norm_zero] at hNorm
  exact (lt_irrefl 0) hNorm

theorem steep_jump_kernel_probability {n d s t : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (ht : (t : ℝ) ≤ (9 / 100 : ℝ) * n)
    (hLoss : ((d : ℝ) - 1) * ((t : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ) / 20) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ (x : Fin n → ℂ) (c : ℂ),
        4 * (d : ℝ) * orderedNorm x ⟨t - 1, by omega⟩ < orderedNorm x ⟨s - 1, by omega⟩ ∧
        ‖c‖ ≤ orderedNorm x ⟨t - 1, by omega⟩ / 10 ∧
        (retainedShiftedMatrix I ζ rows).mulVec (fun j => x j + c) = 0) ≤
      Real.exp (-uniqueWitnessRate * d * s + (t : ℝ) *
        (Real.log (Real.exp 1 * n / t) + Real.log 2)) := by
  apply (uniformProbability_mono ?_).trans
    (uniform_unique_witness_failure_entropy hn hd hdn (by omega : 0 < t) htn I hI ht hLoss)
  intro rows hEvent hWitness
  obtain ⟨x, c, hJump, hCenter, hKernel⟩ := hEvent
  exact steep_unique_witness_exclusion hd hs hst htn I rows hWitness x c ζ
    hJump hCenter hSpectral hKernel

end CircularLaw
