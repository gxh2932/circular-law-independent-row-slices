import CircularLaw.GridBox
import CircularLaw.SmallSetEntropy
import CircularLaw.OrderedNormStability
import CircularLaw.AlmostConstantGeometry

/-!
# Finite nets with three coordinate ranges

The support, the middle prefix and the high prefix are actual subsets
of coordinates. Each finite family is counted by its coordinate choices;
the global net ranges over every allowed choice of these subsets.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def coordinateGridNet {n : ℕ} (H M S : Finset (Fin n)) (A B C : Finset ℂ) :
    Finset (Fin n → ℂ) :=
  Fintype.piFinset (fun j => if j ∈ S then
    (if j ∈ H then A else if j ∈ M then B else C) else {0})

theorem coordinateGridNet_zero_outside {n : ℕ} (H M S : Finset (Fin n))
    (A B C : Finset ℂ) (u : Fin n → ℂ) (hu : u ∈ coordinateGridNet H M S A B C)
    (j : Fin n) (hj : j ∉ S) : u j = 0 := by
  have h := Fintype.mem_piFinset.mp hu j
  simpa only [if_neg hj, Finset.mem_singleton] using h

theorem coordinateGridNet_card_le {n : ℕ} (H M S : Finset (Fin n)) (A B C : Finset ℂ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    (coordinateGridNet H M S A B C).card ≤ A.card ^ H.card * B.card ^ M.card * C.card ^ S.card := by
  have hAOne : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hBOne : 1 ≤ B.card := Finset.one_le_card.mpr hB
  have hCOne : 1 ≤ C.card := Finset.one_le_card.mpr hC
  unfold coordinateGridNet
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ j : Fin n, ((if j ∈ H then A.card else 1) *
        (if j ∈ M then B.card else 1) * (if j ∈ S then C.card else 1)) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro j _
      split_ifs <;> (try simp) <;> first | assumption |
        nlinarith [Nat.mul_le_mul hAOne hBOne, Nat.mul_le_mul hAOne hCOne,
          Nat.mul_le_mul hBOne hCOne, Nat.mul_le_mul_left A.card hBOne,
          Nat.mul_le_mul_left A.card hCOne, Nat.mul_le_mul_left B.card hCOne,
          Nat.mul_le_mul_left (A.card * B.card) hCOne]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
      simp only [Finset.prod_const]

def threeRangeGridNet (n h m s : ℕ) (A B C : Finset ℂ) : Finset (Fin n → ℂ) :=
  (smallCoordinateSets n h).biUnion (fun H =>
    (smallCoordinateSets n m).biUnion (fun M =>
      (smallCoordinateSets n s).biUnion (fun S => coordinateGridNet H M S A B C)))

theorem mem_threeRangeGridNet {n h m s : ℕ} (A B C : Finset ℂ)
    (u : Fin n → ℂ) : u ∈ threeRangeGridNet n h m s A B C ↔
      ∃ H M S : Finset (Fin n), H.card ≤ h ∧ M.card ≤ m ∧ S.card ≤ s ∧
        u ∈ coordinateGridNet H M S A B C := by
  simp only [threeRangeGridNet, Finset.mem_biUnion, mem_smallCoordinateSets]
  constructor
  · rintro ⟨H, hH, M, hM, S, hS, hu⟩
    exact ⟨H, M, S, hH, hM, hS, hu⟩
  · rintro ⟨H, M, S, hH, hM, hS, hu⟩
    exact ⟨H, hH, M, hM, S, hS, hu⟩

theorem threeRangeGridNet_card_le {n h m s : ℕ} (A B C : Finset ℂ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    (threeRangeGridNet n h m s A B C).card ≤
      (smallCoordinateSets n h).card * (smallCoordinateSets n m).card *
        (smallCoordinateSets n s).card * (A.card ^ h * B.card ^ m * C.card ^ s) := by
  have hBound : ∀ H ∈ smallCoordinateSets n h, ∀ M ∈ smallCoordinateSets n m,
      ∀ S ∈ smallCoordinateSets n s,
        (coordinateGridNet H M S A B C).card ≤ A.card ^ h * B.card ^ m * C.card ^ s := by
    intro H hH M hM S hS
    apply (coordinateGridNet_card_le H M S A B C hA hB hC).trans
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul (Nat.pow_le_pow_right (Finset.card_pos.mpr hA)
        ((mem_smallCoordinateSets H).mp hH))
        (Nat.pow_le_pow_right (Finset.card_pos.mpr hB) ((mem_smallCoordinateSets M).mp hM))
    · exact Nat.pow_le_pow_right (Finset.card_pos.mpr hC) ((mem_smallCoordinateSets S).mp hS)
  unfold threeRangeGridNet
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ H ∈ smallCoordinateSets n h, ∑ M ∈ smallCoordinateSets n m,
        ∑ _S ∈ smallCoordinateSets n s, (A.card ^ h * B.card ^ m * C.card ^ s) := by
      apply Finset.sum_le_sum
      intro H hH
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro M hM
      apply Finset.card_biUnion_le.trans
      exact Finset.sum_le_sum (fun S hS => hBound H hH M hM S hS)
    _ = _ := by simp only [Finset.sum_const, smul_eq_mul]; ring

theorem norm_le_orderedNormAt_notMem_prev_prefix {n t : ℕ} (x : Fin n → ℂ)
    (ht : 0 < t) (htn : t ≤ n) (j : Fin n) (hj : j ∉ orderedPrefix x (t - 1)) :
    ‖x j‖ ≤ orderedNormAt x t := by
  have hRank : (⟨t - 1, by omega⟩ : Fin n) ≤ (normOrderPerm x).symm j := by
    apply Fin.le_iff_val_le_val.mpr
    change t - 1 ≤ ((normOrderPerm x).symm j).val
    have hNot : ¬((normOrderPerm x).symm j).val < t - 1 := fun h =>
      hj ((mem_orderedPrefix x (t - 1) j).mpr h)
    omega
  have h := orderedNorm_antitone x hRank
  rw [orderedNorm_of_rank, ← orderedNormAt_eq x ht htn] at h
  exact h

def truncatedCanonicalApprox {n : ℕ} (k t : ℕ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun j => if j ∈ orderedPrefix x (t - 1) then canonicalApprox k (x j) else 0

theorem truncatedCanonicalApprox_error {n k t : ℕ} {δ : ℝ}
    (hk : 0 < k) (ht : 0 < t) (htn : t ≤ n)
    (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (x : Fin n → ℂ) (hTail : orderedNormAt x t ≤ δ) :
    ∀ j, ‖x j - truncatedCanonicalApprox k t x j‖ ≤ δ := by
  intro j
  by_cases hj : j ∈ orderedPrefix x (t - 1)
  · simp only [truncatedCanonicalApprox, if_pos hj]
    exact (canonicalApprox_norm_error hk (x j)).trans hGrid
  · simp only [truncatedCanonicalApprox, if_neg hj, sub_zero]
    exact (norm_le_orderedNormAt_notMem_prev_prefix x ht htn j hj).trans hTail

theorem truncatedCanonicalApprox_tail_zero {n k t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (x : Fin n → ℂ) : orderedNormAt (truncatedCanonicalApprox k t x) t = 0 := by
  apply le_antisymm _ (orderedNormAt_nonneg _ _)
  let F := (Finset.univ : Finset (Fin n)) \ orderedPrefix x (t - 1)
  have hCount : F.card = n - (t - 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      orderedPrefix_card x (by omega : t - 1 ≤ n)]
  apply orderedNormAt_le_of_many_small ht htn _ 0 F (by rw [hCount]; omega)
  intro j hj
  have hNot := (Finset.mem_sdiff.mp hj).2
  simp only [truncatedCanonicalApprox, if_neg hNot, norm_zero, le_refl]

theorem truncatedCanonicalApprox_mem_threeRangeGridNet {n k h m t : ℕ}
    {RA RB RC : ℝ} (hh : 0 < h) (hm : 0 < m) (ht : 0 < t)
    (hhn : h ≤ n) (hmn : m ≤ n) (htn : t ≤ n)
    (x : Fin n → ℂ) (hHigh : ∀ j, ‖x j‖ ≤ RA)
    (hMiddle : orderedNormAt x h ≤ RB) (hBase : orderedNormAt x m ≤ RC) :
    truncatedCanonicalApprox k t x ∈ threeRangeGridNet n (h - 1) (m - 1) (t - 1)
      (gridBox k (gridBoxRadius k RA)) (gridBox k (gridBoxRadius k RB))
        (gridBox k (gridBoxRadius k RC)) := by
  apply (mem_threeRangeGridNet _ _ _ _).mpr
  refine ⟨orderedPrefix x (h - 1), orderedPrefix x (m - 1), orderedPrefix x (t - 1),
    ?_, ?_, ?_, ?_⟩
  · exact (orderedPrefix_card x (by omega : h - 1 ≤ n)).le
  · exact (orderedPrefix_card x (by omega : m - 1 ≤ n)).le
  · exact (orderedPrefix_card x (by omega : t - 1 ≤ n)).le
  · apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hS : j ∈ orderedPrefix x (t - 1)
    · simp only [truncatedCanonicalApprox, if_pos hS]
      by_cases hH : j ∈ orderedPrefix x (h - 1)
      · simp only [if_pos hH]
        exact canonicalApprox_mem_gridBox (x j) (hHigh j)
      · simp only [if_neg hH]
        by_cases hM : j ∈ orderedPrefix x (m - 1)
        · simp only [if_pos hM]
          exact canonicalApprox_mem_gridBox (x j)
            ((norm_le_orderedNormAt_notMem_prev_prefix x hh hhn j hH).trans hMiddle)
        · simp only [if_neg hM]
          exact canonicalApprox_mem_gridBox (x j)
            ((norm_le_orderedNormAt_notMem_prev_prefix x hm hmn j hM).trans hBase)
    · simp only [truncatedCanonicalApprox, if_neg hS, Finset.mem_singleton]

end CircularLaw
