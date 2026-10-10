import CircularLaw.RowSliceDiscrepancy

/-!
# Simultaneous discrepancy union bounds

Both set families are the actual fixed-cardinality subsets. Their
binomial counts are charged to the logarithmic tail before summing
over the possible sizes.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceSizedDiscrepancyBad {m n d : ℕ} (beta : ℝ) (k l : ℕ)
    (rows : Fin m → RowSlice n d) : Prop :=
  ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    ∃ T ∈ (Finset.univ : Finset (Fin n)).powersetCard l,
      rowSliceDiscrepancyBad beta S T rows

theorem rowSliceDiscrepancy_fixed_sizes_probability {m n d k l : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hk : 0 < k) (hkm : k ≤ m) (hl : 0 < l) (hln : l ≤ n) (beta : ℝ) :
    uniformProbability (rowSliceSizedDiscrepancyBad (m := m) (n := n) (d := d) beta k l) ≤
      Real.exp (-(beta + 2) * edgeSetEntropy n (max k l)) := by
  let A := (Finset.univ : Finset (Fin m)).powersetCard k
  let B := (Finset.univ : Finset (Fin n)).powersetCard l
  have hPoint (S : Finset (Fin m)) (hS : S ∈ A) (T : Finset (Fin n)) (hT : T ∈ B) :
      uniformProbability (rowSliceDiscrepancyBad (d := d) beta S T) ≤
        Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) := by
    have hSCard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hTCard : T.card = l := (Finset.mem_powersetCard.mp hT).2
    have hSNon : S.Nonempty := Finset.card_pos.mp (by omega)
    have hTNon : T.Nonempty := Finset.card_pos.mp (by omega)
    have h := rowSliceDiscrepancy_fixed_sets_probability hn hd hdn beta S T hSNon hTNon
    simpa only [hSCard, hTCard] using h
  unfold rowSliceSizedDiscrepancyBad
  apply (uniformProbability_finset_exists_le A
    (fun S (rows : Fin m → RowSlice n d) => ∃ T ∈ B, rowSliceDiscrepancyBad beta S T rows)).trans
  calc
    _ ≤ ∑ S ∈ A, ∑ T ∈ B, uniformProbability (rowSliceDiscrepancyBad (d := d) beta S T) := by
      apply Finset.sum_le_sum
      intro S _
      exact uniformProbability_finset_exists_le B (fun T rows => rowSliceDiscrepancyBad beta S T rows)
    _ ≤ ∑ _S ∈ A, ∑ _T ∈ B, Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      exact hPoint S hS T hT
    _ = (m.choose k : ℝ) * (n.choose l : ℝ) * Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) := by
      simp [A, B, mul_assoc]
    _ ≤ Real.exp (2 * edgeSetEntropy n (max k l)) *
        Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) :=
      mul_le_mul_of_nonneg_right (choose_rectangular_entropy hn hmn hk hkm hl hln) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem rowSliceDiscrepancy_failure_size_cover {m n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (beta : ℝ) (rows : Fin m → RowSlice n d)
    (hFail : ¬RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows) :
    ∃ k ∈ Finset.Icc 1 m, ∃ l ∈ Finset.Icc 1 n, rowSliceSizedDiscrepancyBad beta k l rows := by
  obtain ⟨S, T, hS, hT, hBad⟩ := (rowSliceDiscrepancy_failure_iff hn hd beta rows).mp hFail
  have hSm : S.card ≤ m := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hTn : T.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  refine ⟨S.card, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hS.card_pos, hSm⟩,
    T.card, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hT.card_pos, hTn⟩, S, ?_, T, ?_, hBad⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, rfl⟩

theorem rowSliceDiscrepancy_all_sizes_probability {m n d : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {beta : ℝ} (hBeta : 0 ≤ beta) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      ¬RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows) ≤
        (m : ℝ) * n * Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
  have hPoint (k : ℕ) (hk : k ∈ Finset.Icc 1 m) (l : ℕ) (hl : l ∈ Finset.Icc 1 n) :
      uniformProbability (rowSliceSizedDiscrepancyBad (m := m) (n := n) (d := d) beta k l) ≤
        Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
    obtain ⟨hkOne, hkm⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hlOne, hln⟩ := Finset.mem_Icc.mp hl
    apply (rowSliceDiscrepancy_fixed_sizes_probability hn hmn hd hdn (by omega) hkm (by omega) hln beta).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (edgeSetEntropy_log_lower (by omega : 0 < max k l) (max_le (hkm.trans hmn) hln)) (by linarith)
  apply (uniformProbability_mono (fun rows hFail =>
    rowSliceDiscrepancy_failure_size_cover hn hd beta rows hFail)).trans
  apply (uniformProbability_finset_exists_le (Finset.Icc 1 m)
    (fun k (rows : Fin m → RowSlice n d) => ∃ l ∈ Finset.Icc 1 n, rowSliceSizedDiscrepancyBad beta k l rows)).trans
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 m, ∑ l ∈ Finset.Icc 1 n,
        uniformProbability (rowSliceSizedDiscrepancyBad (m := m) (n := n) (d := d) beta k l) := by
      apply Finset.sum_le_sum
      intro k _
      exact uniformProbability_finset_exists_le (Finset.Icc 1 n)
        (fun l (rows : Fin m → RowSlice n d) => rowSliceSizedDiscrepancyBad beta k l rows)
    _ ≤ ∑ _k ∈ Finset.Icc 1 m, ∑ _l ∈ Finset.Icc 1 n,
        Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact hPoint k hk l hl
    _ = _ := by simp [mul_assoc]

theorem rowSliceDiscrepancy_failure_probability {m n d : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {beta : ℝ} (hBeta : 0 ≤ beta) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      ¬RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows) ≤ (n : ℝ) ^ (-beta) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hCount := mul_le_mul_of_nonneg_right hmnR hnR.le
  have hSquare : (n : ℝ) ^ 2 = Real.exp (2 * Real.log (n : ℝ)) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hnR] using (Real.exp_nat_mul (Real.log (n : ℝ)) 2).symm
  apply (rowSliceDiscrepancy_all_sizes_probability hn hmn hd hdn hBeta).trans
  calc
    _ ≤ (n : ℝ) ^ 2 * Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
      simpa only [← pow_two] using mul_le_mul_of_nonneg_right hCount
        (Real.exp_nonneg (-(beta + 2) * Real.log (n : ℝ)))
    _ = (n : ℝ) ^ (-beta) := by
      rw [hSquare, ← Real.exp_add, Real.rpow_def_of_pos hnR]
      congr 1
      ring

theorem rowSliceDiscrepancy_good_probability {m n d : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {beta : ℝ} (hBeta : 0 ≤ beta) :
    1 - (n : ℝ) ^ (-beta) ≤ uniformProbability
      (RowSliceDiscrepancy (m := m) (n := n) (d := d) (Real.exp 2) (2 * (beta + 4))) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  let E := RowSliceDiscrepancy (m := m) (n := n) (d := d) (Real.exp 2) (2 * (beta + 4))
  have hPoint : (fun rows : Fin m → RowSlice n d =>
      (if E rows then (1 : ℝ) else 0) + (if ¬E rows then (1 : ℝ) else 0)) = fun _ => 1 := by
    funext rows
    by_cases h : E rows <;> simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false] <;> norm_num
  have hTotal := congrArg finiteMean hPoint
  rw [finiteMean_add, finiteMean_indicator, finiteMean_indicator, finiteMean_const] at hTotal
  have hFail := rowSliceDiscrepancy_failure_probability hn hmn hd hdn hBeta
  change 1 - (n : ℝ) ^ (-beta) ≤ uniformProbability E
  change uniformProbability (fun rows => ¬E rows) ≤ (n : ℝ) ^ (-beta) at hFail
  linarith only [hTotal, hFail]

end CircularLaw
