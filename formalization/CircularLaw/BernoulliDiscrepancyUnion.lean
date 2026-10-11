import CircularLaw.BernoulliMatrixDiscrepancy

/-!
# Simultaneous discrepancy under the actual Bernoulli square law

The actual fixed-cardinality set families pay their binomial entropy.
Summing the fixed-set logarithmic tail supplies every prescribed inverse
power with no assumed discrepancy event.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def BernoulliSizedMatrixDiscrepancyBad {n : ℕ} (d : ℕ) (beta : ℝ) (k l : ℕ)
    (sample : BernoulliSquareSample n) : Prop :=
  ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    ∃ T ∈ (Finset.univ : Finset (Fin n)).powersetCard l,
      BernoulliMatrixDiscrepancyBad d beta S T sample

theorem bernoulli_matrix_discrepancy_fixed_sizes_probability {n d k l : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk : 0 < k) (hkn : k ≤ n) (hl : 0 < l) (hln : l ≤ n) (beta : ℝ) :
    (sparseBernoulliMatrixLaw n d).real {sample | BernoulliSizedMatrixDiscrepancyBad d beta k l sample} ≤
      Real.exp (-(beta + 2) * edgeSetEntropy n (max k l)) := by
  let μ := sparseBernoulliMatrixLaw n d
  let A := (Finset.univ : Finset (Fin n)).powersetCard k
  let B := (Finset.univ : Finset (Fin n)).powersetCard l
  have hPoint (S : Finset (Fin n)) (hS : S ∈ A) (T : Finset (Fin n)) (hT : T ∈ B) :
      μ.real {sample | BernoulliMatrixDiscrepancyBad d beta S T sample} ≤
        Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) := by
    have hSCard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hTCard : T.card = l := (Finset.mem_powersetCard.mp hT).2
    have hSNon : S.Nonempty := Finset.card_pos.mp (by omega)
    have hTNon : T.Nonempty := Finset.card_pos.mp (by omega)
    have h := bernoulli_matrix_discrepancy_fixed_sets_probability hn hd hdn beta S T hSNon hTNon
    simpa only [hSCard, hTCard] using h
  unfold BernoulliSizedMatrixDiscrepancyBad
  apply (finite_measure_finset_exists_le μ A
    (fun S (sample : BernoulliSquareSample n) => ∃ T ∈ B, BernoulliMatrixDiscrepancyBad d beta S T sample)).trans
  calc
    _ ≤ ∑ S ∈ A, ∑ T ∈ B, μ.real {sample | BernoulliMatrixDiscrepancyBad d beta S T sample} := by
      apply Finset.sum_le_sum
      intro S _
      exact finite_measure_finset_exists_le μ B (fun T sample => BernoulliMatrixDiscrepancyBad d beta S T sample)
    _ ≤ ∑ _S ∈ A, ∑ _T ∈ B, Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      exact hPoint S hS T hT
    _ = (n.choose k : ℝ) * (n.choose l : ℝ) * Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) := by
      simp [A, B, mul_assoc]
    _ ≤ Real.exp (2 * edgeSetEntropy n (max k l)) *
        Real.exp (-(beta + 4) * edgeSetEntropy n (max k l)) :=
      mul_le_mul_of_nonneg_right (choose_rectangular_entropy hn (le_refl n) hk hkn hl hln) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem bernoulli_matrix_discrepancy_failure_size_cover {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (beta : ℝ) (sample : BernoulliSquareSample n)
    (hFail : ¬MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4)) (bernoulliSquareMatrixReal sample)) :
    ∃ k ∈ Finset.Icc 1 n, ∃ l ∈ Finset.Icc 1 n, BernoulliSizedMatrixDiscrepancyBad d beta k l sample := by
  obtain ⟨S, T, hS, hT, hBad⟩ := (bernoulli_matrix_discrepancy_failure_iff hn hd beta sample).mp hFail
  have hSn : S.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hTn : T.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  refine ⟨S.card, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hS.card_pos, hSn⟩,
    T.card, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hT.card_pos, hTn⟩, S, ?_, T, ?_, hBad⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, rfl⟩

theorem bernoulli_matrix_discrepancy_all_sizes_probability {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) {beta : ℝ} (hBeta : 0 ≤ beta) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4)) (bernoulliSquareMatrixReal sample)} ≤
        (n : ℝ) * n * Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
  let μ := sparseBernoulliMatrixLaw n d
  have hPoint (k : ℕ) (hk : k ∈ Finset.Icc 1 n) (l : ℕ) (hl : l ∈ Finset.Icc 1 n) :
      μ.real {sample | BernoulliSizedMatrixDiscrepancyBad d beta k l sample} ≤
        Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
    obtain ⟨hkOne, hkn⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hlOne, hln⟩ := Finset.mem_Icc.mp hl
    apply (bernoulli_matrix_discrepancy_fixed_sizes_probability hn hd hdn (by omega) hkn (by omega) hln beta).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (edgeSetEntropy_log_lower (by omega : 0 < max k l) (max_le hkn hln)) (by linarith)
  apply (measureReal_mono (μ := μ) (fun sample hFail =>
    bernoulli_matrix_discrepancy_failure_size_cover hn hd beta sample hFail) (h₂ := by finiteness)).trans
  apply (finite_measure_finset_exists_le μ (Finset.Icc 1 n)
    (fun k (sample : BernoulliSquareSample n) => ∃ l ∈ Finset.Icc 1 n, BernoulliSizedMatrixDiscrepancyBad d beta k l sample)).trans
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Icc 1 n,
        μ.real {sample | BernoulliSizedMatrixDiscrepancyBad d beta k l sample} := by
      apply Finset.sum_le_sum
      intro k _
      exact finite_measure_finset_exists_le μ (Finset.Icc 1 n)
        (fun l (sample : BernoulliSquareSample n) => BernoulliSizedMatrixDiscrepancyBad d beta k l sample)
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, ∑ _l ∈ Finset.Icc 1 n,
        Real.exp (-(beta + 2) * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact hPoint k hk l hl
    _ = _ := by simp [mul_assoc]

theorem bernoulli_matrix_discrepancy_failure_probability {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) {beta : ℝ} (hBeta : 0 ≤ beta) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4)) (bernoulliSquareMatrixReal sample)} ≤
        (n : ℝ) ^ (-beta) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSquare : (n : ℝ) ^ 2 = Real.exp (2 * Real.log (n : ℝ)) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hnR] using (Real.exp_nat_mul (Real.log (n : ℝ)) 2).symm
  apply (bernoulli_matrix_discrepancy_all_sizes_probability hn hd hdn hBeta).trans_eq
  rw [← pow_two, hSquare, ← Real.exp_add, Real.rpow_def_of_pos hnR]
  congr 1
  ring

end CircularLaw
