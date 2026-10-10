import CircularLaw.LLYUniqueColumnWitness
import CircularLaw.LLYFirstSteepGeometry

/-!
# Uniform column witnesses at all first-steep ranks

Each clipped rank has an actual out-expansion estimate. Its expansion
deficit and diagonal deletion give simultaneous unique witnesses for
every nested prefix pair, with all stride budgets explicit.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def LLYFirstColumnWitness {n d : ℕ} (ℓ r k : ℕ) (rows : RowSliceMatrix n d) : Prop :=
  ∀ i ∈ Finset.range (r + 1),
    UniformUniqueColumnWitness (llyFirstRank ℓ k i) (llyFirstRank ℓ k (i + 1)) rows

theorem unique_column_witness_stride_budgets {ℓ s t d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hRatio : t ≤ ℓ * s) (hError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4) :
    ε * t ≤ (s : ℝ) / 8 ∧ (t : ℝ) ≤ (d : ℝ) * s / 4 := by
  have hRatioR : (t : ℝ) ≤ (ℓ : ℝ) * s := by exact_mod_cast hRatio
  have hErrorScaled := mul_le_mul_of_nonneg_right hError (Nat.cast_nonneg (α := ℝ) s)
  have hEpsScaled := mul_le_mul_of_nonneg_left hRatioR hε
  have hStrideScaled := mul_le_mul_of_nonneg_right hStride (Nat.cast_nonneg (α := ℝ) s)
  constructor <;> nlinarith only [hRatioR, hErrorScaled, hEpsScaled, hStrideScaled]

theorem out_expansion_entropy_of_log_budget {n k d : ℕ} (hn : 0 < n) (hk : 0 < k) {ε : ℝ}
    (hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d) :
    16 * Real.log (Real.exp 1 * n / k) ≤ ε ^ 2 * d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hUpper : Real.exp 1 * n / k ≤ Real.exp 1 * n := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < k)).mpr
    have h := mul_le_mul_of_nonneg_left hkR (by positivity : 0 ≤ Real.exp 1 * (n : ℝ))
    nlinarith only [h]
  have hLog := Real.log_le_log (by positivity) hUpper
  rw [Real.log_mul (Real.exp_pos 1).ne' hnR.ne', Real.log_exp] at hLog
  linarith only [hLog, hBudget]

theorem lly_first_column_witness_failure_probability {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k ≤ ε * n)
    (hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYFirstColumnWitness ℓ r k rows) ≤
      (r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) := by
  let E := fun i : ℕ => fun rows : RowSliceMatrix n d =>
    ¬RowSliceOutExpansion (llyFirstRank ℓ k (i + 1)) ε rows
  apply (uniformProbability_mono ?_).trans
    ((uniformProbability_finset_exists_le (Finset.range (r + 1)) E).trans ?_)
  · intro rows hBad
    by_contra hNone
    push_neg at hNone
    apply hBad
    intro i hi
    have hBudgets := unique_column_witness_stride_budgets hε (lly_first_rank_ratio (k := k) hℓ i) hError hStride
    exact uniform_unique_column_witness_of_expansion rows (not_not.mp (hNone i hi)) hBudgets.1 hBudgets.2
  · calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), Real.exp (-ε ^ 2 * (d : ℝ) / 16) := by
        apply Finset.sum_le_sum
        intro i _
        have ht := lly_first_rank_pos hℓ hk (i + 1)
        have htn := (lly_first_rank_le ℓ k (i + 1)).trans hkn
        have hRank : (llyFirstRank ℓ k (i + 1) : ℝ) ≤ k := by exact_mod_cast lly_first_rank_le ℓ k (i + 1)
        apply (row_slice_out_expansion_failure_absorbed hn hd ht htn hε
          ((mul_le_mul_of_nonneg_left hRank (Nat.cast_nonneg d)).trans hSize)
          (out_expansion_entropy_of_log_budget hn ht hBudget)).trans
        apply Real.exp_le_exp.mpr
        have htR : (1 : ℝ) ≤ llyFirstRank ℓ k (i + 1) := by exact_mod_cast ht
        have h := mul_le_mul_of_nonneg_right htR (by positivity : 0 ≤ ε ^ 2 * (d : ℝ))
        nlinarith only [h]
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end CircularLaw
