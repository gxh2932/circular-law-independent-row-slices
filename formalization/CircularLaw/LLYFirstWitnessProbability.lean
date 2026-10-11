import CircularLaw.LLYFirstSteepAction

/-!
# Uniform probability of the actual first-steep witness event

Set-pair entropy is absorbed using the clipped adjacent-rank ratio.
The probability is on the full square row-slice sample, including when
the deterministic retained set omits one row.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lly_small_unique_witness_loss {n d t : ℕ} (hn : 3 ≤ n) (hd : 0 < d)
    (hSmall : 16 * d * t ≤ n) :
    (t : ℝ) ≤ (9 / 100 : ℝ) * n ∧
      ((d : ℝ) - 1) * ((t : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSmallR : (16 : ℝ) * d * t ≤ n := by exact_mod_cast hSmall
  have hT := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg (α := ℝ) t)
  have hNumerator : ((d : ℝ) - 1) * ((t : ℝ) - 1) ≤ (d : ℝ) * t := by
    calc
      _ ≤ ((d : ℝ) - 1) * t := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg t)
  constructor
  · nlinarith
  · apply (div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
    nlinarith

theorem lly_first_pair_entropy_absorbed {n d ℓ s t : ℕ} (hn : 0 < n) (hs : 0 < s)
    (hst : s ≤ t) (hRatio : t ≤ ℓ * s)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d) :
    (t : ℝ) * (Real.log (Real.exp 1 * n / t) + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d * s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have hUpper : Real.exp 1 * n / t ≤ Real.exp 1 * n := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < t)).mpr
    nlinarith [mul_le_mul_of_nonneg_left htR (by positivity : 0 ≤ Real.exp 1 * (n : ℝ))]
  have hLog : Real.log (Real.exp 1 * n / t) + Real.log 2 ≤ 1 + Real.log n + Real.log 2 := by
    have h := Real.log_le_log (by positivity) hUpper
    rw [Real.log_mul (Real.exp_pos 1).ne' hnR.ne', Real.log_exp] at h
    linarith
  have hC : 0 ≤ 1 + Real.log (n : ℝ) + Real.log 2 := by
    have hN := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    have hTwo := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hRatioR : (t : ℝ) ≤ (ℓ : ℝ) * s := by exact_mod_cast hRatio
  calc
    _ ≤ (t : ℝ) * (1 + Real.log n + Real.log 2) :=
      mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg t)
    _ ≤ (ℓ : ℝ) * s * (1 + Real.log n + Real.log 2) :=
      mul_le_mul_of_nonneg_right hRatioR hC
    _ = (s : ℝ) * ((ℓ : ℝ) * (1 + Real.log n + Real.log 2)) := by ring
    _ ≤ (s : ℝ) * ((uniqueWitnessRate / 2) * d) :=
      mul_le_mul_of_nonneg_left hBudget (Nat.cast_nonneg s)
    _ = _ := by ring

theorem lly_first_pair_witness_failure {n d ℓ s t : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * t ≤ n) (hRatio : t ≤ ℓ * s)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬UniformUniqueWitness I s t rows) ≤
      Real.exp (-(uniqueWitnessRate / 2) * d) := by
  have hLoss := lly_small_unique_witness_loss hn hd hSmall
  have hEntropy := lly_first_pair_entropy_absorbed (by omega : 0 < n) hs hst hRatio hBudget
  apply (uniform_unique_witness_failure_entropy (by omega : 2 ≤ n) hd hdn
    (by omega : 0 < t) htn I hI hLoss.1 hLoss.2).trans
  apply Real.exp_le_exp.mpr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hDs : (d : ℝ) ≤ (d : ℝ) * s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsR (Nat.cast_nonneg (α := ℝ) d)
  have hScale := mul_le_mul_of_nonneg_left hDs (le_of_lt uniqueWitnessRate_pos)
  nlinarith

theorem lly_first_witness_failure_probability {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYFirstWitness I ℓ r k rows) ≤
      (r + 1 : ℕ) * Real.exp (-(uniqueWitnessRate / 2) * d) := by
  apply (uniformProbability_mono ?_).trans
    ((uniformProbability_finset_exists_le (Finset.range (r + 1))
      (fun i rows => ¬UniformUniqueWitness I (llyFirstRank ℓ k i)
        (llyFirstRank ℓ k (i + 1)) rows)).trans ?_)
  · intro rows hBad
    unfold LLYFirstWitness at hBad
    push_neg at hBad
    exact hBad
  · calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), Real.exp (-(uniqueWitnessRate / 2) * d) := by
        apply Finset.sum_le_sum
        intro i _
        exact lly_first_pair_witness_failure hn hd hdn (lly_first_rank_pos hℓ hk i)
          (lly_first_rank_mono hℓ (by omega : i ≤ i + 1))
          ((lly_first_rank_le ℓ k (i + 1)).trans hkn) I hI
          ((Nat.mul_le_mul_left (16 * d) (lly_first_rank_le ℓ k (i + 1))).trans hSmall)
          (lly_first_rank_ratio hℓ i) hBudget
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem lly_first_witness_failure_polynomial {n d ℓ r k : ℕ}
    (hn : 3 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 16 * d * k ≤ n)
    (hBudget : (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d)
    (hScales : r + 1 ≤ n) (A : ℝ)
    (hDegree : (2 / uniqueWitnessRate) * (A + 1) * Real.log (n : ℝ) ≤ d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYFirstWitness I ℓ r k rows) ≤
      (n : ℝ) ^ (-A) := by
  apply (lly_first_witness_failure_probability hn hd hdn hℓ hk hkn I hI hSmall hBudget).trans
  have hScalesR : ((r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hScales
  have hExponent : -(uniqueWitnessRate / 2) * (d : ℝ) = -(d : ℝ) / (2 / uniqueWitnessRate) := by
    field_simp
  calc
    _ ≤ (n : ℝ) * Real.exp (-(uniqueWitnessRate / 2) * d) :=
      mul_le_mul_of_nonneg_right hScalesR (Real.exp_pos _).le
    _ = (n : ℝ) * Real.exp (-(d : ℝ) / (2 / uniqueWitnessRate)) := by rw [hExponent]
    _ ≤ _ := dimension_exp_degree_le_rpow (by omega : 0 < n)
      (div_pos (by norm_num) uniqueWitnessRate_pos) hDegree

end CircularLaw
