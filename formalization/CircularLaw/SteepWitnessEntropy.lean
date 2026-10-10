import CircularLaw.SteepScales
import CircularLaw.UniqueWitnessFailure

/-!
# Entropy absorption for the steep witness pairs

The smallest source jump size gives `d*s >= 10*n/d^3`. The stride and
degree bounds absorb the exact set-pair entropy into the witness rate.
Only deterministic scale inequalities remain in this finite estimate.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem small_unique_witness_loss {n d t : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (hSmall : 100 * d * t ≤ n) :
    (t : ℝ) ≤ (9 / 100 : ℝ) * n ∧
      ((d : ℝ) - 1) * ((t : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSmallR : (100 : ℝ) * d * t ≤ n := by exact_mod_cast hSmall
  have hT := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  have hNumerator : ((d : ℝ) - 1) * ((t : ℝ) - 1) ≤ (d : ℝ) * t := by
    calc
      _ ≤ ((d : ℝ) - 1) * t :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg t)
  constructor
  · nlinarith
  · apply (div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
    nlinarith

theorem steep_pair_entropy_absorbed {n d p s t : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hs : 0 < s) (hst : s ≤ t) (hStride : (p : ℝ) ≤ Real.sqrt d / 5)
    (hRatio : t ≤ p * s) (hDensity : 10 * (n : ℝ) / (d : ℝ) ^ 3 ≤ (d : ℝ) * s)
    (hDegree : Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d) :
    (t : ℝ) * (Real.log (Real.exp 1 * n / t) + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d * s := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hDensityMul := (div_le_iff₀ (pow_pos hdR 3)).mp hDensity
  have hOrder : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hOrderScaled := mul_le_mul_of_nonneg_left hOrder (pow_nonneg hdR.le 4)
  have hN : (n : ℝ) ≤ (d : ℝ) ^ 4 * t := by
    have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hRatioUpper : Real.exp 1 * n / t ≤ Real.exp 1 * (d : ℝ) ^ 4 := by
    apply (div_le_iff₀ htR).mpr
    have hScaled := mul_le_mul_of_nonneg_left hN (Real.exp_pos 1).le
    nlinarith
  have hLog : Real.log (Real.exp 1 * n / t) + Real.log 2 ≤
      1 + 4 * Real.log d + Real.log 2 := by
    have h := Real.log_le_log (by positivity) hRatioUpper
    rw [Real.log_mul (Real.exp_pos 1).ne' (pow_pos hdR 4).ne', Real.log_exp,
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hLogD : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hC : 0 ≤ 1 + 4 * Real.log d + Real.log 2 := by
    have hLogTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hRatioR : (t : ℝ) ≤ (p : ℝ) * s := by exact_mod_cast hRatio
  calc
    _ ≤ (t : ℝ) * (1 + 4 * Real.log d + Real.log 2) :=
      mul_le_mul_of_nonneg_left hLog htR.le
    _ ≤ (p : ℝ) * s * (1 + 4 * Real.log d + Real.log 2) :=
      mul_le_mul_of_nonneg_right hRatioR hC
    _ = (p : ℝ) * ((s : ℝ) * (1 + 4 * Real.log d + Real.log 2)) := by ring
    _ ≤ (Real.sqrt d / 5) * ((s : ℝ) * (1 + 4 * Real.log d + Real.log 2)) :=
      mul_le_mul_of_nonneg_right hStride (mul_nonneg (Nat.cast_nonneg s) hC)
    _ = (s : ℝ) * (Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2)) := by ring
    _ ≤ (s : ℝ) * ((uniqueWitnessRate / 2) * d) :=
      mul_le_mul_of_nonneg_left hDegree (Nat.cast_nonneg s)
    _ = _ := by ring

theorem steep_pair_witness_failure {n d p s t : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hs : 0 < s) (hst : s ≤ t)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card)
    (hSmall : 100 * d * t ≤ n) (hStride : (p : ℝ) ≤ Real.sqrt d / 5)
    (hRatio : t ≤ p * s) (hDensity : 10 * (n : ℝ) / (d : ℝ) ^ 3 ≤ (d : ℝ) * s)
    (hDegree : Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬UniformUniqueWitness I s t rows) ≤
      Real.exp (-5 * uniqueWitnessRate * n / (d : ℝ) ^ 3) := by
  have hLoss := small_unique_witness_loss hn hd hSmall
  have htn : t ≤ n := by nlinarith
  have hEntropy := steep_pair_entropy_absorbed (by omega : 0 < n) hd hs hst
    hStride hRatio hDensity hDegree
  apply (uniform_unique_witness_failure_entropy hn hd hdn (by omega : 0 < t) htn
    I hI hLoss.1 hLoss.2).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ -(uniqueWitnessRate / 2) * ((d : ℝ) * s) := by nlinarith
    _ ≤ -(uniqueWitnessRate / 2) * (10 * (n : ℝ) / (d : ℝ) ^ 3) :=
      mul_le_mul_of_nonpos_left hDensity (by nlinarith [uniqueWitnessRate_pos])
    _ = _ := by ring

theorem steep_witness_failure_union {n d p : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (I : Finset (Fin n)) (hI : (99 / 100 : ℝ) * n ≤ I.card) (A : Finset (ℕ × ℕ))
    (hStride : (p : ℝ) ≤ Real.sqrt d / 5)
    (hDegree : Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d)
    (hScales : ∀ a ∈ A, 0 < a.1 ∧ a.1 ≤ a.2 ∧ 100 * d * a.2 ≤ n ∧
      a.2 ≤ p * a.1 ∧ 10 * (n : ℝ) / (d : ℝ) ^ 3 ≤ (d : ℝ) * a.1) :
    uniformProbability (fun rows : RowSliceMatrix n d => ∃ a ∈ A,
      ¬UniformUniqueWitness I a.1 a.2 rows) ≤
        (A.card : ℝ) * Real.exp (-5 * uniqueWitnessRate * n / (d : ℝ) ^ 3) := by
  apply (uniformProbability_finset_exists_le A
    (fun a rows => ¬UniformUniqueWitness I a.1 a.2 rows)).trans
  calc
    _ ≤ ∑ _a ∈ A, Real.exp (-5 * uniqueWitnessRate * n / (d : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hs, hst, hSmall, hRatio, hDensity⟩ := hScales a ha
      exact steep_pair_witness_failure hn hd hdn hs hst I hI hSmall hStride hRatio hDensity hDegree
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end CircularLaw
