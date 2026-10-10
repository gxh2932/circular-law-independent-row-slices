import CircularLaw.UniformWitnessFailure

/-!
# The source equal-block entropy and its absorption

Combining the two logarithms gives exactly the Section 4 form
`exp(-c*d*s + 2*s*log(e*n/s))`. Restriction identifies the same event
under the full matrix law when only the retained rows are counted.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem uniform_equal_block_failure_source_entropy {n d s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hs : 0 < s) (hRows : (n : ℝ) / 2 ≤ Fintype.card ι) (hSmall : 100 * d * s ≤ n)
    {cw : ℝ} (hcw : cw ≤ 1 / 4) :
    uniformProbability (fun rows : ι → RowSlice n d => ¬UniformEqualBlockWitness cw s rows) ≤
      Real.exp (-(binomialHalfRate / 2) * d * s + 2 * (s : ℝ) *
        Real.log (Real.exp 1 * n / s)) := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsPos : (0 : ℝ) < s := by exact_mod_cast hs
  have hRatio : (0 : ℝ) < Real.exp 1 * n / (2 * s : ℕ) := by positivity
  have hLog : Real.log (Real.exp 1 * n / (2 * s : ℕ)) + Real.log 2 =
      Real.log (Real.exp 1 * n / s) := by
    rw [← Real.log_mul hRatio.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    field_simp
  have h := uniform_equal_block_failure_entropy hn hd hdn hs hRows hSmall hcw
  rw [hLog] at h
  convert h using 1
  congr 1
  push_cast
  ring

theorem uniform_equal_block_failure_absorbed {n d s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hs : 0 < s) (hRows : (n : ℝ) / 2 ≤ Fintype.card ι) (hSmall : 100 * d * s ≤ n)
    {cw : ℝ} (hcw : cw ≤ 1 / 4)
    (hEntropy : 8 * Real.log (Real.exp 1 * n / s) ≤ binomialHalfRate * d) :
    uniformProbability (fun rows : ι → RowSlice n d => ¬UniformEqualBlockWitness cw s rows) ≤
      Real.exp (-(binomialHalfRate / 4) * d * s) := by
  apply (uniform_equal_block_failure_source_entropy hn hd hdn hs hRows hSmall hcw).trans
  apply Real.exp_le_exp.mpr
  have hScaled := mul_le_mul_of_nonneg_right hEntropy (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  nlinarith

theorem retained_equal_block_failure_source_entropy {n d s : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hs : 0 < s) (I : Finset (Fin n))
    (hRows : (n : ℝ) / 2 ≤ I.card) (hSmall : 100 * d * s ≤ n)
    {cw : ℝ} (hcw : cw ≤ 1 / 4) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬UniformEqualBlockWitness cw s (fun i : I => rows i.val)) ≤
        Real.exp (-(binomialHalfRate / 2) * d * s + 2 * (s : ℝ) *
          Real.log (Real.exp 1 * n / s)) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun retained => ¬UniformEqualBlockWitness cw s retained)]
  exact uniform_equal_block_failure_source_entropy hn hd hdn hs
    (by simpa only [Fintype.card_coe] using hRows) hSmall hcw

end CircularLaw
