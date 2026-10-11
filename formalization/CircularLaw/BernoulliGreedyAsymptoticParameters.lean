import CircularLaw.BernoulliGreedyPaperPrefix

/-!
# Eventual actual Bernoulli parameters for the finite greedy estimate

The probability is the literal d/n. At any fixed nonzero normalized shift,
the raw diagonal shift z*sqrt(d) eventually lies between a fixed positive
beta and d. These are deductions from the degree hypotheses.
-/

noncomputable section
open Classical Filter
open scoped Topology NNReal

namespace CircularLaw

theorem source_raw_bernoulli_shift_norm (d : ℕ) (z : ℂ) :
    ‖sourceRawBernoulliShift d z‖ = ‖z‖ * Real.sqrt (d : ℝ) := by
  simp only [sourceRawBernoulliShift, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

theorem bernoulli_greedy_shift_beta_pos {z : ℂ} (hz : z ≠ 0) : 0 < min (1 : ℝ) ‖z‖ :=
  lt_min zero_lt_one (norm_pos_iff.mpr hz)

theorem bernoulli_greedy_shift_range_eventually (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) :
    ∀ᶠ n in atTop, min (1 : ℝ) ‖z‖ ≤ ‖sourceRawBernoulliShift (d n) z‖ ∧
      ‖sourceRawBernoulliShift (d n) z‖ ≤ d n := by
  have hReal : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hRoot := Real.tendsto_sqrt_atTop.comp hReal
  filter_upwards [hRoot.eventually_ge_atTop 1, hRoot.eventually_ge_atTop ‖z‖] with n hn hnZ
  change 1 ≤ Real.sqrt (d n : ℝ) at hn
  change ‖z‖ ≤ Real.sqrt (d n : ℝ) at hnZ
  rw [source_raw_bernoulli_shift_norm]
  constructor
  · exact (min_le_right _ _).trans (by nlinarith [norm_nonneg z])
  · have hSquare := Real.sq_sqrt (Nat.cast_nonneg (d n) : (0 : ℝ) ≤ d n)
    nlinarith [Real.sqrt_nonneg (d n)]

theorem sparse_bernoulli_greedy_probability_parameters_eventually
    (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) :
    ∀ᶠ n in atTop, 0 < n ∧ 0 < d n ∧ d n ≤ n ∧
      0 < (rowBernoulliParameter n (d n) : ℝ) ∧
      (rowBernoulliParameter n (d n) : ℝ) ≤ 1 / 2 ∧
      (d n : ℝ) = (n : ℝ) * rowBernoulliParameter n (d n) ∧
      Real.exp 1024 ≤ (d n : ℝ) := by
  have hReal : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  filter_upwards [eventually_gt_atTop 0, hDegree.eventually_ge_atTop 1,
    hSparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hReal.eventually_ge_atTop (Real.exp 1024)] with n hn hd hHalf hLarge
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hdPos : 0 < d n := by omega
  have hdN : d n ≤ n := by
    have hRatio : (d n : ℝ) / n ≤ 1 := by linarith
    exact_mod_cast (div_le_one hnReal).mp hRatio
  refine ⟨hn, hdPos, hdN, ?_, ?_, ?_, hLarge⟩
  · rw [rowBernoulliParameter_coe]
    exact div_pos (by exact_mod_cast hdPos) hnReal
  · rw [rowBernoulliParameter_coe]
    exact hHalf.le
  · rw [rowBernoulliParameter_coe]
    field_simp

end CircularLaw
