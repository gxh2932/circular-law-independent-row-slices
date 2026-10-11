import CircularLaw.ParameterBernoulliWordMeans

/-!
# Actual all-word mean limits for varying Bernoulli parameters

Dimensions may be any growing sequence. Entry probabilities tend to zero,
and the real effective degrees tend to infinity. The actual centered word
means, normalized by those degrees, have exactly the Gaussian word limits.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

local instance parameterBernoulliMeanBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

theorem parameter_bernoulli_even_pattern_tendsto {k m : ℕ} (q : ℕ → ℕ)
    (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0))
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m) :
    Tendsto (fun n => parameterBernoulliPatternContribution (q n) (p n) (hp n) b s)
      atTop (𝓝 (if BernoulliLeadingPattern b s then 1 else 0)) := by
  by_cases hLeading : BernoulliLeadingPattern b s
  · rw [if_pos hLeading]
    have hE : bernoulliPatternEntryCount b s = m := by
      have h := hLeading.2.2
      omega
    have hV : bernoulliPatternVertexCount s = m + 1 := hLeading.2.1.trans (by rw [hE])
    have hBudget : Tendsto (fun n => sparseRealEvenPatternBudget (q n)
        (bernoulliPatternVertexCount s) m m (bernoulliEffectiveDegree (q n) (p n)))
        atTop (𝓝 1) := by
      simpa only [hV, eq_self_iff_true, and_self, if_true] using
        sparse_real_even_pattern_budget_tendsto q _ hQ hDegree _ m m hV.le le_rfl
    have hFactor : Tendsto (fun n => (1 - (p n : ℝ)) ^ m) atTop (𝓝 1) := by
      simpa only [sub_zero, one_pow] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hSparse).pow m
    have h := hBudget.mul hFactor
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [hQ.eventually_gt_atTop 0, hDegree.eventually_gt_atTop 0] with n hn hd
    exact (parameter_bernoulli_even_leading_pattern_formula hn (p n) (hp n) hd
      b s hLength hLeading).symm
  · rw [if_neg hLeading]
    by_cases hSurvive : BernoulliSurvivingPattern b s
    · have hV := bernoulli_pattern_vertex_bound b s
      have hE : bernoulliPatternEntryCount b s ≤ m := by
        have h := bernoulli_pattern_surviving_entry_bound b s hSurvive
        omega
      have hNonleading : ¬ (bernoulliPatternVertexCount s =
          bernoulliPatternEntryCount b s + 1 ∧ bernoulliPatternEntryCount b s = m) := by
        rintro ⟨h1, h2⟩
        exact hLeading ⟨hSurvive, h1, by omega⟩
      have hBudget := sparse_real_even_nonleading_budget_tendsto_zero q _ hQ hDegree
        _ _ m hV hE hNonleading
      have hAbs : Tendsto
          (fun n => |parameterBernoulliPatternContribution (q n) (p n) (hp n) b s|)
          atTop (𝓝 0) := by
        apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hBudget
        filter_upwards [hQ.eventually_gt_atTop 0, hDegree.eventually_gt_atTop 0] with n hn hd
        exact parameter_bernoulli_even_pattern_abs_bound hn (p n) (hp n) hd b s hLength hSurvive
      exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hAbs)
    · simpa only [parameter_bernoulli_nonsurviving_pattern_zero _ _ _ b s hSurvive] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem parameter_bernoulli_odd_pattern_abs_bound {n k m : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) (hD : 1 ≤ bernoulliEffectiveDegree n p)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hLength : k + 1 = 2 * m + 1) (hSurvive : BernoulliSurvivingPattern b s) :
    |parameterBernoulliPatternContribution n p hp b s| ≤
      (Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ := by
  have hE : bernoulliPatternEntryCount b s ≤ m := by
    have h := bernoulli_pattern_surviving_entry_bound b s hSurvive
    omega
  have hV := bernoulli_pattern_vertex_bound b s
  have hBudget := sparse_real_even_pattern_budget_le_one hn hD hV hE
  have hDPos : 0 < bernoulliEffectiveDegree n p := by linarith
  calc
    _ ≤ (((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + 1) / n) *
        (n.descFactorial (bernoulliPatternVertexCount s) : ℝ)) *
          (p : ℝ) ^ bernoulliPatternEntryCount b s :=
      parameter_bernoulli_pattern_abs_bound n p hp b s hSurvive
    _ = sparseRealEvenPatternBudget n (bernoulliPatternVertexCount s)
        (bernoulliPatternEntryCount b s) m (bernoulliEffectiveDegree n p) *
          (Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ := by
      rw [hLength, pow_succ, bernoulli_parameter_eq_effective_degree_div hn p,
        ← sparse_real_even_pattern_scale_identity hn hDPos]
      ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hBudget

theorem parameter_bernoulli_odd_pattern_tendsto_zero {k m : ℕ} (q : ℕ → ℕ)
    (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m + 1) :
    Tendsto (fun n => parameterBernoulliPatternContribution (q n) (p n) (hp n) b s)
      atTop (𝓝 0) := by
  by_cases hSurvive : BernoulliSurvivingPattern b s
  · have hAbs : Tendsto
        (fun n => |parameterBernoulliPatternContribution (q n) (p n) (hp n) b s|)
        atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
        (inverse_sqrt_real_degree_tendsto_zero _ hDegree)
      filter_upwards [hQ.eventually_gt_atTop 0, hDegree.eventually_ge_atTop 1] with n hn hd
      exact parameter_bernoulli_odd_pattern_abs_bound hn (p n) (hp n) hd b s hLength hSurvive
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hAbs)
  · simpa only [parameter_bernoulli_nonsurviving_pattern_zero _ _ _ b s hSurvive] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem parameter_bernoulli_nonempty_word_mean_tendsto {k : ℕ} (q : ℕ → ℕ)
    (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (b : Fin (k + 1) → Bool) :
    Tendsto (fun n => parameterBernoulliWordMean (q n) (p n) (hp n) (List.ofFn b))
      atTop (𝓝 (bernoulliLeadingPatternCount b : ℝ)) := by
  simp only [parameter_bernoulli_word_mean_pattern_sum]
  obtain ⟨m, hEven | hOdd⟩ := Nat.even_or_odd' (k + 1)
  · rw [bernoulli_leading_pattern_count_indicator_sum]
    exact tendsto_finset_sum Finset.univ (fun s _ =>
      parameter_bernoulli_even_pattern_tendsto q p hp hQ hDegree hSparse b s hEven)
  · rw [bernoulli_odd_leading_pattern_count_zero b hOdd, Nat.cast_zero]
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun s _ =>
        parameter_bernoulli_odd_pattern_tendsto_zero q p hp hQ hDegree b s hOdd)

theorem parameter_bernoulli_all_word_mean_tendsto (q : ℕ → ℕ) (p : ℕ → ℝ≥0)
    (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (hSparse : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0)) (w : List Bool) :
    Tendsto (fun n => parameterBernoulliWordMean (q n) (p n) (hp n) w)
      atTop (𝓝 (gaussianWordMeanCount w : ℝ)) := by
  rw [← bernoulli_word_mean_limit_eq_gaussian]
  cases w with
  | nil =>
    simp only [bernoulliWordMeanLimit, Nat.cast_one]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [hQ.eventually_gt_atTop 0] with n hn
    exact (parameter_bernoulli_empty_word_mean hn (p n) (hp n)).symm
  | cons b w =>
    simpa only [bernoulliWordMeanLimit, List.ofFn_get] using
      parameter_bernoulli_nonempty_word_mean_tendsto q p hp hQ hDegree hSparse ((b :: w).get)

end CircularLaw
