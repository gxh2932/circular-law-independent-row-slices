import CircularLaw.BernoulliPatternMeanLimits

/-!
# Actual sparse Bernoulli mean limits for every finite word

Odd words have one extra inverse square-root degree factor. Their
surviving pattern contributions tend to zero. Even words retain the
checked leading-pattern count, and the empty word has mean one. Thus
every actual centered, sparsely normalized direct/adjoint word has its
mean limit. Gaussian identification and second-moment concentration
remain required before obtaining the Bernoulli weak singular law.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

theorem inverse_sqrt_degree_tendsto_zero (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop) :
    Tendsto (fun n => (Real.sqrt (d n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hDegree))

theorem bernoulli_odd_pattern_contribution_abs_bound {n d k m : ℕ}
    (hn : 0 < n) (hd : 0 < d) (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m + 1)
    (hSurvive : BernoulliSurvivingPattern b s) :
    |bernoulliPatternContribution n d b s| ≤ (Real.sqrt (d : ℝ))⁻¹ := by
  have hE : bernoulliPatternEntryCount b s ≤ m := by
    have h := bernoulli_pattern_surviving_entry_bound b s hSurvive
    omega
  have hV := bernoulli_pattern_vertex_bound b s
  have hBudget := sparse_even_pattern_budget_le_one hn hd hV hE
  calc
    _ ≤ ((((Real.sqrt (d : ℝ))⁻¹) ^ (k + 1) / n) *
        (n.descFactorial (bernoulliPatternVertexCount s) : ℝ)) *
          ((d : ℝ) / n) ^ bernoulliPatternEntryCount b s :=
      bernoulli_pattern_contribution_abs_parameter_bound n d b s hSurvive
    _ = sparseEvenPatternBudget n d (bernoulliPatternVertexCount s)
        (bernoulliPatternEntryCount b s) m * (Real.sqrt (d : ℝ))⁻¹ := by
      rw [hLength, pow_succ]
      rw [show (((Real.sqrt (d : ℝ))⁻¹ ^ (2 * m) * (Real.sqrt (d : ℝ))⁻¹ / n) *
          (n.descFactorial (bernoulliPatternVertexCount s) : ℝ)) *
            ((d : ℝ) / n) ^ bernoulliPatternEntryCount b s =
          (((Real.sqrt (d : ℝ))⁻¹ ^ (2 * m) / n) *
            (n.descFactorial (bernoulliPatternVertexCount s) : ℝ) *
              ((d : ℝ) / n) ^ bernoulliPatternEntryCount b s) * (Real.sqrt (d : ℝ))⁻¹ by ring]
      rw [sparse_even_pattern_scale_identity hn hd]
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hBudget

theorem bernoulli_odd_pattern_contribution_tendsto_zero {k m : ℕ}
    (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m + 1) :
    Tendsto (fun n => bernoulliPatternContribution n (d n) b s) atTop (𝓝 0) := by
  by_cases hSurvive : BernoulliSurvivingPattern b s
  · have hAbs : Tendsto (fun n => |bernoulliPatternContribution n (d n) b s|) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
        (inverse_sqrt_degree_tendsto_zero d hDegree)
      filter_upwards [eventually_gt_atTop 0, hDegree.eventually_gt_atTop 0] with n hn hd
      exact bernoulli_odd_pattern_contribution_abs_bound hn hd b s hLength hSurvive
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hAbs)
  · simpa only [bernoulli_nonsurviving_pattern_contribution_zero _ _ b s hSurvive] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem bernoulli_odd_leading_pattern_count_zero {k m : ℕ} (b : Fin (k + 1) → Bool)
    (hLength : k + 1 = 2 * m + 1) : bernoulliLeadingPatternCount b = 0 := by
  have hNot (s : Setoid (Fin (k + 1))) : ¬ BernoulliLeadingPattern b s := by
    intro h
    have hE := h.2.2
    omega
  have hCount : (bernoulliLeadingPatternCount b : ℝ) = 0 := by
    rw [bernoulli_leading_pattern_count_indicator_sum]
    simp only [if_neg (hNot _), Finset.sum_const_zero]
  exact_mod_cast hCount

theorem bernoulli_odd_word_mean_tendsto_zero {k m : ℕ} (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    (b : Fin (k + 1) → Bool) (hLength : k + 1 = 2 * m + 1) :
    Tendsto (fun n => bernoulliNormalizedWordMean n (d n) (List.ofFn b)) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ s : Setoid (Fin (k + 1)),
      bernoulliPatternContribution n (d n) b s) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun s _ =>
        bernoulli_odd_pattern_contribution_tendsto_zero d hDegree b s hLength)
  apply h.congr'
  filter_upwards [sparse_degrees_eventually_valid d hDegree hSparse] with n hn
  exact (bernoulli_normalized_word_eq_pattern_sum hn.1 hn.2.2 k b).symm

theorem bernoulli_nonempty_word_mean_tendsto {k : ℕ} (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    (b : Fin (k + 1) → Bool) :
    Tendsto (fun n => bernoulliNormalizedWordMean n (d n) (List.ofFn b)) atTop
      (𝓝 (bernoulliLeadingPatternCount b : ℝ)) := by
  obtain ⟨m, hEven | hOdd⟩ := Nat.even_or_odd' (k + 1)
  · exact bernoulli_even_word_mean_tendsto d hDegree hSparse b hEven
  · rw [bernoulli_odd_leading_pattern_count_zero b hOdd, Nat.cast_zero]
    exact bernoulli_odd_word_mean_tendsto_zero d hDegree hSparse b hOdd

def bernoulliWordMeanLimit : List Bool → ℕ
  | [] => 1
  | b :: w => bernoulliLeadingPatternCount ((b :: w).get)

theorem bernoulli_all_word_mean_tendsto (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w : List Bool) :
    Tendsto (fun n => bernoulliNormalizedWordMean n (d n) w) atTop
      (𝓝 (bernoulliWordMeanLimit w : ℝ)) := by
  cases w with
  | nil =>
    simp only [bernoulliWordMeanLimit, Nat.cast_one]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (bernoulli_normalized_empty_word_mean hn (d n)).symm
  | cons b w =>
    simpa only [bernoulliWordMeanLimit, List.ofFn_get] using
      bernoulli_nonempty_word_mean_tendsto d hDegree hSparse ((b :: w).get)

end CircularLaw
