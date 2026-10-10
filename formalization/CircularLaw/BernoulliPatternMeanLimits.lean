import CircularLaw.BernoulliWalkPatterns
import CircularLaw.SparsePatternPowerLimits

/-!
# Actual even Bernoulli word-mean limits from equality patterns

Sparse degrees tend to infinity while d/n tends to zero. Singleton
entries vanish exactly, nonleading patterns vanish by dimension or
degree loss, and every leading paired tree pattern contributes one.
The exact finite pattern sum therefore gives the actual normalized
trace-mean limit at every positive even word length. Identifying this
pattern count with the Gaussian count and proving concentration remain
separate obligations. Odd words are handled in `BernoulliAllWordMeanLimits`.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

local instance bernoulliMeanQuotientBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

def BernoulliSurvivingPattern {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) : Prop :=
  ∀ e, (bernoulliPatternEntryWord b s).count e ≠ 1

def BernoulliLeadingPattern {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) : Prop :=
  BernoulliSurvivingPattern b s ∧
    bernoulliPatternVertexCount s = bernoulliPatternEntryCount b s + 1 ∧
      2 * bernoulliPatternEntryCount b s = k + 1

def bernoulliPatternContribution {k : ℕ} (n d : ℕ) (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) : ℝ :=
  (((Real.sqrt (d : ℝ))⁻¹) ^ (k + 1) / n) *
    (n.descFactorial (bernoulliPatternVertexCount s) : ℝ) *
      bernoulliWalkPatternWeight (min (rowBernoulliParameter n d) 1) (min_le_right _ _) b s

theorem bernoulli_normalized_word_eq_pattern_sum {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (k : ℕ) (b : Fin (k + 1) → Bool) :
    bernoulliNormalizedWordMean n d (List.ofFn b) =
      ∑ s : Setoid (Fin (k + 1)), bernoulliPatternContribution n d b s := by
  rw [bernoulli_normalized_word_pattern_formula hn hdn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold bernoulliPatternContribution bernoulliPatternVertexCount
  simp only [min_eq_left (rowBernoulliParameter_le_one hn hdn)]
  ring

theorem sparse_degrees_eventually_valid (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < n ∧ 0 < d n ∧ d n ≤ n := by
  have hSmall := hSparse.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_gt_atTop 0, hDegree.eventually_gt_atTop 0, hSmall]
    with n hn hd hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdnR : (d n : ℝ) < n := (div_lt_one hnR).mp hp
  exact ⟨hn, hd, by exact_mod_cast hdnR.le⟩

theorem bernoulli_nonsurviving_pattern_contribution_zero {k : ℕ} (n d : ℕ)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hNot : ¬ BernoulliSurvivingPattern b s) : bernoulliPatternContribution n d b s = 0 := by
  unfold BernoulliSurvivingPattern at hNot
  push_neg at hNot
  obtain ⟨e, he⟩ := hNot
  unfold bernoulliPatternContribution
  rw [bernoulli_pattern_weight_singleton_zero _ _ b s e he, mul_zero]

theorem bernoulli_pattern_contribution_abs_parameter_bound {k : ℕ}
    (n d : ℕ) (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hSurvive : BernoulliSurvivingPattern b s) :
    |bernoulliPatternContribution n d b s| ≤
      ((((Real.sqrt (d : ℝ))⁻¹) ^ (k + 1) / n) *
        (n.descFactorial (bernoulliPatternVertexCount s) : ℝ)) *
          ((d : ℝ) / n) ^ bernoulliPatternEntryCount b s := by
  have hClip : ((min (rowBernoulliParameter n d) 1 : ℝ≥0) : ℝ) ≤ (d : ℝ) / n := by
    rw [← rowBernoulliParameter_coe]
    exact_mod_cast min_le_left (rowBernoulliParameter n d) 1
  have hWeight : |bernoulliWalkPatternWeight (min (rowBernoulliParameter n d) 1)
      (min_le_right _ _) b s| ≤ ((d : ℝ) / n) ^ bernoulliPatternEntryCount b s :=
    (bernoulli_pattern_weight_abs_bound _ _ b s hSurvive).trans
      (pow_le_pow_left₀ (NNReal.coe_nonneg _) hClip _)
  unfold bernoulliPatternContribution
  rw [abs_mul, abs_of_nonneg (show 0 ≤
    (((Real.sqrt (d : ℝ))⁻¹) ^ (k + 1) / n) *
      (n.descFactorial (bernoulliPatternVertexCount s) : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left hWeight (by positivity)

theorem bernoulli_even_pattern_contribution_abs_bound {n d k m : ℕ}
    (hn : 0 < n) (hd : 0 < d) (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m)
    (hSurvive : BernoulliSurvivingPattern b s) :
    |bernoulliPatternContribution n d b s| ≤
      sparseEvenPatternBudget n d (bernoulliPatternVertexCount s)
        (bernoulliPatternEntryCount b s) m := by
  have h := bernoulli_pattern_contribution_abs_parameter_bound n d b s hSurvive
  rwa [hLength, sparse_even_pattern_scale_identity hn hd] at h

theorem bernoulli_even_leading_pattern_contribution_formula {n d k m : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m)
    (hLeading : BernoulliLeadingPattern b s) :
    bernoulliPatternContribution n d b s =
      sparseEvenPatternBudget n d (bernoulliPatternVertexCount s) m m *
        (1 - (d : ℝ) / n) ^ m := by
  have hE : bernoulliPatternEntryCount b s = m := by
    have h := hLeading.2.2
    omega
  have hPaired := bernoulli_maximal_entry_pattern_paired b s hLeading.1 hLeading.2.2
  have hWeight : bernoulliWalkPatternWeight (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one hn hdn) b s =
        (((d : ℝ) / n) * (1 - (d : ℝ) / n)) ^ m := by
    rw [bernoulli_paired_pattern_weight _ _ b s hPaired,
      ← bernoulliPatternEntryCount, hE, rowBernoulliParameter_coe]
  unfold bernoulliPatternContribution
  simp only [min_eq_left (rowBernoulliParameter_le_one hn hdn)]
  rw [hWeight, hLength,
    mul_pow, ← mul_assoc, sparse_even_pattern_scale_identity hn hd]

theorem bernoulli_even_pattern_contribution_tendsto {k m : ℕ}
    (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) (hLength : k + 1 = 2 * m) :
    Tendsto (fun n => bernoulliPatternContribution n (d n) b s) atTop
      (𝓝 (if BernoulliLeadingPattern b s then 1 else 0)) := by
  have hValid := sparse_degrees_eventually_valid d hDegree hSparse
  by_cases hLeading : BernoulliLeadingPattern b s
  · rw [if_pos hLeading]
    have hE : bernoulliPatternEntryCount b s = m := by
      have h := hLeading.2.2
      omega
    have hV : bernoulliPatternVertexCount s = m + 1 := hLeading.2.1.trans (by rw [hE])
    have hBudget : Tendsto (fun n => sparseEvenPatternBudget n (d n)
        (bernoulliPatternVertexCount s) m m) atTop (𝓝 1) := by
      simpa only [hV, eq_self_iff_true, and_self, if_true] using
        sparse_even_pattern_budget_tendsto d hDegree _ m m hV.le le_rfl
    have hFactor : Tendsto (fun n => (1 - (d n : ℝ) / n) ^ m) atTop (𝓝 1) := by
      have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [sub_zero, one_pow] using (hOne.sub hSparse).pow m
    have h := hBudget.mul hFactor
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [hValid] with n hn
    exact (bernoulli_even_leading_pattern_contribution_formula hn.1 hn.2.1 hn.2.2
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
      have hBudget := sparse_even_nonleading_budget_tendsto_zero d hDegree _ _ m hV hE hNonleading
      have hAbs : Tendsto (fun n => |bernoulliPatternContribution n (d n) b s|) atTop (𝓝 0) := by
        apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hBudget
        filter_upwards [hValid] with n hn
        exact bernoulli_even_pattern_contribution_abs_bound hn.1 hn.2.1 b s hLength hSurvive
      exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hAbs)
    · simpa only [bernoulli_nonsurviving_pattern_contribution_zero _ _ b s hSurvive] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

def bernoulliLeadingPatternCount {k : ℕ} (b : Fin (k + 1) → Bool) : ℕ :=
  Nat.card {s : Setoid (Fin (k + 1)) // BernoulliLeadingPattern b s}

theorem bernoulli_leading_pattern_count_indicator_sum {k : ℕ} (b : Fin (k + 1) → Bool) :
    (bernoulliLeadingPatternCount b : ℝ) =
      ∑ s : Setoid (Fin (k + 1)), if BernoulliLeadingPattern b s then (1 : ℝ) else 0 := by
  rw [bernoulliLeadingPatternCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

theorem bernoulli_even_word_mean_tendsto {k m : ℕ} (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    (b : Fin (k + 1) → Bool) (hLength : k + 1 = 2 * m) :
    Tendsto (fun n => bernoulliNormalizedWordMean n (d n) (List.ofFn b)) atTop
      (𝓝 (bernoulliLeadingPatternCount b : ℝ)) := by
  rw [bernoulli_leading_pattern_count_indicator_sum]
  have h := tendsto_finset_sum Finset.univ (fun s _ =>
    bernoulli_even_pattern_contribution_tendsto d hDegree hSparse b s hLength)
  apply h.congr'
  filter_upwards [sparse_degrees_eventually_valid d hDegree hSparse] with n hn
  exact (bernoulli_normalized_word_eq_pattern_sum hn.1 hn.2.2 k b).symm

end CircularLaw
