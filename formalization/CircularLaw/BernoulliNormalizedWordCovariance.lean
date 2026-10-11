import CircularLaw.BernoulliTwoWordCovariance
import CircularLaw.BernoulliAllWordMeanLimits

/-!
# Actual normalized Bernoulli word covariance vanishes

Entry-disjoint pairs cancel exactly. A pair sharing an entry is connected,
so its number of vertices is at most its number of entries plus one.
Together with the two trace normalizations, this supplies a dimension
loss for every surviving covariance pattern, at every fixed word length.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

def bernoulliNormalizedWordTrace {n : ℕ} (d : ℕ) (w : List Bool)
    (x : BernoulliSquareSample n) : ℝ :=
  (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace.re / n

def bernoulliNormalizedWordCovariance (n d : ℕ) (w v : List Bool) : ℝ :=
  (∫ x, bernoulliNormalizedWordTrace d w x * bernoulliNormalizedWordTrace d v x
    ∂sparseBernoulliMatrixLaw n d) -
    bernoulliNormalizedWordMean n d w * bernoulliNormalizedWordMean n d v

theorem bernoulli_normalized_word_trace_scale {n : ℕ} (d : ℕ) (w : List Bool)
    (x : BernoulliSquareSample n) :
    bernoulliNormalizedWordTrace d w x =
      ((Real.sqrt (d : ℝ))⁻¹ ^ w.length / n) *
        (matrixAdjointWord (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) x) w).trace.re := by
  unfold bernoulliNormalizedWordTrace normalizedCenteredBernoulliMatrix
  rw [← Complex.ofReal_inv, matrix_adjoint_word_trace_re_real_smul]
  ring

theorem bernoulli_normalized_two_word_covariance_scale {n d k l : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    bernoulliNormalizedWordCovariance n d (List.ofFn b) (List.ofFn c) =
      ((Real.sqrt (d : ℝ))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
        bernoulliTwoWordRawCovariance n (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one hn hdn) b c := by
  have hMean (w : List Bool) : bernoulliNormalizedWordMean n d w =
      ∫ x, bernoulliNormalizedWordTrace d w x ∂sparseBernoulliMatrixLaw n d := rfl
  have hProduct (a e : ℝ) (f g : BernoulliSquareSample n → ℝ) :
      (∫ x, (a * f x) * (e * g x) ∂sparseBernoulliMatrixLaw n d) =
        (a * e) * ∫ x, f x * g x ∂sparseBernoulliMatrixLaw n d := by
    rw [show (fun x => (a * f x) * (e * g x)) =
      (fun x => (a * e) * (f x * g x)) by funext x; ring, integral_const_mul]
  unfold bernoulliNormalizedWordCovariance
  rw [hMean, hMean]
  simp_rw [bernoulli_normalized_word_trace_scale, List.length_ofFn]
  rw [hProduct, integral_const_mul, integral_const_mul]
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  unfold bernoulliTwoWordRawCovariance
  rw [show k + l + 2 = (k + 1) + (l + 1) by omega, pow_add, pow_two]
  ring

def bernoulliTwoPatternContribution {k l : ℕ} (n d : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) : ℝ :=
  ((Real.sqrt (d : ℝ))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
    (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ) *
      bernoulliTwoPatternCovarianceWeight (min (rowBernoulliParameter n d) 1)
        (min_le_right _ _) b c s

theorem bernoulli_normalized_two_word_covariance_pattern_sum {n d k l : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    bernoulliNormalizedWordCovariance n d (List.ofFn b) (List.ofFn c) =
      ∑ s : Setoid (BernoulliTwoWalkPositions k l), bernoulliTwoPatternContribution n d b c s := by
  rw [bernoulli_normalized_two_word_covariance_scale hn hdn,
    bernoulli_two_word_raw_covariance_pattern_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold bernoulliTwoPatternContribution
  simp only [min_eq_left (rowBernoulliParameter_le_one hn hdn)]
  ring

theorem bernoulli_two_pattern_no_shared_contribution_zero {k l : ℕ} (n d : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (h : ¬ BernoulliTwoPatternSharesEntry b c s) :
    bernoulliTwoPatternContribution n d b c s = 0 := by
  unfold bernoulliTwoPatternContribution
  rw [bernoulli_two_pattern_no_shared_covariance_zero _ _ b c s h, mul_zero]

theorem bernoulli_two_pattern_nonsurviving_contribution_zero {k l : ℕ} (n d : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (h : ¬ BernoulliTwoPatternSurvives b c s) :
    bernoulliTwoPatternContribution n d b c s = 0 := by
  unfold bernoulliTwoPatternContribution
  rw [bernoulli_two_pattern_nonsurviving_covariance_zero _ _ b c s h, mul_zero]

theorem bernoulli_two_pattern_contribution_abs_parameter_bound {k l : ℕ} (n d : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (h : BernoulliTwoPatternSurvives b c s) :
    |bernoulliTwoPatternContribution n d b c s| ≤
      (((Real.sqrt (d : ℝ))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
        (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ)) *
          (2 * ((d : ℝ) / n) ^ bernoulliTwoPatternEntryCount b c s) := by
  have hClip : ((min (rowBernoulliParameter n d) 1 : ℝ≥0) : ℝ) ≤ (d : ℝ) / n := by
    rw [← rowBernoulliParameter_coe]
    exact_mod_cast min_le_left (rowBernoulliParameter n d) 1
  have hWeight := bernoulli_two_pattern_covariance_abs_bound
    (min (rowBernoulliParameter n d) 1) (min_le_right _ _) b c s h
  have hPow := pow_le_pow_left₀ (NNReal.coe_nonneg _) hClip
    (bernoulliTwoPatternEntryCount b c s)
  have hBound := hWeight.trans (mul_le_mul_of_nonneg_left hPow (by norm_num : (0 : ℝ) ≤ 2))
  unfold bernoulliTwoPatternContribution
  rw [abs_mul, abs_of_nonneg (show 0 ≤
    ((Real.sqrt (d : ℝ))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
      (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left hBound (by positivity)

theorem bernoulli_even_two_pattern_contribution_abs_bound {n d k l m : ℕ}
    (hn : 0 < n) (hd : 0 < d) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hLength : k + l + 2 = 2 * m)
    (hSurvive : BernoulliTwoPatternSurvives b c s)
    (hShared : BernoulliTwoPatternSharesEntry b c s) :
    |bernoulliTwoPatternContribution n d b c s| ≤ 2 / (n : ℝ) := by
  have hE : bernoulliTwoPatternEntryCount b c s ≤ m := by
    have h := bernoulli_two_pattern_surviving_entry_bound b c s hSurvive
    omega
  have hV := bernoulli_two_pattern_shared_entry_vertex_bound b c s hShared
  have hBudget := sparse_even_pattern_budget_le_one hn hd hV hE
  calc
    _ ≤ _ := bernoulli_two_pattern_contribution_abs_parameter_bound n d b c s hSurvive
    _ = (2 / (n : ℝ)) * sparseEvenPatternBudget n d
        (bernoulliTwoPatternVertexCount s) (bernoulliTwoPatternEntryCount b c s) m := by
      rw [hLength, ← sparse_even_pattern_scale_identity hn hd, pow_two]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hBudget

theorem bernoulli_odd_two_pattern_contribution_abs_bound {n d k l m : ℕ}
    (hn : 0 < n) (hd : 0 < d) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hLength : k + l + 2 = 2 * m + 1)
    (hSurvive : BernoulliTwoPatternSurvives b c s)
    (hShared : BernoulliTwoPatternSharesEntry b c s) :
    |bernoulliTwoPatternContribution n d b c s| ≤ (2 / (n : ℝ)) * (Real.sqrt (d : ℝ))⁻¹ := by
  have hE : bernoulliTwoPatternEntryCount b c s ≤ m := by
    have h := bernoulli_two_pattern_surviving_entry_bound b c s hSurvive
    omega
  have hV := bernoulli_two_pattern_shared_entry_vertex_bound b c s hShared
  have hBudget := sparse_even_pattern_budget_le_one hn hd hV hE
  calc
    _ ≤ _ := bernoulli_two_pattern_contribution_abs_parameter_bound n d b c s hSurvive
    _ = ((2 / (n : ℝ)) * (Real.sqrt (d : ℝ))⁻¹) * sparseEvenPatternBudget n d
        (bernoulliTwoPatternVertexCount s) (bernoulliTwoPatternEntryCount b c s) m := by
      rw [hLength, pow_succ, ← sparse_even_pattern_scale_identity hn hd, pow_two]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hBudget

theorem bernoulli_two_pattern_contribution_tendsto_zero {k l : ℕ}
    (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) :
    Tendsto (fun n => bernoulliTwoPatternContribution n (d n) b c s) atTop (𝓝 0) := by
  by_cases hSurvive : BernoulliTwoPatternSurvives b c s
  · by_cases hShared : BernoulliTwoPatternSharesEntry b c s
    · have hInv : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
      have hAbs : Tendsto (fun n => |bernoulliTwoPatternContribution n (d n) b c s|)
          atTop (𝓝 0) := by
        obtain ⟨m, hEven | hOdd⟩ := Nat.even_or_odd' (k + l + 2)
        · apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hInv
          filter_upwards [eventually_gt_atTop 0, hDegree.eventually_gt_atTop 0] with n hn hd
          exact bernoulli_even_two_pattern_contribution_abs_bound hn hd b c s hEven hSurvive hShared
        · have hUpper := hInv.mul (inverse_sqrt_degree_tendsto_zero d hDegree)
          simp only [zero_mul] at hUpper
          apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hUpper
          filter_upwards [eventually_gt_atTop 0, hDegree.eventually_gt_atTop 0] with n hn hd
          exact bernoulli_odd_two_pattern_contribution_abs_bound hn hd b c s hOdd hSurvive hShared
      exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hAbs)
    · simpa only [bernoulli_two_pattern_no_shared_contribution_zero _ _ b c s hShared] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · simpa only [bernoulli_two_pattern_nonsurviving_contribution_zero _ _ b c s hSurvive] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem bernoulli_nonempty_word_covariance_tendsto_zero {k l : ℕ}
    (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Tendsto (fun n => bernoulliNormalizedWordCovariance n (d n) (List.ofFn b) (List.ofFn c))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ s : Setoid (BernoulliTwoWalkPositions k l),
      bernoulliTwoPatternContribution n (d n) b c s) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ
      (fun s _ => bernoulli_two_pattern_contribution_tendsto_zero d hDegree b c s)
  apply h.congr'
  filter_upwards [sparse_degrees_eventually_valid d hDegree hSparse] with n hn
  exact (bernoulli_normalized_two_word_covariance_pattern_sum hn.1 hn.2.2 b c).symm

theorem bernoulli_normalized_word_covariance_empty_left (n d : ℕ) (w : List Bool) :
    bernoulliNormalizedWordCovariance n d [] w = 0 := by
  simp [bernoulliNormalizedWordCovariance, bernoulliNormalizedWordTrace,
    bernoulliNormalizedWordMean, matrixAdjointWord, integral_const_mul]

theorem bernoulli_normalized_word_covariance_symm (n d : ℕ) (w v : List Bool) :
    bernoulliNormalizedWordCovariance n d w v = bernoulliNormalizedWordCovariance n d v w := by
  unfold bernoulliNormalizedWordCovariance
  simp only [mul_comm]

theorem bernoulli_all_word_covariance_tendsto_zero (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (w v : List Bool) :
    Tendsto (fun n => bernoulliNormalizedWordCovariance n (d n) w v) atTop (𝓝 0) := by
  cases w with
  | nil => simpa only [bernoulli_normalized_word_covariance_empty_left] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | cons b w =>
    cases v with
    | nil => simpa only [bernoulli_normalized_word_covariance_symm _ _ (b :: w) [],
        bernoulli_normalized_word_covariance_empty_left] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | cons c v => simpa only [List.ofFn_get] using
        bernoulli_nonempty_word_covariance_tendsto_zero d hDegree hSparse ((b :: w).get) ((c :: v).get)

end CircularLaw
