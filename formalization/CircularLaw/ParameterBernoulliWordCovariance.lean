import CircularLaw.ParameterBernoulliMeanLimits

/-!
# Actual Bernoulli word covariance at a real effective degree

The exact joint-kernel covariance sum works for every Bernoulli parameter.
A shared entry connects the two walks, giving a dimension loss. The degree
budget needs only effective degree at least one, rather than integrality.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix NNReal Topology

namespace CircularLaw

def parameterBernoulliWordCovariance (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (w v : List Bool) : ℝ :=
  (∫ x, parameterBernoulliWordTrace p w x * parameterBernoulliWordTrace p v x
    ∂bernoulliSquareMatrixLaw n p hp) -
    parameterBernoulliWordMean n p hp w * parameterBernoulliWordMean n p hp v

def parameterBernoulliTwoPatternContribution {k l : ℕ} (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) : ℝ :=
  ((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
    (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ) *
      bernoulliTwoPatternCovarianceWeight p hp b c s

theorem parameter_bernoulli_two_word_covariance_scale {n k l : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    parameterBernoulliWordCovariance n p hp (List.ofFn b) (List.ofFn c) =
      ((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
        bernoulliTwoWordRawCovariance n p hp b c := by
  have hProduct (a e : ℝ) (f g : BernoulliSquareSample n → ℝ) :
      (∫ x, (a * f x) * (e * g x) ∂bernoulliSquareMatrixLaw n p hp) =
        (a * e) * ∫ x, f x * g x ∂bernoulliSquareMatrixLaw n p hp := by
    rw [show (fun x => (a * f x) * (e * g x)) =
      (fun x => (a * e) * (f x * g x)) by funext x; ring, integral_const_mul]
  unfold parameterBernoulliWordCovariance parameterBernoulliWordMean
  simp_rw [parameter_bernoulli_word_trace_scale, List.length_ofFn]
  rw [hProduct, integral_const_mul, integral_const_mul]
  unfold bernoulliTwoWordRawCovariance
  rw [show k + l + 2 = (k + 1) + (l + 1) by omega, pow_add, pow_two]
  ring

theorem parameter_bernoulli_two_word_covariance_pattern_sum {n k l : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    parameterBernoulliWordCovariance n p hp (List.ofFn b) (List.ofFn c) =
      ∑ s : Setoid (BernoulliTwoWalkPositions k l),
        parameterBernoulliTwoPatternContribution n p hp b c s := by
  rw [parameter_bernoulli_two_word_covariance_scale p hp,
    bernoulli_two_word_raw_covariance_pattern_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold parameterBernoulliTwoPatternContribution
  ring

theorem parameter_bernoulli_two_pattern_no_shared_zero {k l : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (h : ¬ BernoulliTwoPatternSharesEntry b c s) :
    parameterBernoulliTwoPatternContribution n p hp b c s = 0 := by
  unfold parameterBernoulliTwoPatternContribution
  rw [bernoulli_two_pattern_no_shared_covariance_zero p hp b c s h, mul_zero]

theorem parameter_bernoulli_two_pattern_nonsurviving_zero {k l : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (h : ¬ BernoulliTwoPatternSurvives b c s) :
    parameterBernoulliTwoPatternContribution n p hp b c s = 0 := by
  unfold parameterBernoulliTwoPatternContribution
  rw [bernoulli_two_pattern_nonsurviving_covariance_zero p hp b c s h, mul_zero]

theorem parameter_bernoulli_two_pattern_abs_bound {k l : ℕ} (n : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (h : BernoulliTwoPatternSurvives b c s) :
    |parameterBernoulliTwoPatternContribution n p hp b c s| ≤
      (((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
        (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ)) *
          (2 * (p : ℝ) ^ bernoulliTwoPatternEntryCount b c s) := by
  unfold parameterBernoulliTwoPatternContribution
  rw [abs_mul, abs_of_nonneg (show 0 ≤
    ((Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ ^ (k + l + 2) / (n : ℝ) ^ 2) *
      (n.descFactorial (bernoulliTwoPatternVertexCount s) : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left (bernoulli_two_pattern_covariance_abs_bound p hp b c s h)
    (by positivity)

theorem parameter_bernoulli_even_two_pattern_abs_bound {n k l m : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) (hD : 1 ≤ bernoulliEffectiveDegree n p)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hLength : k + l + 2 = 2 * m)
    (hSurvive : BernoulliTwoPatternSurvives b c s) (hShared : BernoulliTwoPatternSharesEntry b c s) :
    |parameterBernoulliTwoPatternContribution n p hp b c s| ≤ 2 / (n : ℝ) := by
  have hE : bernoulliTwoPatternEntryCount b c s ≤ m := by
    have h := bernoulli_two_pattern_surviving_entry_bound b c s hSurvive
    omega
  have hV := bernoulli_two_pattern_shared_entry_vertex_bound b c s hShared
  have hBudget := sparse_real_even_pattern_budget_le_one hn hD hV hE
  have hDPos : 0 < bernoulliEffectiveDegree n p := by linarith
  calc
    _ ≤ _ := parameter_bernoulli_two_pattern_abs_bound n p hp b c s hSurvive
    _ = (2 / (n : ℝ)) * sparseRealEvenPatternBudget n
        (bernoulliTwoPatternVertexCount s) (bernoulliTwoPatternEntryCount b c s) m
        (bernoulliEffectiveDegree n p) := by
      rw [hLength, bernoulli_parameter_eq_effective_degree_div hn p,
        ← sparse_real_even_pattern_scale_identity hn hDPos, pow_two]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hBudget

theorem parameter_bernoulli_odd_two_pattern_abs_bound {n k l m : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) (hD : 1 ≤ bernoulliEffectiveDegree n p)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hLength : k + l + 2 = 2 * m + 1)
    (hSurvive : BernoulliTwoPatternSurvives b c s) (hShared : BernoulliTwoPatternSharesEntry b c s) :
    |parameterBernoulliTwoPatternContribution n p hp b c s| ≤
      (2 / (n : ℝ)) * (Real.sqrt (bernoulliEffectiveDegree n p))⁻¹ := by
  have hE : bernoulliTwoPatternEntryCount b c s ≤ m := by
    have h := bernoulli_two_pattern_surviving_entry_bound b c s hSurvive
    omega
  have hV := bernoulli_two_pattern_shared_entry_vertex_bound b c s hShared
  have hBudget := sparse_real_even_pattern_budget_le_one hn hD hV hE
  have hDPos : 0 < bernoulliEffectiveDegree n p := by linarith
  calc
    _ ≤ _ := parameter_bernoulli_two_pattern_abs_bound n p hp b c s hSurvive
    _ = ((2 / (n : ℝ)) * (Real.sqrt (bernoulliEffectiveDegree n p))⁻¹) *
        sparseRealEvenPatternBudget n (bernoulliTwoPatternVertexCount s)
          (bernoulliTwoPatternEntryCount b c s) m (bernoulliEffectiveDegree n p) := by
      rw [hLength, pow_succ, bernoulli_parameter_eq_effective_degree_div hn p,
        ← sparse_real_even_pattern_scale_identity hn hDPos, pow_two]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hBudget

theorem parameter_bernoulli_two_pattern_tendsto_zero {k l : ℕ}
    (q : ℕ → ℕ) (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) :
    Tendsto (fun n => parameterBernoulliTwoPatternContribution (q n) (p n) (hp n) b c s)
      atTop (𝓝 0) := by
  by_cases hSurvive : BernoulliTwoPatternSurvives b c s
  · by_cases hShared : BernoulliTwoPatternSharesEntry b c s
    · have hInv : Tendsto (fun n => 2 / (q n : ℝ)) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hQ)).const_mul (2 : ℝ)
      have hAbs : Tendsto
          (fun n => |parameterBernoulliTwoPatternContribution (q n) (p n) (hp n) b c s|)
          atTop (𝓝 0) := by
        obtain ⟨m, hEven | hOdd⟩ := Nat.even_or_odd' (k + l + 2)
        · apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hInv
          filter_upwards [hQ.eventually_gt_atTop 0, hDegree.eventually_ge_atTop 1] with n hn hd
          exact parameter_bernoulli_even_two_pattern_abs_bound hn (p n) (hp n) hd
            b c s hEven hSurvive hShared
        · have hUpper := hInv.mul (inverse_sqrt_real_degree_tendsto_zero _ hDegree)
          simp only [zero_mul] at hUpper
          apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hUpper
          filter_upwards [hQ.eventually_gt_atTop 0, hDegree.eventually_ge_atTop 1] with n hn hd
          exact parameter_bernoulli_odd_two_pattern_abs_bound hn (p n) (hp n) hd
            b c s hOdd hSurvive hShared
      exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hAbs)
    · simpa only [parameter_bernoulli_two_pattern_no_shared_zero _ _ _ b c s hShared] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · simpa only [parameter_bernoulli_two_pattern_nonsurviving_zero _ _ _ b c s hSurvive] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem parameter_bernoulli_nonempty_word_covariance_tendsto_zero {k l : ℕ}
    (q : ℕ → ℕ) (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Tendsto (fun n => parameterBernoulliWordCovariance (q n) (p n) (hp n)
      (List.ofFn b) (List.ofFn c)) atTop (𝓝 0) := by
  simp only [parameter_bernoulli_two_word_covariance_pattern_sum]
  simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ
    (fun s _ => parameter_bernoulli_two_pattern_tendsto_zero q p hp hQ hDegree b c s)

theorem parameter_bernoulli_word_covariance_empty_left (n : ℕ) (p : ℝ≥0)
    (hp : p ≤ 1) (w : List Bool) : parameterBernoulliWordCovariance n p hp [] w = 0 := by
  simp [parameterBernoulliWordCovariance, parameterBernoulliWordTrace,
    parameterBernoulliWordMean, matrixAdjointWord, integral_const_mul]

theorem parameter_bernoulli_word_covariance_symm (n : ℕ) (p : ℝ≥0)
    (hp : p ≤ 1) (w v : List Bool) :
    parameterBernoulliWordCovariance n p hp w v = parameterBernoulliWordCovariance n p hp v w := by
  unfold parameterBernoulliWordCovariance
  simp only [mul_comm]

theorem parameter_bernoulli_all_word_covariance_tendsto_zero
    (q : ℕ → ℕ) (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hQ : Tendsto q atTop atTop)
    (hDegree : Tendsto (fun n => bernoulliEffectiveDegree (q n) (p n)) atTop atTop)
    (w v : List Bool) :
    Tendsto (fun n => parameterBernoulliWordCovariance (q n) (p n) (hp n) w v)
      atTop (𝓝 0) := by
  cases w with
  | nil => simpa only [parameter_bernoulli_word_covariance_empty_left] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | cons b w =>
    cases v with
    | nil => simpa only [parameter_bernoulli_word_covariance_symm _ _ _ (b :: w) [],
        parameter_bernoulli_word_covariance_empty_left] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | cons c v =>
      simpa only [List.ofFn_get] using
        parameter_bernoulli_nonempty_word_covariance_tendsto_zero q p hp hQ hDegree
          ((b :: w).get) ((c :: v).get)

end CircularLaw
