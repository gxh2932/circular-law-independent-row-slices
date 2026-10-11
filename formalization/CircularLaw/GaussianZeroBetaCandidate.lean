import CircularLaw.BetaCatalanMoments

/-!
# An explicit beta candidate for the zero-shift squared singular law

The beta(1/2,3/2) variable, scaled by four, is placed in the same compact
interval used by the actual Gaussian moment construction. Its clipping
outside the beta support is irrelevant almost everywhere. Every actual
moment is the corresponding Catalan number.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace CircularLaw

def gaussianZeroBetaBase : Measure ℝ := betaMeasure (1 / 2) (3 / 2)

instance gaussianZeroBetaBase_probability : IsProbabilityMeasure gaussianZeroBetaBase :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

def gaussianZeroBetaSquaredMap (x : ℝ) : Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2) :=
  ⟨max 0 (min 4 (4 * x)), by
    constructor
    · exact le_max_left _ _
    · apply le_trans (max_le (by norm_num) (min_le_left _ _))
      norm_num⟩

theorem continuous_gaussian_zero_beta_squared_map : Continuous gaussianZeroBetaSquaredMap := by
  apply Continuous.subtype_mk
  fun_prop

theorem gaussian_zero_beta_squared_map_ae :
    ∀ᵐ x ∂gaussianZeroBetaBase, (gaussianZeroBetaSquaredMap x : ℝ) = 4 * x := by
  filter_upwards [beta_measure_ae_unit_interval (1 / 2) (3 / 2)] with x hx
  change max 0 (min 4 (4 * x)) = 4 * x
  rw [min_eq_right (by linarith : (4 : ℝ) * x ≤ 4), max_eq_right (by linarith : (0 : ℝ) ≤ 4 * x)]

def gaussianZeroBetaSquaredCandidate : ProbabilityMeasure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)) :=
  ProbabilityMeasure.map (⟨gaussianZeroBetaBase, inferInstance⟩ : ProbabilityMeasure ℝ)
    continuous_gaussian_zero_beta_squared_map.measurable.aemeasurable

theorem gaussian_zero_beta_squared_candidate_moments (k : ℕ) :
    (∫ t, (t : ℝ) ^ k
      ∂(gaussianZeroBetaSquaredCandidate : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)))) =
        (catalan k : ℝ) := by
  change (∫ t, (t : ℝ) ^ k ∂gaussianZeroBetaBase.map gaussianZeroBetaSquaredMap) = _
  rw [integral_map_of_stronglyMeasurable continuous_gaussian_zero_beta_squared_map.measurable
    (continuous_subtype_val.pow k).measurable.stronglyMeasurable]
  calc
    _ = ∫ x, ((4 : ℝ) * x) ^ k ∂gaussianZeroBetaBase :=
      integral_congr_ae (gaussian_zero_beta_squared_map_ae.mono (fun _ h => congrArg (fun t : ℝ => t ^ k) h))
    _ = _ := beta_scaled_half_power_integral k

theorem gaussian_zero_shift_original_moment_limit_catalan (k : ℕ) :
    gaussianZeroShiftMomentLimit k = (catalan k : ℝ) := by
  cases k with
  | zero => simp only [gaussian_zero_shift_moment_limit_zero, catalan_zero, Nat.cast_one]
  | succ k => rw [gaussian_zero_shift_moment_limit_succ, gaussian_leading_moment_count_catalan]

theorem gaussian_zero_beta_squared_candidate_actual_moments (k : ℕ) :
    (∫ t, (t : ℝ) ^ k
      ∂(gaussianZeroBetaSquaredCandidate : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)))) =
        gaussianZeroShiftMomentLimit k := by
  rw [gaussian_zero_beta_squared_candidate_moments, gaussian_zero_shift_original_moment_limit_catalan]

def gaussianZeroBetaSingularCandidate : Measure ℝ≥0 :=
  (gaussianZeroBetaSquaredCandidate : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))).map
    (fun t : Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2) => nonnegativeRealSquareRoot (t : ℝ))

instance gaussianZeroBetaSingularCandidate_probability :
    IsProbabilityMeasure gaussianZeroBetaSingularCandidate :=
  (gaussianZeroBetaSquaredCandidate : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))).isProbabilityMeasure_map
    (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable.aemeasurable

end CircularLaw
