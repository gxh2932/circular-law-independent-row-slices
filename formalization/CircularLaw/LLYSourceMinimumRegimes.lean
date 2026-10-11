import CircularLaw.LLYSourceMinimumProbability
import CircularLaw.LLYSourceRadiusRegimes

/-!
# Actual row-slice minimum bounds at both manuscript degree scales

A fixed, existing choice of numerical parameters supplies both estimates.
The Bernoulli minimum bound is still a separate obligation for the joint
manuscript results.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

structure LLYSourceMinimumParameters where
  C : ℝ
  a₁ : ℝ
  a₂ : ℝ
  a₃ : ℝ
  α : ℝ
  degree : 1920000 ≤ C
  firstEntropy : 16 / uniqueWitnessRate ^ 2 ≤ C
  firstFailure : (2 / uniqueWitnessRate) * 2 ≤ C
  columnFailure : (1 / (2 * sliceTailRate)) * 2 ≤ C
  firstPos : 0 < a₁
  firstOne : a₁ ≤ 1
  secondPos : 0 < a₂
  secondSmall : a₂ ≤ 1 / 1000
  thirdPos : 0 < a₃
  thirdSmall : a₃ ≤ 1 / 4096
  firstCost : 12288 * a₁ ≤ C * Real.log 2
  entropy : smallSetEntropy a₃ ≤ rowLoadRate / 4
  alphaPos : 0 < α
  alphaSmall : α ≤ a₃ / 2

theorem lly_source_minimum_parameters_nonempty : Nonempty LLYSourceMinimumParameters := by
  obtain ⟨a, ha, _, hEntropy⟩ := small_set_entropy_threshold
    (div_pos rowLoadRate_pos (by norm_num : (0 : ℝ) < 4))
  let a₃ : ℝ := min a (1 / 4096)
  have ha₃ : 0 < a₃ := lt_min ha (by norm_num)
  have ha₃Small : a₃ ≤ 1 / 4096 := min_le_right _ _
  let C : ℝ := max 1920000 (max (16 / uniqueWitnessRate ^ 2)
    (max (4 / uniqueWitnessRate) (max (1 / sliceTailRate) (12288 / Real.log 2))))
  have hC : 1920000 ≤ C := le_max_left _ _
  have hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hFirstFailure : 4 / uniqueWitnessRate ≤ C := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hColumnFailure : 1 / sliceTailRate ≤ C := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hSourceCost : 12288 / Real.log 2 ≤ C := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨{
    C := C
    a₁ := 1
    a₂ := a₃
    a₃ := a₃
    α := a₃ / 4
    degree := hC
    firstEntropy := hEntropyCost
    firstFailure := ?_
    columnFailure := ?_
    firstPos := by norm_num
    firstOne := le_rfl
    secondPos := ha₃
    secondSmall := ?_
    thirdPos := ha₃
    thirdSmall := ha₃Small
    firstCost := ?_
    entropy := ?_
    alphaPos := by positivity
    alphaSmall := by linarith only [ha₃]
  }⟩
  · convert hFirstFailure using 1
    ring
  · convert hColumnFailure using 1
    field_simp
  · linarith only [ha₃Small]
  · norm_num only [mul_one]
    exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hSourceCost
  · exact hEntropy a₃ ha₃ (min_le_left _ _)

def llySourceMinimumErrorConstant (p : LLYSourceMinimumParameters) : ℝ :=
  5 + (sliceSmallBallDegreeConstant p.α + 4) / p.α

theorem lly_source_minimum_error_constant_pos (p : LLYSourceMinimumParameters) :
    0 < llySourceMinimumErrorConstant p := by
  have hα := p.alphaPos
  have hConstant := slice_small_ball_degree_constant_pos hα
  unfold llySourceMinimumErrorConstant
  positivity

theorem eventually_lly_source_parameter_minimum_probability (p : LLYSourceMinimumParameters) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, p.C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
            ((llySourceAlmostRadius n d p.a₁ / Real.sqrt n) * llySourceAlmostRadius n d p.a₁ / Real.sqrt n)) ≤
              llySourceMinimumErrorConstant p / Real.sqrt d :=
  eventually_lly_source_row_slice_minimum_probability p.degree p.firstEntropy p.firstFailure
    p.columnFailure p.firstPos p.firstOne p.secondPos p.secondSmall p.thirdPos p.thirdSmall
    p.firstCost p.entropy p.alphaPos p.alphaSmall

theorem eventually_lly_source_lower_cutoff_probability (p : LLYSourceMinimumParameters) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, p.C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
            (lowerHermitizationCutoff n (2 * llySourceLoglogRatioConstant + 12))) ≤
              llySourceMinimumErrorConstant p / Real.sqrt d := by
  filter_upwards [eventually_lly_source_parameter_minimum_probability p,
    eventually_lly_source_lower_cutoff_radius p.degree p.firstPos p.firstOne]
      with n hProbability hRadius
  intro d hDegree hSize ζ hShift
  apply (uniformProbability_mono ?_).trans (hProbability d hDegree hSize ζ hShift)
  intro rows hFail
  obtain ⟨j, hj⟩ := hFail
  exact ⟨j, hj.trans (hRadius d hDegree (by omega : d ≤ n))⟩

theorem eventually_lly_source_superlog_cutoff_probability (p : LLYSourceMinimumParameters)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, p.C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
              (polynomialHermitizationCutoff n (2 * (8 * (1 + ε) / ε) + 12))) ≤
                llySourceMinimumErrorConstant p / Real.sqrt d := by
  filter_upwards [eventually_lly_source_parameter_minimum_probability p,
    eventually_lly_source_superlog_cutoff_radius p.degree p.firstPos p.firstOne hε]
      with n hProbability hRadius
  intro d hDegree hSize hLower ζ hShift
  apply (uniformProbability_mono ?_).trans (hProbability d hDegree hSize ζ hShift)
  intro rows hFail
  obtain ⟨j, hj⟩ := hFail
  exact ⟨j, hj.trans (hRadius d hDegree (by omega : d ≤ n) hLower)⟩

theorem eventually_superlog_implies_any_log_degree (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) → C * Real.log (n : ℝ) ≤ d := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hPower := (tendsto_rpow_atTop hε).comp hLog
  filter_upwards [hLog.eventually_gt_atTop 0, hPower.eventually_ge_atTop C] with n hLogN hC
  change 0 < Real.log (n : ℝ) at hLogN
  change C ≤ (Real.log (n : ℝ)) ^ ε at hC
  intro d hLower
  have hScaled := mul_le_mul_of_nonneg_right hC hLogN.le
  apply le_trans _ hLower
  rw [Real.rpow_add hLogN, Real.rpow_one]
  nlinarith only [hScaled]

theorem eventually_lly_source_superlog_probability (p : LLYSourceMinimumParameters)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) → 2 * d ≤ n →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
              (polynomialHermitizationCutoff n (2 * (8 * (1 + ε) / ε) + 12))) ≤
                llySourceMinimumErrorConstant p / Real.sqrt d := by
  filter_upwards [eventually_lly_source_superlog_cutoff_probability p hε,
    eventually_superlog_implies_any_log_degree p.C hε] with n hProbability hDegree
  intro d hLower hSize ζ hShift
  exact hProbability d (hDegree d hLower) hSize hLower ζ hShift

theorem row_slice_lower_cutoff_minimum_absolute_constants :
    ∃ C D CL : ℝ, 0 < C ∧ 0 < D ∧ 0 < CL ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) (lowerHermitizationCutoff n CL)) ≤
              D / Real.sqrt d := by
  obtain ⟨p⟩ := lly_source_minimum_parameters_nonempty
  refine ⟨p.C, llySourceMinimumErrorConstant p, 2 * llySourceLoglogRatioConstant + 12,
    by linarith only [p.degree], lly_source_minimum_error_constant_pos p, ?_,
    eventually_lly_source_lower_cutoff_probability p⟩
  linarith only [lly_source_loglog_ratio_constant_ge_eight]

theorem row_slice_superlog_minimum_absolute_constants :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 2 < B ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
        (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) → 2 * d ≤ n →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
            uniformProbability (fun rows : RowSliceMatrix n d =>
              squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) (polynomialHermitizationCutoff n B)) ≤
                D / Real.sqrt d := by
  obtain ⟨p⟩ := lly_source_minimum_parameters_nonempty
  refine ⟨llySourceMinimumErrorConstant p, lly_source_minimum_error_constant_pos p, ?_⟩
  intro ε hε
  refine ⟨2 * (8 * (1 + ε) / ε) + 12, ?_, eventually_lly_source_superlog_probability p hε⟩
  have hPos : 0 < 8 * (1 + ε) / ε := by positivity
  linarith only [hPos]

end CircularLaw
