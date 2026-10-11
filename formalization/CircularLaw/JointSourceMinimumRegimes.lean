import CircularLaw.BernoulliSourceMinimumProbability
import CircularLaw.LLYSourceMinimumRegimes

/-!
# Joint quantitative minimum estimates for the two actual matrix laws

One fixed choice of source parameters supplies both probabilities. The
radius conversions retain the full degree and spectral windows and give
the same logarithmic or polynomial exponent for both models.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

structure JointSourceMinimumParameters extends LLYSourceMinimumParameters where
  bernoulliUpper : (1 / bernoulliDegreeUpperRate) * 2 ≤ C

theorem joint_source_minimum_parameters_nonempty : Nonempty JointSourceMinimumParameters := by
  obtain ⟨p⟩ := lly_source_minimum_parameters_nonempty
  let C := max p.C ((1 / bernoulliDegreeUpperRate) * 2)
  have hC : p.C ≤ C := le_max_left _ _
  refine ⟨{
    C := C
    a₁ := p.a₁
    a₂ := p.a₂
    a₃ := p.a₃
    α := p.α
    degree := p.degree.trans hC
    firstEntropy := p.firstEntropy.trans hC
    firstFailure := p.firstFailure.trans hC
    columnFailure := p.columnFailure.trans hC
    firstPos := p.firstPos
    firstOne := p.firstOne
    secondPos := p.secondPos
    secondSmall := p.secondSmall
    thirdPos := p.thirdPos
    thirdSmall := p.thirdSmall
    firstCost := p.firstCost.trans (mul_le_mul_of_nonneg_right hC
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    entropy := p.entropy
    alphaPos := p.alphaPos
    alphaSmall := p.alphaSmall
    bernoulliUpper := le_max_right _ _
  }⟩

def bernoulliSourceMinimumErrorConstant (p : JointSourceMinimumParameters) : ℝ :=
  6 + (bernoulliScalarSmallBallConstant / Real.sqrt p.α + 6) / p.α

def jointSourceMinimumErrorConstant (p : JointSourceMinimumParameters) : ℝ :=
  llySourceMinimumErrorConstant p.toLLYSourceMinimumParameters +
    bernoulliSourceMinimumErrorConstant p

theorem joint_source_minimum_error_constant_pos (p : JointSourceMinimumParameters) :
    0 < jointSourceMinimumErrorConstant p := by
  have hSlice := lly_source_minimum_error_constant_pos p.toLLYSourceMinimumParameters
  have hBernoulli : 0 < bernoulliSourceMinimumErrorConstant p := by
    have hα := p.alphaPos
    have hScalar := bernoulli_scalar_small_ball_constant_pos
    unfold bernoulliSourceMinimumErrorConstant
    positivity
  exact add_pos hSlice hBernoulli

theorem eventually_joint_source_minimum_probability (p : JointSourceMinimumParameters) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, p.C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        smallestSingularFailureSum n d ζ
          ((llySourceAlmostRadius n d p.a₁ / Real.sqrt n) * llySourceAlmostRadius n d p.a₁ / Real.sqrt n)
          ((llySourceAlmostRadius n d p.a₁ / Real.sqrt n) * llySourceAlmostRadius n d p.a₁ / Real.sqrt n) ≤
            jointSourceMinimumErrorConstant p / Real.sqrt d := by
  filter_upwards [eventually_lly_source_parameter_minimum_probability p.toLLYSourceMinimumParameters,
    eventually_bernoulli_source_minimum_probability p.degree p.firstEntropy p.firstFailure
      p.bernoulliUpper p.firstPos p.firstOne p.secondPos p.secondSmall p.thirdPos p.thirdSmall
      p.firstCost p.entropy p.alphaPos p.alphaSmall] with n hSlice hBernoulli
  intro d hDegree hSize ζ hShift
  have hA := hSlice d hDegree hSize ζ hShift
  have hB := hBernoulli d hDegree hSize ζ hShift
  have hALaw : (rowSliceMatrixLaw n d).real {rows |
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
        ((llySourceAlmostRadius n d p.a₁ / Real.sqrt n) * llySourceAlmostRadius n d p.a₁ / Real.sqrt n)} ≤
      llySourceMinimumErrorConstant p.toLLYSourceMinimumParameters / Real.sqrt d := by
    simpa only [rowSliceMatrixLaw, finiteUniformMeasure_real] using hA
  unfold smallestSingularFailureSum jointSourceMinimumErrorConstant
  rw [add_div]
  exact add_le_add hALaw hB

theorem eventually_joint_source_lower_cutoff_probability (p : JointSourceMinimumParameters) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, p.C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        smallestSingularFailureSum n d ζ
          (lowerHermitizationCutoff n (2 * llySourceLoglogRatioConstant + 12))
          (lowerHermitizationCutoff n (2 * llySourceLoglogRatioConstant + 12)) ≤
            jointSourceMinimumErrorConstant p / Real.sqrt d := by
  filter_upwards [eventually_joint_source_minimum_probability p,
    eventually_lly_source_lower_cutoff_radius p.degree p.firstPos p.firstOne] with n hBound hRadius
  intro d hDegree hSize ζ hShift
  haveI := rowSliceMatrixLaw_probability (by omega : d ≤ n)
  apply le_trans _ (hBound d hDegree hSize ζ hShift)
  unfold smallestSingularFailureSum
  apply add_le_add <;> apply measureReal_mono (h₂ := by finiteness) <;>
    rintro sample ⟨j, hj⟩ <;> exact ⟨j, hj.trans (hRadius d hDegree (by omega : d ≤ n))⟩

theorem eventually_joint_source_superlog_probability (p : JointSourceMinimumParameters)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (Real.log (n : ℝ)) ^ (1 + ε) ≤ (d : ℝ) → 2 * d ≤ n →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          smallestSingularFailureSum n d ζ
            (polynomialHermitizationCutoff n (2 * (8 * (1 + ε) / ε) + 12))
            (polynomialHermitizationCutoff n (2 * (8 * (1 + ε) / ε) + 12)) ≤
              jointSourceMinimumErrorConstant p / Real.sqrt d := by
  filter_upwards [eventually_joint_source_minimum_probability p,
    eventually_lly_source_superlog_cutoff_radius p.degree p.firstPos p.firstOne hε,
    eventually_superlog_implies_any_log_degree p.C hε] with n hBound hRadius hLower
  intro d hDegree hSize ζ hShift
  haveI := rowSliceMatrixLaw_probability (by omega : d ≤ n)
  have hLogDegree := hLower d hDegree
  apply le_trans _ (hBound d hLogDegree hSize ζ hShift)
  unfold smallestSingularFailureSum
  apply add_le_add <;> apply measureReal_mono (h₂ := by finiteness) <;>
    rintro sample ⟨j, hj⟩ <;> exact ⟨j, hj.trans (hRadius d hLogDegree (by omega : d ≤ n) hDegree)⟩

end CircularLaw
