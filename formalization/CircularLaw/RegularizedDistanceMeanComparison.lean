import CircularLaw.RegularizedDistanceFourthMoment

/-!
# The complete two-sided Bernoulli mean comparison

For the actual positive-contraction regularized distance, scale at least
one gives `D/8 <= mu <= D`. The lower estimate uses the checked second
and fourth moments and an elementary pointwise moment inequality.
No concentration estimate or lower-mean premise is assumed.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

theorem nonnegative_second_fourth_moment_inequality {D f : ℝ} (hD : 0 ≤ D) (hf : 0 ≤ f) :
    36 * D ^ 2 * f ^ 2 ≤ 216 * D ^ 3 * f + f ^ 4 := by
  by_cases hSmall : f ≤ 6 * D
  · have hSquare : f ^ 2 ≤ 6 * D * f := by nlinarith
    have hProduct := mul_le_mul_of_nonneg_left hSquare (by positivity : 0 ≤ 36 * D ^ 2)
    nlinarith [pow_nonneg hf 4]
  · have hSquare : 36 * D ^ 2 ≤ f ^ 2 := by nlinarith
    have hProduct := mul_le_mul_of_nonneg_right hSquare (sq_nonneg f)
    have hPositive : 0 ≤ 216 * D ^ 3 * f := by positivity
    nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem regularizedDistanceMean_ge_scale_eighth {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1)
    (η : ℝ) (u : EuclideanSpace ℂ ι) (hScale : 1 ≤ regularizedDistanceScale P η u p) :
    regularizedDistanceScale P η u p / 8 ≤ regularizedDistanceMean P η u p hp := by
  let D := regularizedDistanceScale P η u p
  have hD : 0 < D := by dsimp [D]; linarith
  have hPointwise (x : ι → Bool) := nonnegative_second_fourth_moment_inequality
    hD.le (regularizedDistance_nonneg P η u (bernoulliCubeVector x))
  have hIntegral := integral_mono (μ := bernoulliCubeLaw ι p hp)
    Integrable.of_finite Integrable.of_finite hPointwise
  rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, regularizedDistance_bernoulli_second_moment hP.1,
    ← regularizedDistanceScale_sq hP.1 p hp η u] at hIntegral
  have hFourth := regularizedDistance_fourth_moment_le_scale hP p hp η u hScale
  change _ ≤ 9 * D ^ 4 at hFourth
  change 36 * D ^ 2 * D ^ 2 ≤ 216 * D ^ 3 * regularizedDistanceMean P η u p hp + _ at hIntegral
  have hFactor : D ^ 3 * (D - 8 * regularizedDistanceMean P η u p hp) ≤ 0 := by
    nlinarith
  have hLinear : D - 8 * regularizedDistanceMean P η u p hp ≤ 0 := by
    by_contra h
    have hPositive := mul_pos (pow_pos hD 3) (lt_of_not_ge h)
    exact (not_lt_of_ge hFactor) hPositive
  change D / 8 ≤ _
  linarith

theorem regularizedDistanceMean_comparison {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1)
    (η : ℝ) (u : EuclideanSpace ℂ ι) (hScale : 1 ≤ regularizedDistanceScale P η u p) :
    regularizedDistanceScale P η u p / 8 ≤ regularizedDistanceMean P η u p hp ∧
      regularizedDistanceMean P η u p hp ≤ regularizedDistanceScale P η u p :=
  ⟨regularizedDistanceMean_ge_scale_eighth hP p hp η u hScale,
    regularizedDistanceMean_le_scale hP.1 p hp η u⟩

end CircularLaw
