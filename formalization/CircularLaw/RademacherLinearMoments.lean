import CircularLaw.BernoulliQuadraticVariance

/-!
# The mean norm of an actual complex Rademacher sum

The fair Bernoulli cube supplies independent signs. The existing exact
quadratic variance computation gives a fourth-moment bound for any complex
linear form. A polynomial moment inequality then bounds its mean norm
below by one eighth of its coefficient Euclidean norm. This supplies the
probabilistic input for constructing a coordinate-spread basis.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def rademacherValue (b : Bool) : ℂ := cond b 1 (-1)

def rademacherLinearForm {ι : Type*} [Fintype ι] (a : ι → ℂ) (x : ι → Bool) : ℂ :=
  ∑ i, a i * rademacherValue (x i)

def rademacherGram {ι : Type*} (a : ι → ℂ) : Matrix ι ι ℂ := fun i j => star (a i) * a j

theorem rademacher_gram_hermitian {ι : Type*} (a : ι → ℂ) :
    (rademacherGram a).IsHermitian := by
  ext i j
  simp [rademacherGram, Matrix.conjTranspose_apply, mul_comm]

theorem rademacher_gram_trace {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (rademacherGram a).trace.re = ∑ i, ‖a i‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, rademacherGram, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem rademacher_gram_square_trace {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (rademacherGram a * rademacherGram a).trace.re = (∑ i, ‖a i‖ ^ 2) ^ 2 := by
  rw [matrixHermitian_trace_square (rademacher_gram_hermitian a)]
  simp only [rademacherGram, norm_mul, norm_star, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← pow_two]

theorem rademacher_gram_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic (rademacherGram a) v = ‖∑ i, a i * v i‖ ^ 2 := by
  rw [matrixEuclideanQuadratic_sum_entries]
  calc
    _ = (star (∑ i, a i * v i) * (∑ i, a i * v i)).re := by
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, Complex.re_sum,
        rademacherGram]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ = _ := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem rademacher_linear_form_centered {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (x : ι → Bool) :
    rademacherLinearForm a x = (2 : ℂ) * ∑ i, a i * (bernoulliCenteredValue (1 / 2) (x i) : ℂ) := by
  rw [rademacherLinearForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [rademacherValue, bernoulliCenteredValue] <;> ring

theorem rademacher_centered_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (x : ι → Bool) :
    matrixEuclideanQuadratic (rademacherGram a) (bernoulliCenteredVector (1 / 2) x) =
      ‖rademacherLinearForm a x‖ ^ 2 / 4 := by
  rw [rademacher_gram_quadratic, rademacher_linear_form_centered, norm_mul, mul_pow]
  simp only [bernoulliCenteredVector, PiLp.toLp_apply, Complex.norm_ofNat]
  ring

theorem rademacher_linear_form_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) :
    (∫ x, ‖rademacherLinearForm a x‖ ^ 2 ∂bernoulliCubeLaw ι (1 / 2) (by norm_num)) =
      ∑ i, ‖a i‖ ^ 2 := by
  have hMean := bernoulli_centered_quadratic_expectation (1 / 2) (by norm_num) (rademacherGram a) 0
  simp only [add_zero] at hMean
  have hZero : matrixEuclideanQuadratic (rademacherGram a) 0 = 0 := by
    simp [matrixEuclideanQuadratic]
  rw [hZero, add_zero, rademacher_gram_trace] at hMean
  simp_rw [rademacher_centered_quadratic] at hMean
  rw [integral_div] at hMean
  norm_num at hMean
  linarith

theorem rademacher_linear_form_fourth_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) :
    (∫ x, ‖rademacherLinearForm a x‖ ^ 4 ∂bernoulliCubeLaw ι (1 / 2) (by norm_num)) ≤
      5 * (∑ i, ‖a i‖ ^ 2) ^ 2 := by
  let E := ∑ i, ‖a i‖ ^ 2
  have hVariance := regularizedDistanceQuadraticTerm_second_moment_le
    (rademacher_gram_hermitian a) (1 / 2) (by norm_num)
  have hExpand (x : ι → Bool) : regularizedDistanceQuadraticTerm (rademacherGram a) (1 / 2) x ^ 2 =
      ‖rademacherLinearForm a x‖ ^ 4 / 16 - E * ‖rademacherLinearForm a x‖ ^ 2 / 8 + E ^ 2 / 16 := by
    simp only [regularizedDistanceQuadraticTerm, rademacher_centered_quadratic,
      rademacher_gram_trace, NNReal.coe_div, NNReal.coe_one]
    change (‖rademacherLinearForm a x‖ ^ 2 / 4 - (1 / 2 : ℝ) * (1 - 1 / 2) * E) ^ 2 = _
    ring
  simp_rw [hExpand] at hVariance
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_div, integral_div, integral_const_mul,
    rademacher_linear_form_second_moment, integral_const,
    probReal_univ, one_smul, rademacher_gram_square_trace] at hVariance
  norm_num at hVariance
  change _ ≤ 5 * E ^ 2
  change _ ≤ _ * E ^ 2 at hVariance
  linarith

theorem polynomial_mean_norm_lower {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : ∀ x, 0 ≤ X x) {s : ℝ} (hs : 0 < s)
    (hSecond : (∫ x, X x ^ 2 ∂μ) = s ^ 2)
    (hFourth : (∫ x, X x ^ 4 ∂μ) ≤ 5 * s ^ 4) :
    s / 8 ≤ ∫ x, X x ∂μ := by
  have hPoint (x : Ω) : 16 * s ^ 2 * X x ^ 2 ≤ 64 * s ^ 3 * X x + X x ^ 4 := by
    have hxNonneg := hX x
    by_cases hx : X x ≤ 4 * s
    · have hProduct := mul_nonneg (by positivity : 0 ≤ 16 * s ^ 2 * X x) (sub_nonneg.mpr hx)
      nlinarith [sq_nonneg (X x ^ 2)]
    · have hxLarge : 4 * s < X x := lt_of_not_ge hx
      have hSquare : 16 * s ^ 2 ≤ X x ^ 2 := by nlinarith [hX x]
      have hProduct := mul_le_mul_of_nonneg_right hSquare (sq_nonneg (X x))
      have hPositive : 0 ≤ 64 * s ^ 3 * X x := by positivity
      nlinarith
  have hIntegral := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hPoint
  rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, hSecond] at hIntegral
  have hMoment : 11 * s ^ 4 ≤ 64 * s ^ 3 * (∫ x, X x ∂μ) := by nlinarith
  have hCube : 0 < s ^ 3 := pow_pos hs 3
  have hCancel : 11 * s ≤ 64 * (∫ x, X x ∂μ) := by
    apply (mul_le_mul_iff_of_pos_right hCube).mp
    nlinarith only [hMoment]
  linarith

theorem rademacher_linear_form_mean_norm_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) :
    Real.sqrt (∑ i, ‖a i‖ ^ 2) / 8 ≤
      ∫ x, ‖rademacherLinearForm a x‖ ∂bernoulliCubeLaw ι (1 / 2) (by norm_num) := by
  have hEnergy : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hZero : (∑ i, ‖a i‖ ^ 2) = 0
  · rw [hZero, Real.sqrt_zero, zero_div]
    exact integral_nonneg (fun _ => norm_nonneg _)
  · have hPositive : 0 < ∑ i, ‖a i‖ ^ 2 := lt_of_le_of_ne hEnergy (Ne.symm hZero)
    apply polynomial_mean_norm_lower _ _ (fun _ => norm_nonneg _)
      (Real.sqrt_pos.mpr hPositive)
    · rw [rademacher_linear_form_second_moment, Real.sq_sqrt hEnergy]
    · have hBound := rademacher_linear_form_fourth_moment a
      rw [show Real.sqrt (∑ i, ‖a i‖ ^ 2) ^ 4 =
        (Real.sqrt (∑ i, ‖a i‖ ^ 2) ^ 2) ^ 2 by ring, Real.sq_sqrt hEnergy]
      exact hBound

end CircularLaw
