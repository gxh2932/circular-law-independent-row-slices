import CircularLaw.BernoulliQuadraticVariance

/-!
# The regularized-distance fourth-moment bound

The actual squared-distance fluctuation is the sum of the source
quadratic and linear terms. Their checked moments and `P^2 <= P`
give a dimension-free variance bound with constant 8. At scale at
least one the fourth moment is therefore at most nine times `D^4`.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixHermitian_quadratic_add {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (x u : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic P (x + u) = matrixEuclideanQuadratic P x +
      matrixEuclideanQuadratic P u + 2 * (⟪P.toEuclideanLin x, u⟫_ℂ).re := by
  have hSymm := Matrix.isHermitian_iff_isSymmetric.mp hP
  have hCross : (⟪P.toEuclideanLin u, x⟫_ℂ).re = (⟪P.toEuclideanLin x, u⟫_ℂ).re := by
    rw [hSymm]
    change RCLike.re (⟪u, P.toEuclideanLin x⟫_ℂ) = RCLike.re (⟪P.toEuclideanLin x, u⟫_ℂ)
    exact inner_re_symm _ _
  simp only [matrixEuclideanQuadratic, map_add, inner_add_left, inner_add_right, Complex.add_re]
  rw [hCross]
  ring

theorem regularizedDistance_squared_fluctuation {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (p : ℝ≥0) (η : ℝ) (u : EuclideanSpace ℂ ι) (x : ι → Bool) :
    regularizedDistance P η u (bernoulliCubeVector x) ^ 2 - regularizedDistanceScaleSq P η u p =
      regularizedDistanceQuadraticTerm P p x +
        regularizedDistanceLinearTerm P p (u + bernoulliMeanVector ι p) x := by
  rw [regularizedDistance_sq hP, bernoulliCubeVector_centered_shift p x u,
    matrixHermitian_quadratic_add hP.isHermitian]
  simp only [regularizedDistanceScaleSq, regularizedDistanceQuadraticTerm, regularizedDistanceLinearTerm]
  ring

theorem regularizedDistanceLinearTerm_mean {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (p : ℝ≥0) (hp : p ≤ 1) (u : EuclideanSpace ℂ ι) :
    (∫ x, regularizedDistanceLinearTerm P p u x ∂bernoulliCubeLaw ι p hp) = 0 := by
  simp_rw [regularizedDistanceLinearTerm_eq hP]
  exact bernoulliCenteredLinear_mean p hp _

theorem regularizedDistance_squared_fluctuation_second_moment_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1)
    (η : ℝ) (u : EuclideanSpace ℂ ι) :
    (∫ x, (regularizedDistance P η u (bernoulliCubeVector x) ^ 2 -
      regularizedDistanceScaleSq P η u p) ^ 2 ∂bernoulliCubeLaw ι p hp) ≤
      8 * regularizedDistanceScaleSq P η u p := by
  let u₀ := u + bernoulliMeanVector ι p
  let σ := p * (1 - (p : ℝ))
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hσ : 0 ≤ σ := mul_nonneg p.coe_nonneg (sub_nonneg.mpr h1)
  have hσUpper : σ ≤ 1 := by
    dsimp [σ]
    nlinarith [p.coe_nonneg, sq_nonneg (p : ℝ)]
  have hQ := regularizedDistanceQuadraticTerm_second_moment_le hP.1.isHermitian p hp
  have hQBound : (∫ x, regularizedDistanceQuadraticTerm P p x ^ 2 ∂bernoulliCubeLaw ι p hp) ≤
      σ * P.trace.re :=
    hQ.trans (mul_le_mul_of_nonneg_left (positiveContraction_trace_square_le hP) hσ)
  have hL := regularizedDistanceLinearTerm_variance_le hP p hp u₀
  rw [variance_of_integral_eq_zero (bernoulliCubeLaw_memLp p hp _ 2).aemeasurable
    (regularizedDistanceLinearTerm_mean hP.1.isHermitian p hp u₀)] at hL
  have hLBound : (∫ x, regularizedDistanceLinearTerm P p u₀ x ^ 2 ∂bernoulliCubeLaw ι p hp) ≤
      4 * matrixEuclideanQuadratic P u₀ := by
    apply hL.trans
    have hQuad := matrixEuclideanQuadratic_nonneg hP.1 u₀
    nlinarith [mul_le_mul_of_nonneg_right hσUpper hQuad]
  have hPointwise (x : ι → Bool) :
      (regularizedDistance P η u (bernoulliCubeVector x) ^ 2 - regularizedDistanceScaleSq P η u p) ^ 2 ≤
        2 * regularizedDistanceQuadraticTerm P p x ^ 2 + 2 * regularizedDistanceLinearTerm P p u₀ x ^ 2 := by
    rw [regularizedDistance_squared_fluctuation hP.1]
    change (_ + regularizedDistanceLinearTerm P p u₀ x) ^ 2 ≤ _
    nlinarith [sq_nonneg (regularizedDistanceQuadraticTerm P p x - regularizedDistanceLinearTerm P p u₀ x)]
  have hIntegral := integral_mono (μ := bernoulliCubeLaw ι p hp)
    Integrable.of_finite Integrable.of_finite hPointwise
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, integral_const_mul] at hIntegral
  have hTrace := positiveContraction_trace_nonneg hP
  have hQuad := matrixEuclideanQuadratic_nonneg hP.1 u₀
  change _ ≤ 8 * (η ^ 2 + σ * P.trace.re + matrixEuclideanQuadratic P u₀)
  nlinarith [mul_nonneg hσ hTrace, sq_nonneg η]

theorem regularizedDistance_square_variance_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1)
    (η : ℝ) (u : EuclideanSpace ℂ ι) :
    Var[fun x : ι → Bool => regularizedDistance P η u (bernoulliCubeVector x) ^ 2;
      bernoulliCubeLaw ι p hp] ≤ 8 * regularizedDistanceScaleSq P η u p := by
  rw [variance_eq_integral (bernoulliCubeLaw_memLp p hp _ 2).aemeasurable,
    regularizedDistance_bernoulli_second_moment hP.1]
  exact regularizedDistance_squared_fluctuation_second_moment_le hP p hp η u

theorem regularizedDistance_fourth_moment_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1)
    (η : ℝ) (u : EuclideanSpace ℂ ι) :
    (∫ x, regularizedDistance P η u (bernoulliCubeVector x) ^ 4 ∂bernoulliCubeLaw ι p hp) ≤
      regularizedDistanceScaleSq P η u p ^ 2 + 8 * regularizedDistanceScaleSq P η u p := by
  have hVar := regularizedDistance_square_variance_le hP p hp η u
  rw [variance_eq_sub (bernoulliCubeLaw_memLp p hp _ 2)] at hVar
  change (∫ x, (regularizedDistance P η u (bernoulliCubeVector x) ^ 2) ^ 2
    ∂bernoulliCubeLaw ι p hp) -
    (∫ x, regularizedDistance P η u (bernoulliCubeVector x) ^ 2 ∂bernoulliCubeLaw ι p hp) ^ 2 ≤ _ at hVar
  simp only [← pow_mul] at hVar
  rw [regularizedDistance_bernoulli_second_moment hP.1] at hVar
  linarith

theorem regularizedDistance_fourth_moment_le_scale {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1)
    (η : ℝ) (u : EuclideanSpace ℂ ι) (hScale : 1 ≤ regularizedDistanceScale P η u p) :
    (∫ x, regularizedDistance P η u (bernoulliCubeVector x) ^ 4 ∂bernoulliCubeLaw ι p hp) ≤
      9 * regularizedDistanceScale P η u p ^ 4 := by
  have h := regularizedDistance_fourth_moment_le hP p hp η u
  rw [← regularizedDistanceScale_sq hP.1 p hp η u] at h
  nlinarith [sq_nonneg (regularizedDistanceScale P η u p ^ 2 - 1)]

end CircularLaw
