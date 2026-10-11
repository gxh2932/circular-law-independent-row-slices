import CircularLaw.RegularizedDistanceMean

/-!
# Exact linear variance in the positive-contraction argument

The real centered Bernoulli linear form has variance `p(1-p)` times
the squared coefficient norm. Applied to the actual Hermitian cross
term, this is precisely the source's linear variance identity, bounded
by the quadratic form of `P^2` and then by that of `P`.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliCenteredLinear (p : ℝ≥0) (a : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, a i * bernoulliCenteredValue p (x i)

omit [DecidableEq ι] in
theorem bernoulliCenteredLinear_mean (p : ℝ≥0) (hp : p ≤ 1) (a : ι → ℝ) :
    (∫ x, bernoulliCenteredLinear p a x ∂bernoulliCubeLaw ι p hp) = 0 := by
  simp only [bernoulliCenteredLinear]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_const_mul, bernoulliCubeLaw_centered_coordinate_mean,
    mul_zero, Finset.sum_const_zero]

theorem bernoulliCenteredLinear_second_moment (p : ℝ≥0) (hp : p ≤ 1) (a : ι → ℝ) :
    (∫ x, bernoulliCenteredLinear p a x ^ 2 ∂bernoulliCubeLaw ι p hp) =
      p * (1 - (p : ℝ)) * ∑ i, a i ^ 2 := by
  have hExpand (x : ι → Bool) : bernoulliCenteredLinear p a x ^ 2 =
      ∑ i, ∑ j, (a i * a j) *
        (bernoulliCenteredValue p (x i) * bernoulliCenteredValue p (x j)) := by
    simp only [bernoulliCenteredLinear, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hExpand]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite), integral_const_mul,
    bernoulliCubeLaw_centered_coordinate_product]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bernoulliCenteredLinear_variance (p : ℝ≥0) (hp : p ≤ 1) (a : ι → ℝ) :
    Var[bernoulliCenteredLinear p a; bernoulliCubeLaw ι p hp] =
      p * (1 - (p : ℝ)) * ∑ i, a i ^ 2 := by
  rw [variance_eq_sub (bernoulliCubeLaw_memLp p hp _ 2)]
  change (∫ x, bernoulliCenteredLinear p a x ^ 2 ∂bernoulliCubeLaw ι p hp) -
    (∫ x, bernoulliCenteredLinear p a x ∂bernoulliCubeLaw ι p hp) ^ 2 = _
  rw [bernoulliCenteredLinear_second_moment, bernoulliCenteredLinear_mean]
  ring

def regularizedDistanceLinearTerm (P : Matrix ι ι ℂ) (p : ℝ≥0)
    (u : EuclideanSpace ℂ ι) (x : ι → Bool) : ℝ :=
  2 * (⟪P.toEuclideanLin (bernoulliCenteredVector p x), u⟫_ℂ).re

theorem regularizedDistanceLinearTerm_eq {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (p : ℝ≥0) (u : EuclideanSpace ℂ ι) (x : ι → Bool) :
    regularizedDistanceLinearTerm P p u x =
      bernoulliCenteredLinear p (fun i => 2 * (P.toEuclideanLin u i).re) x := by
  rw [regularizedDistanceLinearTerm, Matrix.isHermitian_iff_isSymmetric.mp hP,
    PiLp.inner_apply, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bernoulliCenteredVector, RCLike.inner_apply, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem regularizedDistanceLinearTerm_variance {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (p : ℝ≥0) (hp : p ≤ 1) (u : EuclideanSpace ℂ ι) :
    Var[regularizedDistanceLinearTerm P p u; bernoulliCubeLaw ι p hp] =
      4 * (p * (1 - (p : ℝ))) * ∑ i, (P.toEuclideanLin u i).re ^ 2 := by
  have hEq := funext (regularizedDistanceLinearTerm_eq hP p u)
  rw [hEq, bernoulliCenteredLinear_variance]
  simp only [mul_pow]
  rw [← Finset.mul_sum]
  ring

theorem matrixHermitian_action_norm_sq {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (u : EuclideanSpace ℂ ι) :
    ‖P.toEuclideanLin u‖ ^ 2 = matrixEuclideanQuadratic (P * P) u := by
  have hSymm := Matrix.isHermitian_iff_isSymmetric.mp hP
  rw [matrixEuclideanQuadratic, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply, hSymm]
  simp only [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem regularizedDistanceLinearTerm_variance_le_square {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (p : ℝ≥0) (hp : p ≤ 1) (u : EuclideanSpace ℂ ι) :
    Var[regularizedDistanceLinearTerm P p u; bernoulliCubeLaw ι p hp] ≤
      4 * (p * (1 - (p : ℝ))) * matrixEuclideanQuadratic (P * P) u := by
  rw [regularizedDistanceLinearTerm_variance hP, ← matrixHermitian_action_norm_sq hP,
    EuclideanSpace.norm_sq_eq]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro i _
    have hNorm : ‖P.toEuclideanLin u i‖ ^ 2 =
        (P.toEuclideanLin u i).re ^ 2 + (P.toEuclideanLin u i).im ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [sq_nonneg (P.toEuclideanLin u i).im]
  · have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
    exact mul_nonneg (by norm_num) (mul_nonneg p.coe_nonneg (sub_nonneg.mpr h1))

theorem regularizedDistanceLinearTerm_variance_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (p : ℝ≥0) (hp : p ≤ 1) (u : EuclideanSpace ℂ ι) :
    Var[regularizedDistanceLinearTerm P p u; bernoulliCubeLaw ι p hp] ≤
      4 * (p * (1 - (p : ℝ))) * matrixEuclideanQuadratic P u := by
  apply (regularizedDistanceLinearTerm_variance_le_square hP.1.isHermitian p hp u).trans
  apply mul_le_mul_of_nonneg_left (positiveContraction_squared_quadratic_le hP u)
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  exact mul_nonneg (by norm_num) (mul_nonneg p.coe_nonneg (sub_nonneg.mpr h1))

end CircularLaw
