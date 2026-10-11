import CircularLaw.ComplexGaussianMoments

/-!
# Rotation and exact mixed moments of the standard complex Gaussian

Characteristic functions prove rotation invariance for the actual law.
A unit rotation with a prescribed nontrivial power then annihilates
every unbalanced mixed monomial; balanced moments are factorials.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem standard_complex_gaussian_unit_mul_law (c : ℂ) (hc : ‖c‖ = 1) :
    standardComplexGaussianLaw.map (fun z : ℂ => c * z) = standardComplexGaussianLaw := by
  let M : ℂ →L[ℝ] ℂ := (c • (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ
  have hFun : (fun z : ℂ => c * z) = M := rfl
  have hMApply (z : ℂ) : M z = c * z := rfl
  rw [hFun]
  haveI : IsProbabilityMeasure (standardComplexGaussianLaw.map M) :=
    Measure.isProbabilityMeasure_map M.measurable.aemeasurable
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, standardComplexGaussianLaw_charFunDual,
    standardComplexGaussianLaw_charFunDual]
  have hCoeff := complex_realForm_rotated_norm_sq L c
  rw [hc, one_pow, mul_one] at hCoeff
  simp only [ContinuousLinearMap.comp_apply, hMApply, mul_one]
  rw [mul_comm c Complex.I, hCoeff]

def gaussianMomentRotation (k : ℕ) : ℂ :=
  Complex.exp ((Real.pi / (k : ℝ) : ℂ) * Complex.I)

theorem gaussian_moment_rotation_norm (k : ℕ) : ‖gaussianMomentRotation k‖ = 1 := by
  simp [gaussianMomentRotation, Complex.norm_exp, Complex.mul_re]

theorem gaussian_moment_rotation_power {k : ℕ} (hk : 0 < k) :
    gaussianMomentRotation k ^ k = -1 := by
  rw [gaussianMomentRotation, ← Complex.exp_nat_mul]
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hAngle : (k : ℂ) * ((Real.pi / (k : ℝ) : ℂ) * Complex.I) =
      (Real.pi : ℂ) * Complex.I := by
    have hkComplex : (k : ℂ) ≠ 0 := by exact_mod_cast hkReal
    push_cast
    field_simp [hkComplex]
  rw [hAngle, Complex.exp_pi_mul_I]

theorem unit_mul_mixed_power_factor (c z : ℂ) (p q : ℕ) :
    (c * z) ^ p * star (c * z) ^ q =
      (c ^ p * star c ^ q) * (z ^ p * star z ^ q) := by
  simp only [mul_pow, star_mul]
  ring

theorem unit_mixed_power_factor_of_le (c : ℂ) (hc : ‖c‖ = 1) {p q : ℕ} (hpq : q ≤ p) :
    c ^ p * star c ^ q = c ^ (p - q) := by
  have hUnit : c * star c = 1 := by
    change c * (starRingEnd ℂ) c = 1
    rw [Complex.mul_conj', hc]
    norm_num
  conv_lhs => rw [show p = (p - q) + q by omega, pow_add]
  calc
    (c ^ (p - q) * c ^ q) * star c ^ q = c ^ (p - q) * (c * star c) ^ q := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hUnit, one_pow, mul_one]

theorem standard_complex_gaussian_mixed_moment_zero_of_lt {p q : ℕ} (hpq : q < p) :
    (∫ z : ℂ, z ^ p * star z ^ q ∂standardComplexGaussianLaw) = 0 := by
  let c : ℂ := gaussianMomentRotation (p - q)
  have hc : ‖c‖ = 1 := gaussian_moment_rotation_norm _
  have hRotate : (∫ z : ℂ, (c * z) ^ p * star (c * z) ^ q ∂standardComplexGaussianLaw) =
      ∫ z : ℂ, z ^ p * star z ^ q ∂standardComplexGaussianLaw := by
    rw [← integral_map (by fun_prop : AEMeasurable (fun z : ℂ => c * z)
      standardComplexGaussianLaw) (by fun_prop : AEStronglyMeasurable
        (fun z : ℂ => z ^ p * star z ^ q)
          (standardComplexGaussianLaw.map (fun z : ℂ => c * z))),
      standard_complex_gaussian_unit_mul_law c hc]
  simp only [unit_mul_mixed_power_factor, integral_const_mul] at hRotate
  rw [unit_mixed_power_factor_of_le c hc hpq.le,
    gaussian_moment_rotation_power (by omega : 0 < p - q), neg_one_mul] at hRotate
  have hZero : (2 : ℂ) * (∫ z : ℂ, z ^ p * star z ^ q ∂standardComplexGaussianLaw) = 0 := by
    linear_combination -hRotate
  exact (mul_eq_zero.mp hZero).resolve_left (by norm_num)

theorem standard_complex_gaussian_mixed_moment_conj (p q : ℕ) :
    (∫ z : ℂ, z ^ q * star z ^ p ∂standardComplexGaussianLaw) =
      star (∫ z : ℂ, z ^ p * star z ^ q ∂standardComplexGaussianLaw) := by
  have hStar := integral_conj (𝕜 := ℂ) (μ := standardComplexGaussianLaw)
    (f := fun z : ℂ => z ^ p * star z ^ q)
  change (∫ z : ℂ, star (z ^ p * star z ^ q) ∂standardComplexGaussianLaw) =
    star (∫ z : ℂ, z ^ p * star z ^ q ∂standardComplexGaussianLaw) at hStar
  rw [← hStar]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [star_mul, star_pow, star_star]

theorem standard_complex_gaussian_mixed_moment (p q : ℕ) :
    (∫ z : ℂ, z ^ p * star z ^ q ∂standardComplexGaussianLaw) =
      if p = q then (p.factorial : ℂ) else 0 := by
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne, standard_complex_gaussian_mixed_moment_conj,
      standard_complex_gaussian_mixed_moment_zero_of_lt h, star_zero]
  · subst q
    rw [if_pos rfl, standard_complex_gaussian_balanced_moment]
  · rw [if_neg h.ne', standard_complex_gaussian_mixed_moment_zero_of_lt h]

end CircularLaw
