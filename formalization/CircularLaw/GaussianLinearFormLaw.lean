import CircularLaw.GaussianLinearSecondMoment
import CircularLaw.GaussianInnerLaw

/-!
# The actual law of every finite Gaussian linear form

The independent-entry characteristic function identifies a deterministic
linear form with a complex Gaussian scaled by the square root of its
coefficient energy. The finite index type is arbitrary, allowing matrix
entries themselves to be the coordinates.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

def gaussianLinearFormCLM {ι : Type*} [Fintype ι] (a : ι → ℂ) : (ι → ℂ) →L[ℝ] ℂ :=
  ∑ i, a i • ContinuousLinearMap.proj i

theorem gaussian_linear_form_clm_apply {ι : Type*} [Fintype ι] (a x : ι → ℂ) :
    gaussianLinearFormCLM a x = gaussianLinearForm a x := by
  simp [gaussianLinearFormCLM, gaussianLinearForm, smul_eq_mul]

theorem gaussian_linear_form_clm_single {ι : Type*} [Fintype ι] (a : ι → ℂ) (i : ι) (z : ℂ) :
    gaussianLinearFormCLM a (ContinuousLinearMap.single ℝ (fun _ : ι => ℂ) i z) = a i * z := by
  simp [gaussian_linear_form_clm_apply, gaussianLinearForm, Pi.single_apply, mul_ite]

theorem gaussian_linear_form_variance_coefficients {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (L : ℂ →L[ℝ] ℝ) :
    (∑ i : ι, ((L (gaussianLinearFormCLM a
        (ContinuousLinearMap.single ℝ (fun _ : ι => ℂ) i 1))) ^ 2 +
      (L (gaussianLinearFormCLM a
        (ContinuousLinearMap.single ℝ (fun _ : ι => ℂ) i Complex.I))) ^ 2)) =
      (L 1 ^ 2 + L Complex.I ^ 2) * ∑ i, ‖a i‖ ^ 2 := by
  simp only [gaussian_linear_form_clm_single, mul_one]
  simp_rw [mul_comm _ Complex.I, complex_realForm_rotated_norm_sq]
  rw [← Finset.mul_sum]

def gaussianLinearFormScale {ι : Type*} [Fintype ι] (a : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖a i‖ ^ 2)

theorem gaussian_linear_form_scale_sq {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    gaussianLinearFormScale a ^ 2 = ∑ i, ‖a i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem gaussian_linear_form_law {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (standardComplexGaussianProductLaw ι).map (gaussianLinearFormCLM a) =
      standardComplexGaussianLaw.map (gaussianLinearFormScale a • ContinuousLinearMap.id ℝ ℂ) := by
  haveI : IsProbabilityMeasure
      ((standardComplexGaussianProductLaw ι).map (gaussianLinearFormCLM a)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (standardComplexGaussianLaw.map
      (gaussianLinearFormScale a • ContinuousLinearMap.id ℝ ℂ)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, standardComplexGaussianProductLaw, charFunDual_pi, charFunDual_map]
  simp only [standardComplexGaussianLaw_charFunDual]
  rw [← Complex.exp_sum]
  congr 1
  change (∑ i, -((((L (gaussianLinearFormCLM a
      (ContinuousLinearMap.single ℝ (fun _ : ι => ℂ) i 1))) ^ 2 +
      (L (gaussianLinearFormCLM a
      (ContinuousLinearMap.single ℝ (fun _ : ι => ℂ) i Complex.I))) ^ 2) / 4 : ℝ) : ℂ)) =
    -((((L (gaussianLinearFormScale a • (1 : ℂ))) ^ 2 +
      (L (gaussianLinearFormScale a • Complex.I)) ^ 2) / 4 : ℝ) : ℂ)
  rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.sum_div,
    gaussian_linear_form_variance_coefficients]
  simp only [map_smul, smul_eq_mul, mul_pow]
  rw [← gaussian_linear_form_scale_sq a]
  push_cast
  ring

end CircularLaw
