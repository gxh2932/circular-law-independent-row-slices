import CircularLaw.GaussianCoordinateMoments

/-!
# Exact second moments of Gaussian linear forms

The actual coordinate covariance is the Kronecker delta. Consequently
every deterministic complex linear form has mean-square norm equal to
the coefficient square sum. This also controls traces of Gaussian matrices.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem gaussian_coordinate_covariance_integrable {ι : Type*} [Fintype ι] (i j : ι) :
    Integrable (fun x : ι → ℂ => x i * star (x j))
      (standardComplexGaussianProductLaw ι) := by
  have hWord : (fun x : ι → ℂ => x i * star (x j)) = gaussianEntryWord [i] [j] := by
    funext x
    simp [gaussianEntryWord]
  rw [hWord]
  exact gaussian_entry_word_integrable _ _

theorem gaussian_coordinate_covariance {ι : Type*} [Fintype ι] (i j : ι) :
    (∫ x : ι → ℂ, x i * star (x j) ∂standardComplexGaussianProductLaw ι) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hNorm (x : ι → ℂ) : x i * star (x i) = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      simpa using complex_balanced_power_eq_norm_power (x i) 1
    simp only [hNorm, integral_complex_ofReal]
    have hMoment := gaussian_product_coordinate_even_norm_moment i 1
    norm_num at hMoment
    rw [hMoment]
    rfl
  · rw [if_neg hij]
    have h := gaussian_entry_word_unbalanced_integral [i] [j] i (by simp [Ne.symm hij])
    simpa only [gaussianEntryWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using h

def gaussianLinearForm {ι : Type*} [Fintype ι] (a : ι → ℂ) (x : ι → ℂ) : ℂ :=
  ∑ i, a i * x i

theorem gaussian_linear_form_integrable {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    Integrable (gaussianLinearForm a) (standardComplexGaussianProductLaw ι) := by
  apply integrable_finset_sum
  intro i _
  exact (gaussian_product_coordinate_mean_integrable i).const_mul _

theorem gaussian_linear_form_square_expansion {ι : Type*} [Fintype ι]
    (a x : ι → ℂ) :
    gaussianLinearForm a x * star (gaussianLinearForm a x) =
      ∑ i, ∑ j, (a i * star (a j)) * (x i * star (x j)) := by
  simp only [gaussianLinearForm, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussian_linear_form_square_integrable {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    Integrable (fun x => gaussianLinearForm a x * star (gaussianLinearForm a x))
      (standardComplexGaussianProductLaw ι) := by
  simp only [gaussian_linear_form_square_expansion]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact (gaussian_coordinate_covariance_integrable i j).const_mul _

theorem gaussian_linear_form_square_integral {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (∫ x, gaussianLinearForm a x * star (gaussianLinearForm a x)
      ∂standardComplexGaussianProductLaw ι) = ∑ i, a i * star (a i) := by
  have hInt (i j : ι) :=
    (gaussian_coordinate_covariance_integrable i j).const_mul (a i * star (a j))
  simp only [gaussian_linear_form_square_expansion]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hInt i j))]
  simp only [integral_finset_sum _ (fun j _ => hInt _ j), integral_const_mul,
    gaussian_coordinate_covariance, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem gaussian_linear_form_norm_square_real {ι : Type*} [Fintype ι]
    (a x : ι → ℂ) :
    ‖gaussianLinearForm a x‖ ^ 2 =
      (gaussianLinearForm a x * star (gaussianLinearForm a x)).re := by
  have h : gaussianLinearForm a x * star (gaussianLinearForm a x) =
      ((‖gaussianLinearForm a x‖ ^ 2 : ℝ) : ℂ) := by
    simpa using complex_balanced_power_eq_norm_power (gaussianLinearForm a x) 1
  rw [h, Complex.ofReal_re]

theorem gaussian_linear_form_norm_square_integrable {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    Integrable (fun x => ‖gaussianLinearForm a x‖ ^ 2) (standardComplexGaussianProductLaw ι) := by
  simp only [gaussian_linear_form_norm_square_real]
  exact (gaussian_linear_form_square_integrable a).re

theorem gaussian_linear_form_norm_square_integral {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (∫ x, ‖gaussianLinearForm a x‖ ^ 2 ∂standardComplexGaussianProductLaw ι) = ∑ i, ‖a i‖ ^ 2 := by
  simp only [gaussian_linear_form_norm_square_real]
  change (∫ x, RCLike.re (gaussianLinearForm a x * star (gaussianLinearForm a x))
    ∂standardComplexGaussianProductLaw ι) = _
  rw [integral_re (gaussian_linear_form_square_integrable a), gaussian_linear_form_square_integral]
  change (∑ i, a i * star (a i)).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : a i * star (a i) = ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
    simpa using complex_balanced_power_eq_norm_power (a i) 1
  rw [h, Complex.ofReal_re]

end CircularLaw
