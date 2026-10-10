import CircularLaw.GaussianCoordinateMoments

/-!
# Exact fluctuations of independent Gaussian coordinate energy

For `N` actual independent standard complex Gaussian coordinates,
the energy has mean `N`, second moment `N^2+N` and centered square
mean `N`. These include all repeated-coordinate contributions.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem complex_norm_square_product_real (a b : ℂ) :
    ‖a‖ ^ 2 * ‖b‖ ^ 2 = (a * star a * b * star b).re := by
  have ha : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    simpa using complex_balanced_power_eq_norm_power a 1
  have hb : b * star b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    simpa using complex_balanced_power_eq_norm_power b 1
  rw [mul_assoc (a * star a) b (star b), ha, hb]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

theorem gaussian_coordinate_energy_product_integrable {ι : Type*} [Fintype ι]
    (i j : ι) :
    Integrable (fun x : ι → ℂ => ‖x i‖ ^ 2 * ‖x j‖ ^ 2)
      (standardComplexGaussianProductLaw ι) := by
  simp only [complex_norm_square_product_real]
  exact (gaussian_entry_wick_four_integrable i i j j).re

theorem gaussian_coordinate_energy_product_integral {ι : Type*} [Fintype ι]
    (i j : ι) :
    (∫ x : ι → ℂ, ‖x i‖ ^ 2 * ‖x j‖ ^ 2 ∂standardComplexGaussianProductLaw ι) =
      1 + if i = j then 1 else 0 := by
  simp only [complex_norm_square_product_real]
  change (∫ x : ι → ℂ, RCLike.re (x i * star (x i) * x j * star (x j))
    ∂standardComplexGaussianProductLaw ι) = _
  rw [integral_re (gaussian_entry_wick_four_integrable i i j j), gaussian_entry_wick_four]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

def gaussianProductEnergy {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

theorem gaussian_product_energy_integrable (ι : Type*) [Fintype ι] :
    Integrable (gaussianProductEnergy (ι := ι)) (standardComplexGaussianProductLaw ι) := by
  apply integrable_finset_sum
  intro i _
  exact gaussian_product_coordinate_norm_power_integrable i 2

theorem gaussian_product_energy_integral (ι : Type*) [Fintype ι] :
    (∫ x : ι → ℂ, gaussianProductEnergy x ∂standardComplexGaussianProductLaw ι) =
      (Fintype.card ι : ℝ) := by
  have hMoment (i : ι) :
      (∫ x : ι → ℂ, ‖x i‖ ^ 2 ∂standardComplexGaussianProductLaw ι) = 1 := by
    simpa using gaussian_product_coordinate_even_norm_moment i 1
  simp only [gaussianProductEnergy]
  rw [integral_finset_sum _
    (fun i _ => gaussian_product_coordinate_norm_power_integrable i 2)]
  simp only [hMoment, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem gaussian_product_energy_square_expansion {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    gaussianProductEnergy x ^ 2 = ∑ i, ∑ j, ‖x i‖ ^ 2 * ‖x j‖ ^ 2 := by
  rw [gaussianProductEnergy, pow_two, Fintype.sum_mul_sum]

theorem gaussian_product_energy_square_integrable (ι : Type*) [Fintype ι] :
    Integrable (fun x : ι → ℂ => gaussianProductEnergy x ^ 2)
      (standardComplexGaussianProductLaw ι) := by
  simp only [gaussian_product_energy_square_expansion]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact gaussian_coordinate_energy_product_integrable i j

theorem gaussian_product_energy_square_integral (ι : Type*) [Fintype ι] :
    (∫ x : ι → ℂ, gaussianProductEnergy x ^ 2 ∂standardComplexGaussianProductLaw ι) =
      (Fintype.card ι : ℝ) ^ 2 + Fintype.card ι := by
  simp only [gaussian_product_energy_square_expansion]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => gaussian_coordinate_energy_product_integrable i j))]
  simp only [integral_finset_sum _ (fun j _ => gaussian_coordinate_energy_product_integrable _ j),
    gaussian_coordinate_energy_product_integral, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem gaussian_product_energy_centered_square_integrable (ι : Type*) [Fintype ι] :
    Integrable (fun x : ι → ℂ => (gaussianProductEnergy x - (Fintype.card ι : ℝ)) ^ 2)
      (standardComplexGaussianProductLaw ι) := by
  have hFun (x : ι → ℂ) : (gaussianProductEnergy x - (Fintype.card ι : ℝ)) ^ 2 =
      gaussianProductEnergy x ^ 2 - 2 * Fintype.card ι * gaussianProductEnergy x +
        (Fintype.card ι : ℝ) ^ 2 := by ring
  simp only [hFun]
  exact ((gaussian_product_energy_square_integrable ι).sub
    ((gaussian_product_energy_integrable ι).const_mul _)).add (integrable_const _)

theorem gaussian_product_energy_centered_square_integral (ι : Type*) [Fintype ι] :
    (∫ x : ι → ℂ, (gaussianProductEnergy x - (Fintype.card ι : ℝ)) ^ 2
      ∂standardComplexGaussianProductLaw ι) = (Fintype.card ι : ℝ) := by
  have hFun (x : ι → ℂ) : (gaussianProductEnergy x - (Fintype.card ι : ℝ)) ^ 2 =
      gaussianProductEnergy x ^ 2 - 2 * Fintype.card ι * gaussianProductEnergy x +
        (Fintype.card ι : ℝ) ^ 2 := by ring
  simp only [hFun]
  have hSub : Integrable (fun x : ι → ℂ =>
      gaussianProductEnergy x ^ 2 - 2 * Fintype.card ι * gaussianProductEnergy x)
      (standardComplexGaussianProductLaw ι) :=
    (gaussian_product_energy_square_integrable ι).sub
      ((gaussian_product_energy_integrable ι).const_mul (2 * (Fintype.card ι : ℝ)))
  rw [integral_add hSub (integrable_const _),
    integral_sub (gaussian_product_energy_square_integrable ι)
      ((gaussian_product_energy_integrable ι).const_mul (2 * (Fintype.card ι : ℝ))),
    integral_const_mul, gaussian_product_energy_square_integral,
    gaussian_product_energy_integral, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

end CircularLaw
