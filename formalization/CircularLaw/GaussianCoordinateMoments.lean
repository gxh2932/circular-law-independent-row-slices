import CircularLaw.GaussianWickFour
import CircularLaw.MatrixEnergyShift

/-!
# Coordinate moments under the actual independent-entry law

Evaluation preserves the actual Gaussian law. In particular affine
coordinate energies have exact mean `|c|^2 + |z|^2`, with no spectral
limit assumed.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem gaussian_product_coordinate_integrable {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (i : ι) {f : ℂ → E}
    (hf : Integrable f standardComplexGaussianLaw) :
    Integrable (fun x : ι → ℂ => f (x i)) (standardComplexGaussianProductLaw ι) :=
  (measurePreserving_eval (fun _ : ι => standardComplexGaussianLaw) i).integrable_comp_of_integrable hf

theorem gaussian_product_coordinate_integral {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (i : ι) (f : ℂ → E) (hf : AEStronglyMeasurable f standardComplexGaussianLaw) :
    (∫ x : ι → ℂ, f (x i) ∂standardComplexGaussianProductLaw ι) =
      ∫ z : ℂ, f z ∂standardComplexGaussianLaw := by
  rw [← gaussian_product_law_coordinate i] at hf
  rw [← integral_map (measurable_pi_apply i).aemeasurable hf,
    gaussian_product_law_coordinate]

theorem gaussian_product_coordinate_norm_power_integrable {ι : Type*} [Fintype ι]
    (i : ι) (k : ℕ) :
    Integrable (fun x : ι → ℂ => ‖x i‖ ^ k) (standardComplexGaussianProductLaw ι) :=
  gaussian_product_coordinate_integrable i (standard_complex_gaussian_norm_power_integrable k)

theorem gaussian_product_coordinate_even_norm_moment {ι : Type*} [Fintype ι]
    (i : ι) (k : ℕ) :
    (∫ x : ι → ℂ, ‖x i‖ ^ (2 * k) ∂standardComplexGaussianProductLaw ι) = k.factorial := by
  rw [gaussian_product_coordinate_integral i _
    (standard_complex_gaussian_norm_power_integrable (2 * k)).aestronglyMeasurable,
    standard_complex_gaussian_even_norm_moment]

theorem gaussian_product_coordinate_mean_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun x : ι → ℂ => x i) (standardComplexGaussianProductLaw ι) := by
  apply gaussian_product_coordinate_integrable i (f := id)
  simpa using standard_complex_gaussian_mixed_power_integrable 1 0

theorem gaussian_product_coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℂ, x i ∂standardComplexGaussianProductLaw ι) = 0 := by
  simpa only [gaussianEntryWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] using
      gaussian_entry_word_length_mismatch_integral [i] [] (by simp)

theorem complex_norm_sub_square_identity (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * star b).re := by
  simpa only [Complex.normSq_eq_norm_sq] using Complex.normSq_sub a b

theorem gaussian_product_affine_energy_integrable {ι : Type*} [Fintype ι]
    (i : ι) (c z : ℂ) :
    Integrable (fun x : ι → ℂ => ‖c * x i - z‖ ^ 2)
      (standardComplexGaussianProductLaw ι) := by
  have hCross := ((gaussian_product_coordinate_mean_integrable i).const_mul c).mul_const (star z)
  have hMain : Integrable (fun x : ι → ℂ => ‖c‖ ^ 2 * ‖x i‖ ^ 2 + ‖z‖ ^ 2)
      (standardComplexGaussianProductLaw ι) :=
    ((gaussian_product_coordinate_norm_power_integrable i 2).const_mul
      (‖c‖ ^ 2)).add (integrable_const (‖z‖ ^ 2))
  simpa only [complex_norm_sub_square_identity, norm_mul, mul_pow] using
    hMain.sub (hCross.re.const_mul 2)

theorem gaussian_product_affine_energy_integral {ι : Type*} [Fintype ι]
    (i : ι) (c z : ℂ) :
    (∫ x : ι → ℂ, ‖c * x i - z‖ ^ 2 ∂standardComplexGaussianProductLaw ι) =
      ‖c‖ ^ 2 + ‖z‖ ^ 2 := by
  have hCross := ((gaussian_product_coordinate_mean_integrable i).const_mul c).mul_const (star z)
  have hMain : Integrable (fun x : ι → ℂ => ‖c‖ ^ 2 * ‖x i‖ ^ 2 + ‖z‖ ^ 2)
      (standardComplexGaussianProductLaw ι) :=
    ((gaussian_product_coordinate_norm_power_integrable i 2).const_mul
      (‖c‖ ^ 2)).add (integrable_const (‖z‖ ^ 2))
  simp only [complex_norm_sub_square_identity, norm_mul, mul_pow]
  change (∫ x : ι → ℂ, ‖c‖ ^ 2 * ‖x i‖ ^ 2 + ‖z‖ ^ 2 -
    2 * RCLike.re (c * x i * star z) ∂standardComplexGaussianProductLaw ι) = _
  rw [integral_sub hMain (hCross.re.const_mul 2),
    integral_add ((gaussian_product_coordinate_norm_power_integrable i 2).const_mul _)
      (integrable_const _), integral_const_mul, integral_const_mul,
    integral_re hCross, integral_mul_const, integral_const_mul,
    gaussian_product_coordinate_mean]
  have hSecond := gaussian_product_coordinate_even_norm_moment i 1
  norm_num at hSecond
  simp [hSecond]

end CircularLaw
