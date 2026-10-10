import CircularLaw.GaussianCoordinateMoments
import CircularLaw.LogDeterminantSpatialConvergence

/-!
# The actual square complex Gaussian matrix

Every ordered matrix entry is an independent variance-one complex
Gaussian. The normalized shifted matrix and its actual singular-value
measure are defined from these samples. Their second moments are computed
exactly; no limiting singular-value law is assumed.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

abbrev GaussianSquareSample (n : ℕ) := (Fin n × Fin n) → ℂ

def gaussianSquareMatrixLaw (n : ℕ) : Measure (GaussianSquareSample n) :=
  standardComplexGaussianProductLaw (Fin n × Fin n)

instance gaussianSquareMatrixLaw_probability (n : ℕ) :
    IsProbabilityMeasure (gaussianSquareMatrixLaw n) := by
  unfold gaussianSquareMatrixLaw
  infer_instance

def gaussianSquareMatrix {n : ℕ} (x : GaussianSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => x (i, j)

theorem gaussian_square_matrix_measurable (n : ℕ) :
    Measurable (gaussianSquareMatrix (n := n)) := by
  have h : Continuous (gaussianSquareMatrix (n := n)) := by
    unfold gaussianSquareMatrix
    fun_prop
  exact h.measurable

theorem gaussian_square_matrix_coordinate_law {n : ℕ} (i j : Fin n) :
    (gaussianSquareMatrixLaw n).map (fun x => gaussianSquareMatrix x i j) =
      standardComplexGaussianLaw :=
  gaussian_product_law_coordinate (i, j)

theorem gaussian_square_matrix_independent (n : ℕ) :
    iIndepFun (fun ij : Fin n × Fin n => fun x => gaussianSquareMatrix x ij.1 ij.2)
      (gaussianSquareMatrixLaw n) :=
  gaussian_product_law_independent _

theorem gaussian_square_energy_integrable (n : ℕ) :
    Integrable (fun x => squareMatrixEnergy (gaussianSquareMatrix x))
      (gaussianSquareMatrixLaw n) := by
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact gaussian_product_coordinate_norm_power_integrable (i, j) 2

theorem gaussian_square_energy_integral (n : ℕ) :
    (∫ x, squareMatrixEnergy (gaussianSquareMatrix x) ∂gaussianSquareMatrixLaw n) =
      (n : ℝ) ^ 2 := by
  have hInt (i j : Fin n) : Integrable (fun x : GaussianSquareSample n => ‖x (i, j)‖ ^ 2)
      (gaussianSquareMatrixLaw n) := gaussian_product_coordinate_norm_power_integrable (i, j) 2
  have hMoment (i j : Fin n) :
      (∫ x : GaussianSquareSample n, ‖x (i, j)‖ ^ 2 ∂gaussianSquareMatrixLaw n) = 1 := by
    simpa using gaussian_product_coordinate_even_norm_moment (i, j) 1
  unfold squareMatrixEnergy gaussianSquareMatrix
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hInt i j))]
  simp only [integral_finset_sum _ (fun j _ => hInt _ j), hMoment,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def normalizedShiftedGaussianMatrix {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x - z • 1

theorem normalized_shifted_gaussian_matrix_measurable (n : ℕ) (z : ℂ) :
    Measurable (normalizedShiftedGaussianMatrix (n := n) z) := by
  unfold normalizedShiftedGaussianMatrix
  exact ((gaussian_square_matrix_measurable n).const_smul
    ((Real.sqrt (n : ℝ) : ℂ)⁻¹)).sub measurable_const

theorem normalized_shifted_gaussian_matrix_entry {n : ℕ} (z : ℂ)
    (x : GaussianSquareSample n) (i j : Fin n) :
    normalizedShiftedGaussianMatrix z x i j =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ * x (i, j) - if i = j then z else 0 := by
  by_cases hij : i = j <;>
    simp [normalizedShiftedGaussianMatrix, gaussianSquareMatrix, hij]

theorem inverse_sqrt_dimension_norm_sq (n : ℕ) :
    ‖(Real.sqrt (n : ℝ) : ℂ)⁻¹‖ ^ 2 = 1 / (n : ℝ) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), one_div]

theorem gaussian_shifted_entry_energy_integrable {n : ℕ} (z : ℂ) (i j : Fin n) :
    Integrable (fun x => ‖normalizedShiftedGaussianMatrix z x i j‖ ^ 2)
      (gaussianSquareMatrixLaw n) := by
  simp only [normalized_shifted_gaussian_matrix_entry]
  exact gaussian_product_affine_energy_integrable (i, j) _ _

theorem gaussian_shifted_entry_energy_integral {n : ℕ} (z : ℂ) (i j : Fin n) :
    (∫ x, ‖normalizedShiftedGaussianMatrix z x i j‖ ^ 2 ∂gaussianSquareMatrixLaw n) =
      1 / (n : ℝ) + if i = j then ‖z‖ ^ 2 else 0 := by
  simp only [normalized_shifted_gaussian_matrix_entry, gaussianSquareMatrixLaw,
    gaussian_product_affine_energy_integral, inverse_sqrt_dimension_norm_sq]
  by_cases hij : i = j <;> simp [hij]

theorem gaussian_shifted_energy_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun x => squareMatrixEnergy (normalizedShiftedGaussianMatrix z x))
      (gaussianSquareMatrixLaw n) := by
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact gaussian_shifted_entry_energy_integrable z i j

theorem gaussian_shifted_energy_integral {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (∫ x, squareMatrixEnergy (normalizedShiftedGaussianMatrix z x)
      ∂gaussianSquareMatrixLaw n) = (n : ℝ) * (1 + ‖z‖ ^ 2) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold squareMatrixEnergy
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => gaussian_shifted_entry_energy_integrable z i j))]
  simp only [integral_finset_sum _ (fun j _ => gaussian_shifted_entry_energy_integrable z _ j),
    gaussian_shifted_entry_energy_integral, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

def gaussianSingularMeasure {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) : Measure ℝ≥0 :=
  squareSingularMeasure (normalizedShiftedGaussianMatrix z x)

theorem gaussian_singular_measure_probability {n : ℕ} (hn : 0 < n) (z : ℂ)
    (x : GaussianSquareSample n) : IsProbabilityMeasure (gaussianSingularMeasure z x) :=
  squareSingularMeasure_probability hn _

def gaussianSingularSecondMoment {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) : ℝ :=
  ∫ t, (t : ℝ) ^ 2 ∂gaussianSingularMeasure z x

theorem gaussian_singular_second_moment_eq {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) :
    gaussianSingularSecondMoment z x =
      squareMatrixEnergy (normalizedShiftedGaussianMatrix z x) / n :=
  squareSingularMeasure_second_moment _

theorem gaussian_singular_second_moment_integrable (n : ℕ) (z : ℂ) :
    Integrable (gaussianSingularSecondMoment (n := n) z) (gaussianSquareMatrixLaw n) := by
  have hEq : gaussianSingularSecondMoment (n := n) z =
      fun x => squareMatrixEnergy (normalizedShiftedGaussianMatrix z x) / n :=
    funext (gaussian_singular_second_moment_eq z)
  rw [hEq]
  exact (gaussian_shifted_energy_integrable n z).div_const _

theorem gaussian_singular_second_moment_integral {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (∫ x, gaussianSingularSecondMoment z x ∂gaussianSquareMatrixLaw n) = 1 + ‖z‖ ^ 2 := by
  simp only [gaussian_singular_second_moment_eq]
  rw [integral_div, gaussian_shifted_energy_integral hn z]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end CircularLaw
