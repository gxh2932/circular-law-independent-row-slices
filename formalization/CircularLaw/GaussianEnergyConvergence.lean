import CircularLaw.GaussianProductEnergy
import CircularLaw.GaussianSingularMoments
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Gaussian energy and the first singular moment converge in probability

The raw `n*n` entry energy divided by `n^2` has centered square
expectation exactly `1/n^2`. Markov's inequality therefore gives an
explicit deviation bound under the actual varying Gaussian matrix laws.
This proves convergence of the zero-shift singular second moment to one.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

theorem gaussian_square_energy_eq_product_energy {n : ℕ} (x : GaussianSquareSample n) :
    squareMatrixEnergy (gaussianSquareMatrix x) = gaussianProductEnergy x := by
  simp only [squareMatrixEnergy, gaussianSquareMatrix, gaussianProductEnergy,
    Fintype.sum_prod_type]

def gaussianNormalizedEnergy {n : ℕ} (x : GaussianSquareSample n) : ℝ :=
  squareMatrixEnergy (gaussianSquareMatrix x) / (n : ℝ) ^ 2

theorem gaussian_normalized_energy_centered_square_integrable (n : ℕ) :
    Integrable (fun x => (gaussianNormalizedEnergy x - 1) ^ 2) (gaussianSquareMatrixLaw n) := by
  by_cases hn : n = 0
  · subst n
    simp only [gaussianNormalizedEnergy, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
      div_zero, zero_sub, neg_one_sq]
    exact integrable_const 1
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hFun (x : GaussianSquareSample n) : (gaussianNormalizedEnergy x - 1) ^ 2 =
        (gaussianProductEnergy x - (Fintype.card (Fin n × Fin n) : ℝ)) ^ 2 /
          ((n : ℝ) ^ 2) ^ 2 := by
      rw [gaussianNormalizedEnergy, gaussian_square_energy_eq_product_energy]
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      field_simp
    simp only [hFun]
    exact (gaussian_product_energy_centered_square_integrable (Fin n × Fin n)).div_const _

theorem gaussian_normalized_energy_centered_square_integral {n : ℕ} (hn : 0 < n) :
    (∫ x, (gaussianNormalizedEnergy x - 1) ^ 2 ∂gaussianSquareMatrixLaw n) =
      1 / (n : ℝ) ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hFun (x : GaussianSquareSample n) : (gaussianNormalizedEnergy x - 1) ^ 2 =
      (gaussianProductEnergy x - (Fintype.card (Fin n × Fin n) : ℝ)) ^ 2 /
        ((n : ℝ) ^ 2) ^ 2 := by
    rw [gaussianNormalizedEnergy, gaussian_square_energy_eq_product_energy]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    field_simp
  simp only [hFun]
  rw [integral_div]
  change (∫ x, (gaussianProductEnergy x - (Fintype.card (Fin n × Fin n) : ℝ)) ^ 2
    ∂standardComplexGaussianProductLaw (Fin n × Fin n)) / ((n : ℝ) ^ 2) ^ 2 = _
  rw [gaussian_product_energy_centered_square_integral]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp

theorem gaussian_normalized_energy_deviation_bound {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussianSquareMatrixLaw n).real {x | ε < |gaussianNormalizedEnergy x - 1|} ≤
      1 / ((n : ℝ) ^ 2 * ε ^ 2) := by
  let μ := gaussianSquareMatrixLaw n
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => sq_nonneg (gaussianNormalizedEnergy x - 1)))
    (gaussian_normalized_energy_centered_square_integrable n) (ε ^ 2)
  have hSubset : {x : GaussianSquareSample n | ε < |gaussianNormalizedEnergy x - 1|} ⊆
      {x | ε ^ 2 ≤ (gaussianNormalizedEnergy x - 1) ^ 2} := by
    intro x hx
    change ε < |gaussianNormalizedEnergy x - 1| at hx
    change ε ^ 2 ≤ (gaussianNormalizedEnergy x - 1) ^ 2
    have hSq := (sq_le_sq₀ hε.le (abs_nonneg _)).mpr hx.le
    simpa only [sq_abs] using hSq
  have hBound := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset)
    (sq_nonneg ε)).trans (hMark.trans_eq (gaussian_normalized_energy_centered_square_integral hn))
  have hεSq : 0 < ε ^ 2 := sq_pos_of_pos hε
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos (by exact_mod_cast hn)) hεSq)).mpr
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hScaled := mul_le_mul_of_nonneg_left hBound (sq_nonneg (n : ℝ))
  have hnR : (n : ℝ) ≠ 0 := hN.ne'
  field_simp at hScaled
  nlinarith

theorem gaussian_normalized_energy_converges_in_probability :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianNormalizedEnergy) 1 := by
  intro ε hε
  have hLimit : Tendsto (fun n : ℕ => 1 / ((n : ℝ) ^ 2 * ε ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    have h' := h.div_const (ε ^ 2)
    simpa only [div_pow, one_pow, zero_pow (by norm_num : 2 ≠ 0), zero_div,
      div_div] using h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun _ => measureReal_nonneg))
    ((eventually_gt_atTop 0).mono (fun _ hn => gaussian_normalized_energy_deviation_bound hn hε))

theorem gaussian_zero_shift_second_moment_eq_energy {n : ℕ} (x : GaussianSquareSample n) :
    gaussianSingularSecondMoment 0 x = gaussianNormalizedEnergy x := by
  rw [gaussian_singular_second_moment_eq]
  simp only [normalizedShiftedGaussianMatrix, zero_smul, sub_zero]
  rw [squareMatrixEnergy_sqrt_normalization, gaussianNormalizedEnergy]
  ring

theorem gaussian_zero_shift_second_moment_converges_in_probability :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianSingularSecondMoment 0) 1 := by
  have hEq : (fun n : ℕ => gaussianSingularSecondMoment (n := n) 0) =
      fun n : ℕ => gaussianNormalizedEnergy (n := n) := by
    funext n x
    exact gaussian_zero_shift_second_moment_eq_energy x
  rw [hEq]
  exact gaussian_normalized_energy_converges_in_probability

end CircularLaw
