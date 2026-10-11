import CircularLaw.GaussianProductCurry
import CircularLaw.ComplexGaussianLinearForm

/-!
# Conjugation preserves the actual independent Gaussian row law

Characteristic functions check scalar conjugation invariance. Finite
product pushforwards then preserve every vector and row product law.
This allows the row-distance estimates to apply to the conjugated rows
whose Gram matrix is the literal matrix product `A A*`.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem standard_complex_gaussian_conjugate_law :
    standardComplexGaussianLaw.map (fun z : ℂ => star z) = standardComplexGaussianLaw := by
  let M : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hFun : (fun z : ℂ => star z) = M := rfl
  rw [hFun]
  haveI : IsProbabilityMeasure (standardComplexGaussianLaw.map M) :=
    Measure.isProbabilityMeasure_map M.measurable.aemeasurable
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, standardComplexGaussianLaw_charFunDual,
    standardComplexGaussianLaw_charFunDual]
  simp only [ContinuousLinearMap.comp_apply, M, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_one, Complex.conj_I, map_neg, neg_sq]

theorem gaussian_product_conjugate_law {ι : Type*} [Fintype ι] :
    (standardComplexGaussianProductLaw ι).map (fun x i => star (x i)) =
      standardComplexGaussianProductLaw ι := by
  haveI : IsProbabilityMeasure (standardComplexGaussianLaw.map (fun z : ℂ => star z)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold standardComplexGaussianProductLaw
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : AEMeasurable (fun z : ℂ => star z)
    standardComplexGaussianLaw))]
  simp only [standard_complex_gaussian_conjugate_law]

theorem gaussian_vector_conjugate_law (n : ℕ) :
    (standardComplexGaussianVectorLaw n).map (fun x i => star (x i)) =
      standardComplexGaussianVectorLaw n := gaussian_product_conjugate_law

theorem gaussian_rows_conjugate_law (m n : ℕ) :
    (gaussianRowsLaw m n).map (fun x i j => star (x i j)) = gaussianRowsLaw m n := by
  have hMeas : Measurable (fun x : Fin n → ℂ => fun i => star (x i)) :=
    measurable_pi_iff.mpr (fun i => continuous_star.measurable.comp (measurable_pi_apply i))
  haveI : IsProbabilityMeasure ((standardComplexGaussianVectorLaw n).map
      (fun x i => star (x i))) := Measure.isProbabilityMeasure_map hMeas.aemeasurable
  unfold gaussianRowsLaw
  rw [Measure.pi_map_pi (fun _ => hMeas.aemeasurable)]
  simp only [gaussian_vector_conjugate_law]

end CircularLaw
