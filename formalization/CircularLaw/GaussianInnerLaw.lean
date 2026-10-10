import CircularLaw.ComplexGaussianLinearForm
import CircularLaw.ProjectedComplexGaussian

/-!
# Exact complex linear forms and projected Gaussian normals

Every Hermitian linear form of the actual standard vector has the law of
its coefficient norm times a standard complex Gaussian. The projection
identity then gives the corresponding law for every deterministic normal
subspace, including degenerate directions.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def gaussianInnerForm {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) : (Fin n → ℂ) →L[ℝ] ℂ :=
  ((innerSL ℂ x).restrictScalars ℝ).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap

theorem gaussianInnerForm_apply {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) (z : Fin n → ℂ) :
    gaussianInnerForm x z = ⟪x, standardComplexGaussianVector n z⟫_ℂ := rfl

theorem gaussianInnerForm_single {n : ℕ} (x : EuclideanSpace ℂ (Fin n))
    (i : Fin n) (a : ℂ) :
    gaussianInnerForm x (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i a) =
      a * star (x i) := by
  exact EuclideanSpace.inner_single_right i a x

theorem gaussianInnerForm_variance_coefficients {n : ℕ} (x : EuclideanSpace ℂ (Fin n))
    (L : ℂ →L[ℝ] ℝ) :
    (∑ i : Fin n, ((L (gaussianInnerForm x
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i 1))) ^ 2 +
      (L (gaussianInnerForm x
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i Complex.I))) ^ 2)) =
      (L 1 ^ 2 + L Complex.I ^ 2) * ‖x‖ ^ 2 := by
  simp only [gaussianInnerForm_single, one_mul]
  simp_rw [complex_realForm_rotated_norm_sq, norm_star]
  rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq]

theorem gaussianInnerForm_law {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    (standardComplexGaussianVectorLaw n).map (gaussianInnerForm x) =
      standardComplexGaussianLaw.map (‖x‖ • ContinuousLinearMap.id ℝ ℂ) := by
  let S : ℂ →L[ℝ] ℂ := ‖x‖ • ContinuousLinearMap.id ℝ ℂ
  haveI : IsProbabilityMeasure
      ((standardComplexGaussianVectorLaw n).map (gaussianInnerForm x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (standardComplexGaussianLaw.map S) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, standardComplexGaussianVectorLaw, charFunDual_pi, charFunDual_map]
  simp only [standardComplexGaussianLaw_charFunDual]
  rw [← Complex.exp_sum]
  congr 1
  change (∑ i : Fin n, -((((L (gaussianInnerForm x
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i 1))) ^ 2 +
      (L (gaussianInnerForm x
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i Complex.I))) ^ 2) / 4 : ℝ) : ℂ)) =
    -((((L (‖x‖ • (1 : ℂ))) ^ 2 + (L (‖x‖ • Complex.I)) ^ 2) / 4 : ℝ) : ℂ)
  rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.sum_div,
    gaussianInnerForm_variance_coefficients]
  simp only [map_smul, smul_eq_mul]
  push_cast
  ring

theorem projectedComplexGaussian_inner_law {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin n)) :
    (standardComplexGaussianVectorLaw n).map (fun z => ⟪x, projectedComplexGaussian E z⟫_ℂ) =
      standardComplexGaussianLaw.map
        (‖Eᗮ.starProjection x‖ • ContinuousLinearMap.id ℝ ℂ) := by
  have hEq : (fun z => ⟪x, projectedComplexGaussian E z⟫_ℂ) =
      gaussianInnerForm (Eᗮ.starProjection x) := by
    funext z
    exact projectedComplexGaussian_inner E x z
  rw [hEq]
  exact gaussianInnerForm_law _

def gaussianCoordinateDifferenceVector {n : ℕ} (i j : Fin n) : EuclideanSpace ℂ (Fin n) :=
  EuclideanSpace.single i 1 - EuclideanSpace.single j 1

theorem gaussianCoordinateDifferenceVector_inner {n : ℕ} (i j : Fin n)
    (y : EuclideanSpace ℂ (Fin n)) :
    ⟪gaussianCoordinateDifferenceVector i j, y⟫_ℂ = y i - y j := by
  rw [gaussianCoordinateDifferenceVector, inner_sub_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp

theorem projectedComplexGaussian_pair_law {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n) :
    (standardComplexGaussianVectorLaw n).map
      (fun z => projectedComplexGaussian E z i - projectedComplexGaussian E z j) =
      standardComplexGaussianLaw.map
        (‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖ •
          ContinuousLinearMap.id ℝ ℂ) := by
  simpa only [gaussianCoordinateDifferenceVector_inner] using
    projectedComplexGaussian_inner_law E (gaussianCoordinateDifferenceVector i j)

end CircularLaw
