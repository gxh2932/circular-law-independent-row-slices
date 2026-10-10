import CircularLaw.GaussianLogConvergence
import CircularLaw.ComplexGaussianRotation
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The actual shifted Gaussian limit is radial

Unit multiplication preserves the independent Gaussian matrix law.
The shifted Gram matrix is unchanged after rotating both matrix and
shift. Actual weak-limit uniqueness consequently identifies the full
limiting singular measures, and hence their logarithmic integrals, at
any two shifts with equal norm.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem gaussian_square_unit_mul_law (n : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    (gaussianSquareMatrixLaw n).map (fun x p => c * x p) = gaussianSquareMatrixLaw n := by
  haveI : IsProbabilityMeasure (standardComplexGaussianLaw.map (fun z : ℂ => c * z)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold gaussianSquareMatrixLaw standardComplexGaussianProductLaw
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : AEMeasurable (fun z : ℂ => c * z)
    standardComplexGaussianLaw))]
  simp only [standard_complex_gaussian_unit_mul_law c hc]

theorem gaussian_square_unit_mul_embedding (n : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurableEmbedding (fun x : GaussianSquareSample n => fun p => c * x p) := by
  have hc0 : c ≠ 0 := by
    intro h
    simp only [h, norm_zero] at hc
    norm_num at hc
  let e : GaussianSquareSample n ≃ᵐ GaussianSquareSample n :=
    MeasurableEquiv.piCongrRight (fun _ => (Homeomorph.mulLeft₀ c hc0).toMeasurableEquiv)
  exact e.measurableEmbedding

theorem normalized_shifted_gaussian_unit_rotate {n : ℕ} (c z : ℂ) (x : GaussianSquareSample n) :
    normalizedShiftedGaussianMatrix (c * z) (fun p => c * x p) =
      c • normalizedShiftedGaussianMatrix z x := by
  ext i j
  simp only [normalizedShiftedGaussianMatrix, gaussianSquareMatrix, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem unit_smul_square_gram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) :
    (c • A) * (c • A).conjTranspose = A * A.conjTranspose := by
  have hScalar : star c * c = 1 := by
    rw [mul_comm]
    change c * (starRingEnd ℂ) c = 1
    rw [Complex.mul_conj', hc]
    norm_num
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hScalar, one_smul]

theorem ordered_square_singular_unit_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (j : Fin n) :
    orderedSquareSingularValues (c • A) j = orderedSquareSingularValues A j := by
  unfold orderedSquareSingularValues
  simp only [unit_smul_square_gram A c hc]

theorem gaussian_shifted_singular_unit_rotate {n : ℕ} (c : ℂ) (hc : ‖c‖ = 1)
    (z : ℂ) (x : GaussianSquareSample n) :
    squareSingularValuesNNReal (normalizedShiftedGaussianMatrix (c * z) (fun p => c * x p)) =
      squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) := by
  funext j
  apply Subtype.ext
  change orderedSquareSingularValues
    (normalizedShiftedGaussianMatrix (c * z) (fun p => c * x p)) j =
    orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j
  rw [normalized_shifted_gaussian_unit_rotate]
  exact ordered_square_singular_unit_smul _ c hc j

theorem gaussian_shifted_weak_convergence_unit_rotate (c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
      (gaussianShiftedSingularLimit (c * z)) := by
  intro f hf hBound epsilon hEpsilon
  have h := gaussian_shifted_weak_convergence (c * z) f hf hBound epsilon hEpsilon
  have hProbability (n : ℕ) :
      (gaussianSquareMatrixLaw n).real {x | epsilon <
        |empiricalNonnegativeMean (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) f -
          ∫ t, f t ∂gaussianShiftedSingularLimit (c * z)|} =
      (gaussianSquareMatrixLaw n).real {x | epsilon <
        |empiricalNonnegativeMean (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix (c * z) x)) f -
          ∫ t, f t ∂gaussianShiftedSingularLimit (c * z)|} := by
    have hMap := (gaussian_square_unit_mul_embedding n c hc).map_apply (gaussianSquareMatrixLaw n)
      {x | epsilon < |empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix (c * z) x)) f -
          ∫ t, f t ∂gaussianShiftedSingularLimit (c * z)|}
    rw [gaussian_square_unit_mul_law n c hc] at hMap
    have hSets : (fun x : GaussianSquareSample n => fun p => c * x p) ⁻¹'
        {x | epsilon < |empiricalNonnegativeMean
          (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix (c * z) x)) f -
            ∫ t, f t ∂gaussianShiftedSingularLimit (c * z)|} =
        {x | epsilon < |empiricalNonnegativeMean
          (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) f -
            ∫ t, f t ∂gaussianShiftedSingularLimit (c * z)|} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, gaussian_shifted_singular_unit_rotate c hc]
    rw [hSets] at hMap
    exact congrArg ENNReal.toReal hMap.symm
  simpa only [hProbability] using h

theorem gaussian_shifted_limit_unit_rotate (c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    gaussianShiftedSingularLimit (c * z) = gaussianShiftedSingularLimit z :=
  gaussian_shifted_limit_unique z (gaussianShiftedSingularLimit (c * z))
    (gaussian_shifted_weak_convergence_unit_rotate c hc z)

theorem gaussian_shifted_limit_eq_of_norm_eq {z w : ℂ} (hNorm : ‖w‖ = ‖z‖) :
    gaussianShiftedSingularLimit w = gaussianShiftedSingularLimit z := by
  by_cases hz : z = 0
  · subst z
    have hw : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hNorm)
    subst w
    rfl
  · let c : ℂ := w / z
    have hc : ‖c‖ = 1 := by
      dsimp only [c]
      rw [norm_div, hNorm, div_self (norm_ne_zero_iff.mpr hz)]
    have hcz : c * z = w := div_mul_cancel₀ w hz
    rw [← hcz]
    exact gaussian_shifted_limit_unit_rotate c hc z

theorem gaussian_shifted_log_integral_eq_of_norm_eq {z w : ℂ} (hNorm : ‖w‖ = ‖z‖) :
    (∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit w) =
      ∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z := by
  rw [gaussian_shifted_limit_eq_of_norm_eq hNorm]

theorem gaussian_shifted_limit_eq_real_norm (z : ℂ) :
    gaussianShiftedSingularLimit z = gaussianShiftedSingularLimit (‖z‖ : ℂ) :=
  gaussian_shifted_limit_eq_of_norm_eq (by simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)])

end CircularLaw
