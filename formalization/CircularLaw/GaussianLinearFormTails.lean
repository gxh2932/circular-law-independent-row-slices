import CircularLaw.GaussianLinearFormLaw
import CircularLaw.GaussianCorrelationSmallBall

/-!
# Gaussian linear-form tails from coefficient energy

The exact scaled Gaussian law gives a uniform radial-tail bound whenever
the coefficient energy is at most the square of a positive scale. Zero
coefficient energy is included, rather than treated as nondegenerate.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem scaled_standard_complex_gaussian_tail_le_scale {σ S r : ℝ}
    (hσ : 0 ≤ σ) (hS : 0 < S) (hσS : σ ≤ S) (hr : 0 < r) :
    (standardComplexGaussianLaw.map (σ • ContinuousLinearMap.id ℝ ℂ)).real
      {z | r ≤ ‖z‖} ≤ Real.exp (-(r / S) ^ 2) := by
  by_cases hZero : σ = 0
  · have hs : MeasurableSet {z : ℂ | r ≤ ‖z‖} :=
      (isClosed_le continuous_const continuous_norm).measurableSet
    rw [hZero, map_measureReal_apply (by fun_prop) hs]
    have hEmpty : ((0 : ℝ) • ContinuousLinearMap.id ℝ ℂ) ⁻¹' {z : ℂ | r ≤ ‖z‖} = ∅ := by
      ext z
      simp [hr]
    rw [hEmpty, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hPos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hZero)
    rw [scaledStandardComplexGaussianLaw_radial_tail hPos hr.le]
    apply Real.exp_le_exp.mpr
    have hRatio : r / S ≤ r / σ := div_le_div_of_nonneg_left hr.le hPos hσS
    have hRatioPos : 0 ≤ r / S := div_nonneg hr.le hS.le
    nlinarith

theorem gaussian_linear_form_radial_tail_bound {ι : Type*} [Fintype ι] (a : ι → ℂ)
    {S r : ℝ} (hS : 0 < S) (hEnergy : (∑ i, ‖a i‖ ^ 2) ≤ S ^ 2) (hr : 0 < r) :
    (standardComplexGaussianProductLaw ι).real {x | r ≤ ‖gaussianLinearForm a x‖} ≤
      Real.exp (-(r / S) ^ 2) := by
  have hScale : gaussianLinearFormScale a ≤ S := Real.sqrt_le_iff.mpr ⟨hS.le, hEnergy⟩
  have h := scaled_standard_complex_gaussian_tail_le_scale (Real.sqrt_nonneg _) hS hScale hr
  change (standardComplexGaussianLaw.map
    (gaussianLinearFormScale a • ContinuousLinearMap.id ℝ ℂ)).real {z | r ≤ ‖z‖} ≤ _ at h
  have hs : MeasurableSet {z : ℂ | r ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  rw [← gaussian_linear_form_law a, map_measureReal_apply (by fun_prop) hs] at h
  simpa only [Set.preimage_setOf_eq, gaussian_linear_form_clm_apply] using h

end CircularLaw
