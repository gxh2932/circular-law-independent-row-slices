import CircularLaw.SquaredResolventAnalytic
import CircularLaw.GaussianShiftedMomentSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The actual squared resolvent has the checked moment series near zero

A uniform geometric bound justifies summation under a finite compact
measure. For the actual shifted Gaussian limit, every coefficient is the
checked limiting Gram trace moment, hence the coefficient of its formal
even moment series.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem squared_resolvent_geometric_norm (q : ℂ) (R : ℝ)
    {t : ℝ≥0} (ht : (t : ℝ) ≤ R) (k : ℕ) :
    ‖(q * (Complex.ofReal ((t : ℝ) ^ 2))) ^ k‖ ≤ (‖q‖ * R ^ 2) ^ k := by
  simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs]
  have ht2 : (t : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ t.property ht 2
  exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (mul_le_mul_of_nonneg_left ht2 (norm_nonneg _)) k

theorem squared_resolvent_kernel_power (q : ℂ) (t : ℝ≥0) (k : ℕ) :
    (q * (Complex.ofReal ((t : ℝ) ^ 2))) ^ k = q ^ k * (Complex.ofReal ((t : ℝ) ^ (2 * k))) := by
  rw [mul_pow, ← Complex.ofReal_pow, ← pow_mul]

theorem squared_resolvent_hasSum_moments (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ∀ᵐ (t : ℝ≥0) ∂ν, (t : ℝ) ≤ R)
    (q : ℂ) (hSmall : ‖q‖ * R ^ 2 < 1) :
    HasSum (fun k : ℕ => q ^ k * (∫ t, (Complex.ofReal ((t : ℝ) ^ (2 * k))) ∂ν))
      (squaredResolvent ν q) := by
  have hGeom := summable_geometric_of_lt_one
    (mul_nonneg (norm_nonneg q) (sq_nonneg R)) hSmall
  have hSum := hasSum_integral_of_dominated_convergence
    (μ := ν) (F := fun k t => (q * (Complex.ofReal ((t : ℝ) ^ 2))) ^ k)
    (f := squaredResolventKernel q) (fun k _ => (‖q‖ * R ^ 2) ^ k)
    (fun k => by fun_prop)
    (fun k => hSupport.mono (fun t ht => squared_resolvent_geometric_norm q R ht k))
    (Eventually.of_forall (fun _ => hGeom)) (integrable_const _)
    (hSupport.mono (fun t ht => by
      apply hasSum_geometric_of_norm_lt_one
      have hBound := squared_resolvent_geometric_norm q R ht 1
      simp only [pow_one] at hBound
      exact hBound.trans_lt hSmall))
  simpa only [squared_resolvent_kernel_power, integral_const_mul] using hSum

theorem gaussian_shifted_limit_complex_even_moment (z : ℂ) (k : ℕ) :
    (∫ t, (Complex.ofReal ((t : ℝ) ^ (2 * k))) ∂gaussianShiftedSingularLimit z) =
      gaussianShiftedMomentMeanLimit z k := by
  rw [integral_complex_ofReal, gaussian_shifted_limit_even_moments,
    gaussianShiftedSquaredMomentLimit]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, gaussian_shifted_moment_mean_limit_im_zero]

theorem gaussian_shifted_squared_resolvent_hasSum (r : ℝ) (q : ℂ)
    (hSmall : ‖q‖ * (128 + ‖(r : ℂ)‖) ^ 2 < 1) :
    HasSum (fun k : ℕ => q ^ k * PowerSeries.coeff k (gaussianShiftedEvenMomentSeries r))
      (squaredResolvent (gaussianShiftedSingularLimit (r : ℂ)) q) := by
  simpa only [gaussian_shifted_limit_complex_even_moment, gaussian_shifted_even_series_coeff] using
    squared_resolvent_hasSum_moments (gaussianShiftedSingularLimit (r : ℂ))
      (128 + ‖(r : ℂ)‖) (gaussian_shifted_limit_support_ae (r : ℂ)) q hSmall

end CircularLaw
