import CircularLaw.ComplexGaussianDensity
import CircularLaw.GaussianInnerLaw
import CircularLaw.PlanarDensityScale

/-!
# Small balls for actual projected coordinate differences

The variance scale is the norm of the orthogonal projection of `e_i-e_j`.
At a positive scale the probability of a disk of radius `r` is at most
`(r/scale)^2`, uniformly over its centre. No density or small-ball premise
is assumed for the projected Gaussian.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CircularLaw

theorem scaledStandardComplexGaussianLaw_closedBall_le {σ r : ℝ} (hσ : σ ≠ 0)
    (hr : 0 ≤ r) (z : ℂ) :
    (standardComplexGaussianLaw.map (σ • ContinuousLinearMap.id ℝ ℂ))
      (Metric.closedBall z r) ≤ ENNReal.ofReal ((r / σ) ^ 2) := by
  have hDom : standardComplexGaussianLaw ≤ ENNReal.ofReal Real.pi⁻¹ • volume := by
    rw [standardComplexGaussianLaw_density]
    exact densityLaw_le_scaled_volume (ae_of_all _ standardComplexGaussianDensity_le)
  have h := Measure.map_mono hDom (measurable_const_smul σ)
  rw [Measure.map_smul, planar_volume_map_smul hσ, smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)] at h
  specialize h (Metric.closedBall z r)
  rw [Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall] at h
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [← hpi, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi⁻¹ * (σ ^ 2)⁻¹)] at h
  convert h using 1
  congr 1
  field_simp

theorem projectedComplexGaussian_pair_smallBall {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n)
    (hScale : Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    standardComplexGaussianVectorLaw n
      {z | ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j - w‖ ≤ r} ≤
        ENNReal.ofReal
          ((r / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) ^ 2) := by
  have hMeas : Measurable (fun z => projectedComplexGaussian E z i -
      projectedComplexGaussian E z j) := by
    exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp
      (projectedComplexGaussian_continuous E)).measurable.sub
        ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
          (projectedComplexGaussian_continuous E)).measurable
  have h := scaledStandardComplexGaussianLaw_closedBall_le
    (norm_ne_zero_iff.mpr hScale) hr w
  rw [← projectedComplexGaussian_pair_law E i j, Measure.map_apply hMeas measurableSet_closedBall] at h
  exact h

theorem projectedComplexGaussian_pair_smallBall_real {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n)
    (hScale : Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j - w‖ ≤ r} ≤
        (r / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) ^ 2 := by
  have h := ENNReal.toReal_mono (by finiteness)
    (projectedComplexGaussian_pair_smallBall E i j hScale hr w)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (sq_nonneg _)] using h

end CircularLaw
