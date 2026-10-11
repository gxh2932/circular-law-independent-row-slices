import CircularLaw.ComplexGaussianRadialTail
import CircularLaw.ProjectedGaussianSmallBall

/-!
# From absence of strong correlation to the source small-ball estimate

Correlation is defined by the actual projected Gaussian tail probability.
The exact radial tail forces a positive variance scale and bounds its
reciprocal. This proves the fixed-pair estimate used in LLTTY21 Lemma 4.8.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace CircularLaw

theorem scaledStandardComplexGaussianLaw_radial_tail {σ r : ℝ} (hσ : 0 < σ) (hr : 0 ≤ r) :
    (standardComplexGaussianLaw.map (σ • ContinuousLinearMap.id ℝ ℂ)).real
      {z | r ≤ ‖z‖} = Real.exp (-(r / σ) ^ 2) := by
  have hs : MeasurableSet {z : ℂ | r ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  rw [map_measureReal_apply (by fun_prop) hs]
  have hSet : (σ • ContinuousLinearMap.id ℝ ℂ) ⁻¹' {z | r ≤ ‖z‖} =
      {z : ℂ | r / σ ≤ ‖z‖} := by
    ext z
    change (r ≤ ‖σ • z‖) ↔ (r / σ ≤ ‖z‖)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ, div_le_iff₀ hσ, mul_comm]
  rw [hSet]
  exact standardComplexGaussianLaw_radial_tail (div_nonneg hr hσ.le)

theorem projectedComplexGaussian_pair_radial_tail {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n)
    (hScale : Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    (standardComplexGaussianVectorLaw n).real
      {z | r ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖} =
        Real.exp (-(r / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) ^ 2) := by
  have hMeas : Measurable (fun z => projectedComplexGaussian E z i -
      projectedComplexGaussian E z j) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp
      (projectedComplexGaussian_continuous E)).measurable.sub
        ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
          (projectedComplexGaussian_continuous E)).measurable
  have hs : MeasurableSet {z : ℂ | r ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have h := scaledStandardComplexGaussianLaw_radial_tail (norm_pos_iff.mpr hScale) hr
  rw [← projectedComplexGaussian_pair_law E i j, map_measureReal_apply hMeas hs] at h
  exact h

def projectedGaussianStronglyCorrelated {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (α β : ℝ) (i j : Fin n) : Prop :=
  (standardComplexGaussianVectorLaw n).real
    {z | α ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖} ≤ β

theorem projectedGaussian_noncorrelation_scale_ne_zero {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hNot : ¬ projectedGaussianStronglyCorrelated E α β i j) :
    Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j) ≠ 0 := by
  intro hZero
  have hPair (z : Fin n → ℂ) : projectedComplexGaussian E z i -
      projectedComplexGaussian E z j = 0 := by
    rw [← gaussianCoordinateDifferenceVector_inner, projectedComplexGaussian_inner, hZero,
      inner_zero_left]
  apply hNot
  unfold projectedGaussianStronglyCorrelated
  have hSet : {z | α ≤ ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖} =
      (∅ : Set (Fin n → ℂ)) := by
    ext z
    simp only [hPair, norm_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    linarith
  rw [hSet, measureReal_empty]
  exact hβ

theorem projectedGaussian_noncorrelation_ratio_bound {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hNot : ¬ projectedGaussianStronglyCorrelated E α β i j) :
    α / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖ ≤
      Real.sqrt (Real.log (1 / β)) := by
  have hScale := projectedGaussian_noncorrelation_scale_ne_zero E i j hα hβ.le hNot
  have hTail : β < Real.exp
      (-(α / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) ^ 2) := by
    have h := lt_of_not_ge hNot
    unfold projectedGaussianStronglyCorrelated at h
    rwa [projectedComplexGaussian_pair_radial_tail E i j hScale hα.le] at h
  have hPow : (α / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) ^ 2 ≤
      Real.log (1 / β) := by
    have hLog := (Real.log_lt_iff_lt_exp hβ).mpr hTail
    rw [one_div, Real.log_inv]
    linarith
  have hLogPos : 0 < Real.log (1 / β) := Real.log_pos ((one_lt_div hβ).mpr hβ1)
  apply (sq_le_sq₀ (div_nonneg hα.le (norm_nonneg _)) (Real.sqrt_nonneg _)).mp
  rwa [Real.sq_sqrt hLogPos.le]

theorem projectedGaussian_noncorrelation_smallBall {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n)
    {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s)
    (hNot : ¬ projectedGaussianStronglyCorrelated E α β i j) (w : ℂ) :
    (standardComplexGaussianVectorLaw n).real
      {z | ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j - w‖ ≤
        α * s / Real.sqrt (Real.log (1 / β))} ≤ s ^ 2 := by
  have hScale := projectedGaussian_noncorrelation_scale_ne_zero E i j hα hβ.le hNot
  have hSqrt : 0 < Real.sqrt (Real.log (1 / β)) :=
    Real.sqrt_pos.mpr (Real.log_pos ((one_lt_div hβ).mpr hβ1))
  have hRatio := projectedGaussian_noncorrelation_ratio_bound E i j hα hβ hβ1 hNot
  have hDiv : (α / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) /
      Real.sqrt (Real.log (1 / β)) ≤ 1 := (div_le_one hSqrt).mpr hRatio
  have hr : 0 ≤ α * s / Real.sqrt (Real.log (1 / β)) := by positivity
  have hRadius : (α * s / Real.sqrt (Real.log (1 / β))) /
      ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖ ≤ s := by
    calc
      _ = s * ((α / ‖Eᗮ.starProjection (gaussianCoordinateDifferenceVector i j)‖) /
        Real.sqrt (Real.log (1 / β))) := by ring
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left hDiv hs
      _ = s := mul_one _
  exact (projectedComplexGaussian_pair_smallBall_real E i j hScale hr w).trans
    (pow_le_pow_left₀ (div_nonneg hr (norm_nonneg _)) hRadius 2)

end CircularLaw
