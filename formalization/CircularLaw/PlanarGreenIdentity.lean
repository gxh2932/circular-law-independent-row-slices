import CircularLaw.SmoothedPlanarLog
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration by parts for the actual planar Laplacian

For a compactly supported C2 test and an arbitrary C2 weight, both
integrations by parts have their integrability obligations discharged by
continuity and the compact support of the test and its derivatives.
-/

noncomputable section
open Classical MeasureTheory
open scoped Topology Laplacian

namespace CircularLaw

theorem compact_second_direction_continuous (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (v : ℂ) :
    Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ f w v) z v) := by
  have hd : ContDiff ℝ 1 (fun z => fderiv ℝ f z v) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
  exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem compact_second_direction_support (f : ℂ → ℝ) (hSupport : HasCompactSupport f) (v : ℂ) :
    HasCompactSupport (fun z => fderiv ℝ (fun w => fderiv ℝ f w v) z v) :=
  (hSupport.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v

theorem planar_second_derivative_integration_by_parts (f g : ℂ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hSupport : HasCompactSupport f) (v : ℂ) :
    (∫ z : ℂ, g z * fderiv ℝ (fun w => fderiv ℝ f w v) z v) =
      ∫ z : ℂ, fderiv ℝ (fun w => fderiv ℝ g w v) z v * f z := by
  have hdf : ContDiff ℝ 1 (fun z => fderiv ℝ f z v) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
  have hdg : ContDiff ℝ 1 (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
  have hsdf := hSupport.fderiv_apply (𝕜 := ℝ) v
  have hsd2f := compact_second_direction_support f hSupport v
  have hDgDf : Integrable (fun z => fderiv ℝ g z v * fderiv ℝ f z v) volume :=
    (hdg.continuous.mul hdf.continuous).integrable_of_hasCompactSupport hsdf.mul_left
  have hGD2f : Integrable (fun z => g z * fderiv ℝ (fun w => fderiv ℝ f w v) z v) volume :=
    (hg.continuous.mul (compact_second_direction_continuous f hf v)).integrable_of_hasCompactSupport
      hsd2f.mul_left
  have hGDf : Integrable (fun z => g z * fderiv ℝ f z v) volume :=
    (hg.continuous.mul hdf.continuous).integrable_of_hasCompactSupport hsdf.mul_left
  have hD2gF : Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ g w v) z v * f z) volume :=
    ((compact_second_direction_continuous g hg v).mul hf.continuous).integrable_of_hasCompactSupport
      hSupport.mul_left
  have hDgF : Integrable (fun z => fderiv ℝ g z v * f z) volume :=
    (hdg.continuous.mul hf.continuous).integrable_of_hasCompactSupport hSupport.mul_left
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := g) (g := fun z => fderiv ℝ f z v) (v := v)
    hDgDf hGD2f hGDf (hg.differentiable (by norm_num)) (hdf.differentiable (by norm_num))
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun z => fderiv ℝ g z v) (g := f) (v := v)
    hD2gF hDgDf hDgF (hdg.differentiable (by norm_num)) (hf.differentiable (by norm_num))
  rw [h1, h2, neg_neg]

theorem planar_laplacian_continuous (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  have hFun : Δ f = fun z => fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I := by
    funext z
    exact planar_laplacian_eq_coordinate_second_derivatives f hf z
  rw [hFun]
  exact (compact_second_direction_continuous f hf 1).add
    (compact_second_direction_continuous f hf Complex.I)

theorem planar_laplacian_compact_support (f : ℂ → ℝ) (hSupport : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) : HasCompactSupport (Δ f) := by
  have hFun : Δ f = fun z => fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I := by
    funext z
    exact planar_laplacian_eq_coordinate_second_derivatives f hf z
  rw [hFun]
  exact (compact_second_direction_support f hSupport 1).add
    (compact_second_direction_support f hSupport Complex.I)

theorem planar_green_identity (f g : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hSupport : HasCompactSupport f) :
    (∫ z : ℂ, g z * (Δ f) z) = ∫ z : ℂ, (Δ g) z * f z := by
  have hi₁ : Integrable (fun z => g z * fderiv ℝ (fun w => fderiv ℝ f w 1) z 1) volume :=
    (hg.continuous.mul (compact_second_direction_continuous f hf 1)).integrable_of_hasCompactSupport
      (compact_second_direction_support f hSupport 1).mul_left
  have hiI : Integrable (fun z => g z *
      fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I) volume :=
    (hg.continuous.mul (compact_second_direction_continuous f hf Complex.I)).integrable_of_hasCompactSupport
      (compact_second_direction_support f hSupport Complex.I).mul_left
  have hj₁ : Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ g w 1) z 1 * f z) volume :=
    ((compact_second_direction_continuous g hg 1).mul hf.continuous).integrable_of_hasCompactSupport
      hSupport.mul_left
  have hjI : Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ g w Complex.I) z Complex.I * f z) volume :=
    ((compact_second_direction_continuous g hg Complex.I).mul hf.continuous).integrable_of_hasCompactSupport
      hSupport.mul_left
  simp_rw [planar_laplacian_eq_coordinate_second_derivatives f hf,
    planar_laplacian_eq_coordinate_second_derivatives g hg, mul_add, add_mul]
  rw [integral_add hi₁ hiI, integral_add hj₁ hjI,
    planar_second_derivative_integration_by_parts f g hf hg hSupport 1,
    planar_second_derivative_integration_by_parts f g hf hg hSupport Complex.I]

end CircularLaw
