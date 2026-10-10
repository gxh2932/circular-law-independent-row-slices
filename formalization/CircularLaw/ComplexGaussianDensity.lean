import CircularLaw.ComplexGaussianLinearForm
import CircularLaw.DensityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The actual planar density of the standard complex Gaussian

Transport of the two real Gaussian densities gives `exp(-norm(z)^2)/pi`.
The resulting disk small-ball bound holds at every deterministic centre.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CircularLaw

def standardComplexGaussianDensity (z : ℂ) : ℝ :=
  Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2)

theorem standardGaussianPairLaw_density_product (p : ℝ × ℝ) :
    gaussianPDF 0 (1 / 2) p.1 * gaussianPDF 0 (1 / 2) p.2 =
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2))) := by
  rw [gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  have hPDF (x : ℝ) : gaussianPDFReal 0 (1 / 2) x =
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
    have hHalf : ((1 / 2 : NNReal) : ℝ) = (1 / 2 : ℝ) := by norm_num
    have hpi : (2 : ℝ) * Real.pi * (1 / 2) = Real.pi := by ring
    have hTwo : (2 : ℝ) * (1 / 2) = 1 := by norm_num
    rw [gaussianPDFReal, hHalf, hpi, hTwo, sub_zero, div_one]
  rw [hPDF, hPDF]
  rw [mul_mul_mul_comm, ← mul_inv_rev, Real.mul_self_sqrt Real.pi_pos.le, ← Real.exp_add]
  congr 1
  ring

theorem standardGaussianPairLaw_density :
    standardGaussianPairLaw = (volume : Measure (ℝ × ℝ)).withDensity
      (fun p => ENNReal.ofReal (standardComplexGaussianDensity (Complex.equivRealProdCLM.symm p))) := by
  rw [standardGaussianPairLaw, gaussianReal_of_var_ne_zero _ (by norm_num),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    ← Measure.volume_eq_prod]
  congr 1
  funext p
  rw [standardGaussianPairLaw_density_product]
  congr 1
  rw [standardComplexGaussianDensity, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.equivRealProdCLM_symm_apply_re,
    Complex.equivRealProdCLM_symm_apply_im, pow_two]

theorem standardComplexGaussianLaw_density :
    standardComplexGaussianLaw = densityLaw standardComplexGaussianDensity := by
  have hF : Measurable (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) := by fun_prop
  have hD : Measurable (fun z : ℂ => ENNReal.ofReal (standardComplexGaussianDensity z)) := by
    unfold standardComplexGaussianDensity
    fun_prop
  ext s hs
  rw [standardComplexGaussianLaw, Measure.map_apply hF hs,
    standardGaussianPairLaw_density, withDensity_apply _ (hF hs),
    densityLaw, withDensity_apply _ hs]
  exact Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage hs hD

theorem standardComplexGaussianDensity_le (z : ℂ) :
    standardComplexGaussianDensity z ≤ Real.pi⁻¹ := by
  unfold standardComplexGaussianDensity
  calc
    Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2) ≤ Real.pi⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr (sq_nonneg _)))
        (inv_nonneg.mpr Real.pi_pos.le)
    _ = Real.pi⁻¹ := mul_one _

theorem standardComplexGaussianLaw_closedBall_le {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    standardComplexGaussianLaw (Metric.closedBall z r) ≤ ENNReal.ofReal (r ^ 2) := by
  rw [standardComplexGaussianLaw_density]
  have h := densityLaw_closedBall_le (inv_nonneg.mpr Real.pi_pos.le) hr
    (ae_of_all _ standardComplexGaussianDensity_le) z
  convert h using 1
  congr 1
  field_simp

end CircularLaw
