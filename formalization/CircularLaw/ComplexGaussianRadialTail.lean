import CircularLaw.ComplexGaussianDensity
import CircularLaw.PlanarGaussian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Exact radial tails of the source complex Gaussian

The density is integrated in polar coordinates. The real radial integral
uses its explicit antiderivative and limit at infinity; no distributional
tail formula is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace CircularLaw

theorem gaussian_radial_integral_Ioi (r : ℝ) :
    (∫ x in Ioi r, x * Real.exp (-x ^ 2)) = (1 / 2 : ℝ) * Real.exp (-r ^ 2) := by
  have hDeriv (x : ℝ) : HasDerivAt (fun t : ℝ => -(2 : ℝ)⁻¹ * Real.exp (-t ^ 2))
      (x * Real.exp (-x ^ 2)) x := by
    convert ((hasDerivAt_pow 2 x).neg.exp.const_mul (-(2 : ℝ)⁻¹)) using 1
    dsimp
    ring
  have hLimit : Tendsto (fun t : ℝ => -(2 : ℝ)⁻¹ * Real.exp (-t ^ 2)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))).const_mul
        (-(2 : ℝ)⁻¹)
    simpa using h
  have hInt : Integrable (fun x : ℝ => x * Real.exp (-x ^ 2)) volume := by
    simpa only [neg_mul, one_mul] using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := r)
    (fun x _ => hDeriv x) hInt.integrableOn hLimit
  simpa only [zero_sub, neg_mul, neg_neg, inv_eq_one_div] using h

theorem planarGaussian_radial_tail_integral {r : ℝ} (hr : 0 ≤ r) :
    (∫ z : ℂ in {z | r < ‖z‖}, Real.exp (-‖z‖ ^ 2)) =
      Real.pi * Real.exp (-r ^ 2) := by
  have hs : MeasurableSet {z : ℂ | r < ‖z‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  let f : ℂ → ℝ := {z : ℂ | r < ‖z‖}.indicator (fun z => Real.exp (-‖z‖ ^ 2))
  calc
    (∫ z : ℂ in {z | r < ‖z‖}, Real.exp (-‖z‖ ^ 2)) = ∫ z, f z :=
      (integral_indicator hs).symm
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • f (Complex.polarCoord.symm p) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    _ = (∫ x in Ioi (0 : ℝ), (Ioi r).indicator (fun x => x * Real.exp (-x ^ 2)) x) *
        ∫ _ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, ← Measure.volume_eq_prod]
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      simp only [f, Set.indicator_apply, mem_setOf_eq, mem_Ioi, Complex.norm_polarCoord_symm,
        abs_of_pos hp0, smul_eq_mul, mul_one]
      split_ifs <;> simp
    _ = (∫ x in Ioi r, x * Real.exp (-x ^ 2)) * (2 * Real.pi) := by
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        Ioi_inter_Ioi, max_eq_left hr]
      simp only [setIntegral_const, smul_eq_mul, mul_one,
        Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      congr 1
      ring
    _ = Real.pi * Real.exp (-r ^ 2) := by
      rw [gaussian_radial_integral_Ioi]
      ring

theorem standardComplexGaussianLaw_strict_radial_tail {r : ℝ} (hr : 0 ≤ r) :
    standardComplexGaussianLaw.real {z | r < ‖z‖} = Real.exp (-r ^ 2) := by
  have hs : MeasurableSet {z : ℂ | r < ‖z‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hNonneg (z : ℂ) : 0 ≤ standardComplexGaussianDensity z := by
    unfold standardComplexGaussianDensity
    positivity
  have hD : Measurable (fun z => ENNReal.ofReal (standardComplexGaussianDensity z)) := by
    unfold standardComplexGaussianDensity
    fun_prop
  calc
    standardComplexGaussianLaw.real {z | r < ‖z‖} =
        ∫ _ : ℂ in {z | r < ‖z‖}, (1 : ℝ) ∂standardComplexGaussianLaw := by simp
    _ = ∫ z : ℂ in {z | r < ‖z‖}, standardComplexGaussianDensity z := by
      rw [standardComplexGaussianLaw_density, densityLaw,
        setIntegral_withDensity_eq_setIntegral_toReal_smul hD
          (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) _ hs]
      simp only [ENNReal.toReal_ofReal (hNonneg _),
        smul_eq_mul, mul_one]
    _ = Real.pi⁻¹ * (Real.pi * Real.exp (-r ^ 2)) := by
      simp only [standardComplexGaussianDensity]
      rw [integral_const_mul, planarGaussian_radial_tail_integral hr]
    _ = Real.exp (-r ^ 2) := by field_simp

theorem standardComplexGaussianLaw_sphere_zero (r : ℝ) :
    standardComplexGaussianLaw (Metric.sphere 0 r) = 0 := by
  have hDom : standardComplexGaussianLaw ≤ ENNReal.ofReal Real.pi⁻¹ • volume := by
    rw [standardComplexGaussianLaw_density]
    exact densityLaw_le_scaled_volume (ae_of_all _ standardComplexGaussianDensity_le)
  apply le_antisymm _ bot_le
  simpa only [Measure.smul_apply, Measure.addHaar_sphere, smul_eq_mul, mul_zero] using
    hDom (Metric.sphere 0 r)

theorem standardComplexGaussianLaw_radial_tail {r : ℝ} (hr : 0 ≤ r) :
    standardComplexGaussianLaw.real {z | r ≤ ‖z‖} = Real.exp (-r ^ 2) := by
  have hSphere : ∀ᵐ z ∂standardComplexGaussianLaw, z ∉ Metric.sphere 0 r := by
    simp only [Metric.mem_sphere, dist_zero_right]
    apply ae_iff.mpr
    simpa only [not_not, Metric.sphere, dist_zero_right] using standardComplexGaussianLaw_sphere_zero r
  have hAe : {z : ℂ | r ≤ ‖z‖} =ᵐ[standardComplexGaussianLaw] {z | r < ‖z‖} := by
    filter_upwards [hSphere] with z hz
    have hNe : ‖z‖ ≠ r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    apply propext
    change (r ≤ ‖z‖) ↔ (r < ‖z‖)
    constructor
    · intro h
      exact lt_of_le_of_ne h hNe.symm
    · exact le_of_lt
  rw [measureReal_congr hAe, standardComplexGaussianLaw_strict_radial_tail hr]

end CircularLaw
