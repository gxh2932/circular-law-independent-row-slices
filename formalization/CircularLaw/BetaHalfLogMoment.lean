import CircularLaw.BetaHalfMellin
import CircularLaw.BetaCatalanMoments
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The logarithmic moment of beta(1/2,3/2)

Differentiation of the actual Mellin integral and of its Gamma quotient
gives the logarithmic moment -2*log(2)-1. The Gamma derivative constants
cancel, leaving a closed value with no derivative or integrability premise.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace CircularLaw

theorem beta_half_hasDerivAt :
    HasDerivAt (fun a : ℝ => beta a (3 / 2))
      (beta (1 / 2) (3 / 2) * (-2 * Real.log 2 - 1)) (1 / 2) := by
  have hTwo : HasDerivAt Real.Gamma (1 - Real.eulerMascheroniConstant) (2 : ℝ) := by
    convert Real.hasDerivAt_Gamma_nat 1 using 1 <;>
      norm_num [sub_eq_add_neg, add_comm]
  have hDen : HasDerivAt (fun a : ℝ => Real.Gamma (a + 3 / 2))
      (1 - Real.eulerMascheroniConstant) (1 / 2) := by
    have hPoint : HasDerivAt Real.Gamma (1 - Real.eulerMascheroniConstant)
        ((1 / 2 : ℝ) + 3 / 2) := by convert hTwo using 1; norm_num
    simpa using hPoint.comp (1 / 2) ((hasDerivAt_id (1 / 2 : ℝ)).add_const (3 / 2))
  have hDenVal : Real.Gamma ((1 / 2 : ℝ) + 3 / 2) = 1 := by
    norm_num [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  have hThree : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1
    · norm_num
    · rw [Real.Gamma_one_half_eq]
      ring
  change HasDerivAt (fun a : ℝ => Real.Gamma a * Real.Gamma (3 / 2) /
    Real.Gamma (a + 3 / 2)) _ (1 / 2)
  refine ((Real.hasDerivAt_Gamma_one_half.mul_const _).div hDen
    (by rw [hDenVal]; norm_num)).congr_deriv ?_
  rw [hDenVal, hThree, Real.Gamma_one_half_eq, beta_half_three_halves_constant]
  ring_nf
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

theorem beta_half_log_raw_integral :
    (∫ x in Ioi (0 : ℝ),
      x ^ ((1 / 2 : ℝ) - 1) * Real.log x * Real.sqrt (1 - x)) =
        beta (1 / 2) (3 / 2) * (-2 * Real.log 2 - 1) := by
  have h := (beta_half_mellin_hasDerivAt (by norm_num : (0 : ℝ) < 1 / 2)).real_of_complex
  have hEq : (fun a : ℝ => beta a (3 / 2)) =ᶠ[𝓝 (1 / 2 : ℝ)]
      (fun a : ℝ => (mellin betaHalfMellinKernel (a : ℂ)).re) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
    exact (beta_half_mellin_real_eq_beta ha).symm
  have hUnique := (h.congr_of_eventuallyEq hEq).unique beta_half_hasDerivAt
  rw [beta_half_mellin_log_real] at hUnique
  exact hUnique

theorem beta_half_log_density_integral :
    (∫ x, betaPDFReal (1 / 2) (3 / 2) x * Real.log x) = -2 * Real.log 2 - 1 := by
  rw [beta_half_density_test, beta_half_log_raw_integral]
  have hNonzero := (beta_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 3 / 2)).ne'
  field_simp

theorem beta_half_log_measure_integral :
    (∫ x, Real.log x ∂betaMeasure (1 / 2) (3 / 2)) = -2 * Real.log 2 - 1 := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul
    (beta_density_measurable (1 / 2) (3 / 2))
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, beta_density_toReal (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 3 / 2)]
  exact beta_half_log_density_integral

end CircularLaw
