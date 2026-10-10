import CircularLaw.BetaMeasureMoments
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.RealDeriv

/-!
# A Mellin representation for beta(alpha, 3/2)

The kernel sqrt(1-x) is continuous and vanishes for x >= 1. Its Mellin
transform is differentiable at every positive real parameter. The real
part is the unnormalized beta integral, also for logarithmic tests.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology

namespace CircularLaw

def betaHalfMellinKernel (x : ℝ) : ℂ := Real.sqrt (1 - x)

theorem beta_half_mellin_kernel_continuous : Continuous betaHalfMellinKernel := by
  unfold betaHalfMellinKernel
  fun_prop

theorem beta_half_mellin_kernel_zero {x : ℝ} (hx : 1 ≤ x) :
    betaHalfMellinKernel x = 0 := by
  simp only [betaHalfMellinKernel, Real.sqrt_eq_zero_of_nonpos (by linarith : 1 - x ≤ 0),
    Complex.ofReal_zero]

theorem beta_half_mellin_kernel_bound {x : ℝ} (hx : 0 ≤ x) :
    ‖betaHalfMellinKernel x‖ ≤ 1 := by
  simp only [betaHalfMellinKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (1 - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    _ = 1 := Real.sqrt_one

theorem beta_half_mellin_kernel_top (a : ℝ) :
    betaHalfMellinKernel =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  apply IsBigO.of_bound 0
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [beta_half_mellin_kernel_zero hx, norm_zero, zero_mul, le_refl]

theorem beta_half_mellin_kernel_zero_bound :
    betaHalfMellinKernel =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
    beta_half_mellin_kernel_bound (le_of_lt hx)

theorem beta_half_mellin_hasDerivAt {a : ℝ} (ha : 0 < a) :
    HasDerivAt (mellin betaHalfMellinKernel)
      (mellin (fun x => Real.log x • betaHalfMellinKernel x) (a : ℂ)) (a : ℂ) := by
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (beta_half_mellin_kernel_continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (beta_half_mellin_kernel_top (a + 1)) (by simp)
    beta_half_mellin_kernel_zero_bound (by simpa using ha)).2

theorem beta_half_mellin_real_test (a : ℝ) (g : ℝ → ℝ) :
    (mellin (fun x => (g x : ℂ) * betaHalfMellinKernel x) (a : ℂ)).re =
      ∫ x in Ioi (0 : ℝ), x ^ (a - 1) * g x * Real.sqrt (1 - x) := by
  unfold mellin
  have h : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((a : ℂ) - 1) •
      ((g x : ℂ) * betaHalfMellinKernel x)) =
      ∫ x in Ioi (0 : ℝ), ((x ^ (a - 1) * g x * Real.sqrt (1 - x) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [smul_eq_mul, betaHalfMellinKernel, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow (le_of_lt hx), mul_assoc]
  rw [h, integral_complex_ofReal, Complex.ofReal_re]

theorem beta_half_density_test (a : ℝ) (g : ℝ → ℝ) :
    (∫ x, betaPDFReal a (3 / 2) x * g x) =
      (1 / beta a (3 / 2)) *
        ∫ x in Ioi (0 : ℝ), x ^ (a - 1) * g x * Real.sqrt (1 - x) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioi (0 : ℝ)) (fun x hx => by
      simp only [mem_Ioi, not_lt] at hx
      simp [betaPDFReal, not_lt_of_ge hx])]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  by_cases hx1 : x < 1
  · rw [betaPDFReal, if_pos (show 0 < x ∧ x < 1 from ⟨hx, hx1⟩)]
    simp only [
      show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    ring
  · rw [betaPDFReal, if_neg (show ¬ (0 < x ∧ x < 1) from fun h => hx1 h.2),
      Real.sqrt_eq_zero_of_nonpos (by linarith : 1 - x ≤ 0)]
    simp

theorem beta_half_mellin_real_eq_beta {a : ℝ} (ha : 0 < a) :
    (mellin betaHalfMellinKernel (a : ℂ)).re = beta a (3 / 2) := by
  have hTest := beta_half_mellin_real_test a (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul, mul_one] at hTest
  have hNorm := beta_half_density_test a (fun _ => 1)
  simp only [mul_one] at hNorm
  rw [beta_density_real_integral_one ha (by norm_num), ← hTest] at hNorm
  have hPos := beta_pos ha (by norm_num : (0 : ℝ) < 3 / 2)
  field_simp at hNorm
  linarith

theorem beta_half_mellin_log_real (a : ℝ) :
    (mellin (fun x => Real.log x • betaHalfMellinKernel x) (a : ℂ)).re =
      ∫ x in Ioi (0 : ℝ), x ^ (a - 1) * Real.log x * Real.sqrt (1 - x) := by
  simpa only [Complex.real_smul] using beta_half_mellin_real_test a Real.log

end CircularLaw
