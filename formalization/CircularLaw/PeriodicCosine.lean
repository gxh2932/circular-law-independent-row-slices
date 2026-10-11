import CircularLaw.GaussianLattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A Gaussian bound for the periodic cosine kernel

On one period, the cosine defect has a quadratic lower bound. Gaussian
lattice weights control the translated periods, giving an explicit integral
bound on the real line. This is the one-dimensional analytic input to the
planar concentration estimate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace CircularLaw

def periodicCosineKernel (a x : ℝ) : ℝ := Real.exp (-a * (1 - Real.cos (2 * Real.pi * x)))

def gaussianCosineKernel (b a x : ℝ) : ℝ := Real.exp (-b * x ^ 2) * periodicCosineKernel a x

theorem cosine_defect_quadratic_on_period {x : ℝ} (hx : |x| ≤ 1 / 2) :
    8 * x ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  have hAngle : |2 * Real.pi * x| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  have h := Real.cos_le_one_sub_mul_cos_sq hAngle
  have hScale : 2 / Real.pi ^ 2 * (2 * Real.pi * x) ^ 2 = 8 * x ^ 2 := by
    field_simp
    ring
  rw [hScale] at h
  linarith

theorem periodicCosineKernel_integer_shift (a x : ℝ) (n : ℤ) :
    periodicCosineKernel a (x + n) = periodicCosineKernel a x := by
  unfold periodicCosineKernel
  rw [show 2 * Real.pi * (x + n) = 2 * Real.pi * x + (n : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi]

theorem periodicCosineKernel_le_one {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    periodicCosineKernel a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
    (sub_nonneg.mpr (Real.cos_le_one _))

theorem periodicCosineKernel_intervalIntegrable (a : ℝ) (u v : ℝ) :
    IntervalIntegrable (periodicCosineKernel a) volume u v := by
  apply Continuous.intervalIntegrable
  unfold periodicCosineKernel
  fun_prop

theorem periodicCosineKernel_period_integral_le {a : ℝ} (ha : 0 < a) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), periodicCosineKernel a x) ≤
      Real.sqrt (Real.pi / (8 * a)) := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
    (periodicCosineKernel_intervalIntegrable a _ _)
    (integrable_exp_neg_mul_sq (by positivity : 0 < 8 * a)).intervalIntegrable
    (fun x hx => by
      apply Real.exp_le_exp.mpr
      have hAbs : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hDefect := mul_le_mul_of_nonneg_left
        (cosine_defect_quadratic_on_period hAbs) ha.le
      nlinarith)
  have hGlobal := setIntegral_le_integral (s := Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ))
    (integrable_exp_neg_mul_sq (by positivity : 0 < 8 * a))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
    integral_gaussian] at hGlobal
  exact h.trans hGlobal

theorem gaussianCosineKernel_integrable {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    Integrable (gaussianCosineKernel b a) volume := by
  apply (integrable_exp_neg_mul_sq hb).mono'
  · unfold gaussianCosineKernel periodicCosineKernel
    fun_prop
  · apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (by unfold gaussianCosineKernel periodicCosineKernel; positivity)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (periodicCosineKernel_le_one ha x)

theorem gaussianCosineKernel_cell_integral_le {b a : ℝ} (hb : 0 < b) (n : ℤ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), gaussianCosineKernel b a (x + n)) ≤
      Real.exp (-(b / 4) * (n : ℝ) ^ 2) *
        (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), periodicCosineKernel a x) := by
  have hf : IntervalIntegrable (fun x => gaussianCosineKernel b a (x + n)) volume
      (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    apply Continuous.intervalIntegrable
    unfold gaussianCosineKernel periodicCosineKernel
    fun_prop
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num) hf
    ((periodicCosineKernel_intervalIntegrable a _ _).const_mul _)
  intro x hx
  rw [gaussianCosineKernel, periodicCosineKernel_integer_shift]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have hAbs : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hSq := mul_le_mul_of_nonneg_left (translated_integer_sq_lower n hAbs) hb.le
  nlinarith

theorem gaussianCosineKernel_integral_le {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    (∫ x, gaussianCosineKernel b a x) ≤
      (1 + 2 * Real.sqrt (Real.pi / (b / 4))) * Real.sqrt (Real.pi / (8 * a)) := by
  let P := ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), periodicCosineKernel a x
  have hP : 0 ≤ P := intervalIntegral.integral_nonneg (by norm_num)
    (fun _ _ => (Real.exp_pos _).le)
  have hSum : HasSum (fun n : ℤ => ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      gaussianCosineKernel b a (x + n)) (∫ x, gaussianCosineKernel b a x) := by
    convert (gaussianCosineKernel_integrable hb ha.le).hasSum_intervalIntegral (-1 / 2) using 1
    funext n
    rw [intervalIntegral.integral_comp_add_right]
    congr 1
    ring
  have hWeight := gaussian_integer_summable (by positivity : 0 < b / 4)
  have h := hSum.summable.tsum_le_tsum (fun n => gaussianCosineKernel_cell_integral_le hb n)
    (hWeight.mul_right P)
  rw [hSum.tsum_eq, tsum_mul_right] at h
  calc
    _ ≤ (∑' n : ℤ, Real.exp (-(b / 4) * (n : ℝ) ^ 2)) * P := h
    _ ≤ (1 + 2 * Real.sqrt (Real.pi / (b / 4))) * P :=
      mul_le_mul_of_nonneg_right (gaussian_integer_tsum_le (by positivity : 0 < b / 4)) hP
    _ ≤ _ := mul_le_mul_of_nonneg_left (periodicCosineKernel_period_integral_le ha) (by positivity)

end CircularLaw
