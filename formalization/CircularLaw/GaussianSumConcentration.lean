import CircularLaw.GaussianConcentration
import CircularLaw.FourierLevels

/-!
# Gaussian concentration bounds for independent sums

The actual product sum law has a characteristic function bounded by the
exponential of the sum of its symmetrized defects. This gives the Gaussian
integral bound in the general planar concentration proof, with no density
or assumed concentration estimate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace CircularLaw

theorem nonneg_le_exp_neg_sq_defect {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.exp (-(1 - x ^ 2) / 2) := by
  have h := rpow_le_exp_neg_defect hx (show (0 : ℝ) < 1 by norm_num)
  simp only [Real.rpow_eq_pow, Real.rpow_one, one_mul] at h
  exact h.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x - 1)]))

def sumCharDefect {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ) (t : ℂ) : ℝ :=
  ∑ i, (1 - ‖charFun (μ i) t‖ ^ 2)

theorem sumCharDefect_nonneg {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (t : ℂ) :
    0 ≤ sumCharDefect μ t := by
  apply Finset.sum_nonneg
  intro i _
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one (μ := μ i) t) 2
  simpa only [one_pow, sub_nonneg] using h

theorem measurable_sumCharDefect {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] :
    Measurable (sumCharDefect μ) := by
  unfold sumCharDefect
  fun_prop

theorem norm_charFun_productSumLaw_le_exp_defect {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (t : ℂ) :
    ‖charFun (productSumLaw μ) t‖ ≤ Real.exp (-sumCharDefect μ t / 2) := by
  classical
  rw [charFun_productSumLaw, norm_prod, sumCharDefect]
  calc
    _ ≤ ∏ i, Real.exp (-(1 - ‖charFun (μ i) t‖ ^ 2) / 2) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ =>
        nonneg_le_exp_neg_sq_defect (norm_nonneg _))
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

theorem gaussian_sum_defect_integrable {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun t => Real.exp (-b * ‖t‖ ^ 2 - sumCharDefect μ t / 2)) volume := by
  apply (planarGaussian_integrable hb).mono'
  · exact ((by fun_prop : Measurable (fun t : ℂ => -b * ‖t‖ ^ 2)).sub
      ((measurable_sumCharDefect μ).div_const 2)).exp.aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h := sumCharDefect_nonneg μ t
    linarith

theorem gaussian_product_sum_small_ball {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (productSumLaw μ).real (Metric.closedBall z r) ≤
      Real.exp 1 * (r ^ 2 / (4 * Real.pi)) *
        (∫ t, Real.exp (-(r ^ 2 / 4) * ‖t‖ ^ 2 - sumCharDefect μ t / 2)) := by
  have hb : 0 < r ^ 2 / 4 := by positivity
  have hInt := integral_mono (gaussian_modulus_integrable (productSumLaw μ) hb)
    (gaussian_sum_defect_integrable μ hb) (fun t => by
      dsimp only [planarGaussian]
      rw [sub_eq_add_neg, Real.exp_add]
      simpa only [neg_div] using
        mul_le_mul_of_nonneg_left (norm_charFun_productSumLaw_le_exp_defect μ t)
          (Real.exp_pos (-(r ^ 2 / 4) * ‖t‖ ^ 2)).le)
  exact (gaussian_planar_small_ball (productSumLaw μ) hr z).trans
    (mul_le_mul_of_nonneg_left hInt (by positivity))

theorem productSumLaw_eq_independent_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ) :
    productSumLaw (fun i => μ.map (X i)) = μ.map (fun ω => ∑ i, X i ω) := by
  have hJoint := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hInd
  rw [productSumLaw, ← hJoint, Measure.map_map measurable_finite_sum
    (measurable_pi_lambda _ hX)]
  rfl

theorem gaussian_independent_sum_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℂ) (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    μ.real {ω | ‖(∑ i, X i ω) - z‖ ≤ r} ≤
      Real.exp 1 * (r ^ 2 / (4 * Real.pi)) *
        (∫ t, Real.exp (-(r ^ 2 / 4) * ‖t‖ ^ 2 -
          sumCharDefect (fun i => μ.map (X i)) t / 2)) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (X i)) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have h := gaussian_product_sum_small_ball (fun i => μ.map (X i)) hr z
  rw [productSumLaw_eq_independent_sum μ X hX hInd, measureReal_def,
    Measure.map_apply (Finset.measurable_sum _ (fun i _ => hX i))
      measurableSet_closedBall] at h
  simpa only [Metric.mem_closedBall, dist_eq_norm, Set.preimage, measureReal_def] using h

end CircularLaw
