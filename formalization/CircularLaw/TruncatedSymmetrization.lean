import CircularLaw.GaussianSumConcentration

/-!
# Concentration deficits and truncated symmetrized moments

The law of the difference of independent copies has no greater probability
in a ball about zero than the original law's concentration function.
Consequently its truncated second moment controls the concentration deficit.
These statements apply to arbitrary planar probability laws, including atoms.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution BigOperators

namespace CircularLaw

def planarConcentration (μ : Measure ℂ) (r : ℝ) : ℝ :=
  (levyConcentration μ id r).toReal

theorem levyConcentration_probability_le_one (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (X : ℂ → ℂ) (r : ℝ) : levyConcentration μ X r ≤ 1 := by
  apply iSup_le
  intro z
  exact prob_le_one

theorem levyConcentration_probability_ne_top (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (X : ℂ → ℂ) (r : ℝ) : levyConcentration μ X r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (levyConcentration_probability_le_one μ X r)

theorem planarConcentration_nonneg (μ : Measure ℂ) (r : ℝ) :
    0 ≤ planarConcentration μ r := ENNReal.toReal_nonneg

theorem planarConcentration_le_one (μ : Measure ℂ) [IsProbabilityMeasure μ] (r : ℝ) :
    planarConcentration μ r ≤ 1 := by
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top (levyConcentration_probability_le_one μ id r)

theorem probability_closedBall_le_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (r : ℝ) (z : ℂ) : μ.real (Metric.closedBall z r) ≤ planarConcentration μ r := by
  apply ENNReal.toReal_mono (levyConcentration_probability_ne_top μ id r)
  simpa only [Metric.closedBall, dist_eq_norm, id_eq] using
    (le_iSup (fun z : ℂ => μ {x | ‖id x - z‖ ≤ r}) z)

theorem symmetrized_probability_closedBall_le_concentration
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (r : ℝ) :
    (symmetrizedLaw μ).real (Metric.closedBall 0 r) ≤ planarConcentration μ r := by
  classical
  haveI : IsProbabilityMeasure (μ.map (fun x => -x)) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  have hInd : Integrable ((Metric.closedBall (0 : ℂ) r).indicator (fun _ => (1 : ℝ)))
      (symmetrizedLaw μ) := (integrable_const 1).indicator measurableSet_closedBall
  have hProd : Integrable (fun p : ℂ × ℂ => (Metric.closedBall (0 : ℂ) r).indicator
      (fun _ => (1 : ℝ)) (p.1 + p.2)) (μ.prod (μ.map (fun x => -x))) :=
    (integrable_map_measure hInd.aestronglyMeasurable measurable_add.aemeasurable).mp hInd
  rw [← integral_indicator_one measurableSet_closedBall]
  change (∫ x, (Metric.closedBall (0 : ℂ) r).indicator (fun _ => (1 : ℝ)) x
    ∂symmetrizedLaw μ) ≤ planarConcentration μ r
  rw [symmetrizedLaw, integral_conv hInd]
  calc
    _ ≤ ∫ _ : ℂ, planarConcentration μ r ∂μ := by
      apply integral_mono hProd.integral_prod_left
        (integrable_const (planarConcentration μ r))
      intro x
      change (∫ y, (Metric.closedBall (0 : ℂ) r).indicator (fun _ => (1 : ℝ))
        (x + y) ∂μ.map (fun y => -y)) ≤ planarConcentration μ r
      have hF : AEStronglyMeasurable (fun y : ℂ => (Metric.closedBall (0 : ℂ) r).indicator
          (fun _ => (1 : ℝ)) (x + y)) (μ.map (fun y => -y)) := by
        exact ((measurable_const.indicator measurableSet_closedBall).comp
          (measurable_const.add measurable_id)).aestronglyMeasurable
      rw [integral_map measurable_neg.aemeasurable hF]
      have hEq : (fun y : ℂ => (Metric.closedBall (0 : ℂ) r).indicator
          (fun _ => (1 : ℝ)) (x + -y)) =
          (Metric.closedBall x r).indicator (fun _ => (1 : ℝ)) := by
        funext y
        simp only [Set.indicator_apply, Metric.mem_closedBall, dist_eq_norm, sub_zero, ← sub_eq_add_neg,
          norm_sub_rev]
      rw [hEq, integral_indicator_const _ measurableSet_closedBall]
      simp only [smul_eq_mul, mul_one]
      exact probability_closedBall_le_concentration μ r x
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

def truncatedNormSq (r : ℝ) (x : ℂ) : ℝ := min ‖x‖ r ^ 2

theorem truncatedNormSq_nonneg (r : ℝ) (x : ℂ) :
    0 ≤ truncatedNormSq r x := sq_nonneg _

theorem truncatedNormSq_le {r : ℝ} (hr : 0 ≤ r) (x : ℂ) :
    truncatedNormSq r x ≤ r ^ 2 :=
  pow_le_pow_left₀ (le_min (norm_nonneg _) hr) (min_le_right _ _) 2

theorem truncatedNormSq_integrable (ν : Measure ℂ) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 ≤ r) : Integrable (truncatedNormSq r) ν := by
  apply integrable_of_abs_bound ν (by unfold truncatedNormSq; fun_prop) (C := r ^ 2)
  intro x
  rw [abs_of_nonneg (truncatedNormSq_nonneg r x)]
  exact truncatedNormSq_le hr x

theorem probability_outside_closedBall_mul_le_truncated_moment
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 * ν.real (Metric.closedBall (0 : ℂ) r)ᶜ ≤
      ∫ x, truncatedNormSq r x ∂ν := by
  have h := integral_mono
    ((integrable_const (r ^ 2)).indicator measurableSet_closedBall.compl)
    (truncatedNormSq_integrable ν hr) (fun x => by
      by_cases hx : x ∈ (Metric.closedBall (0 : ℂ) r)ᶜ
      · rw [Set.indicator_of_mem hx]
        have hlt : r < ‖x‖ := by
          simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero,
            not_le] using hx
        have hn := hlt.le
        rw [truncatedNormSq, min_eq_right hn]
      · rw [Set.indicator_of_notMem hx]
        exact truncatedNormSq_nonneg r x)
  rw [integral_indicator_const _ measurableSet_closedBall.compl] at h
  simpa only [smul_eq_mul, mul_comm] using h

def truncatedSymmetrizedMoment (μ : Measure ℂ) (r : ℝ) : ℝ :=
  ∫ x, truncatedNormSq r x ∂symmetrizedLaw μ

theorem concentration_deficit_le_truncated_symmetrized_moment
    (μ : Measure ℂ) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 * (1 - planarConcentration μ r) ≤ truncatedSymmetrizedMoment μ r := by
  have h := probability_outside_closedBall_mul_le_truncated_moment (symmetrizedLaw μ) hr
  rw [probReal_compl_eq_one_sub measurableSet_closedBall] at h
  exact (mul_le_mul_of_nonneg_left
    (sub_le_sub_left (symmetrized_probability_closedBall_le_concentration μ r) 1)
      (sq_nonneg r)).trans h

theorem sum_concentration_deficits_le_truncated_symmetrized_moments
    {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 * (∑ i, (1 - planarConcentration (μ i) r)) ≤
      ∑ i, truncatedSymmetrizedMoment (μ i) r := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ =>
    concentration_deficit_le_truncated_symmetrized_moment (μ i) hr)

end CircularLaw
