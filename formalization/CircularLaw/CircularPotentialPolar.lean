import CircularLaw.PlanarLogIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar integration for the circular measure's logarithmic potential

The actual area integral on the unit disk is reduced to radial integration.
Integrability is proved before Fubini is used, including the logarithmic
singularity on a circle. The angular integral retains its exact area factor.
-/

noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal

namespace CircularLaw

theorem circle_average_log_kernel (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w : ℂ => Real.log ‖w - z‖) 0 r =
      Real.log (max r ‖z‖) := by
  by_cases hz : ‖z‖ ≤ r
  · rw [max_eq_left hz]
    apply circleAverage_log_norm_sub_const_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, abs_of_pos hr] using hz
  · have hzr : r < ‖z‖ := lt_of_not_ge hz
    rw [max_eq_right hzr.le,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
    have hRatio : 1 ≤ r⁻¹ * ‖z‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hr]
      simpa using hzr.le
    have hRatioAbs : 1 ≤ |r⁻¹ * ‖z‖| := by
      simpa only [abs_of_nonneg (by positivity : 0 ≤ r⁻¹ * ‖z‖)] using hRatio
    simp only [zero_sub, norm_neg] at *
    rw [Real.posLog_eq_log hRatioAbs, Real.log_mul (inv_ne_zero hr.ne')
      (hr.trans hzr).ne', Real.log_inv]
    ring

theorem angular_log_kernel_integral (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
      Real.log ‖circleMap 0 r θ - z‖) =
      (2 * Real.pi) * Real.log (max r ‖z‖) := by
  have hPeriodic : Function.Periodic
      (fun θ : ℝ => Real.log ‖circleMap 0 r θ - z‖) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [periodic_circleMap 0 r θ]
  have hPeriod := hPeriodic.intervalIntegral_add_eq (-Real.pi) 0
  have hAverage := circle_average_log_kernel z hr
  rw [Real.circleAverage_def, smul_eq_mul] at hAverage
  have hAngle :
      (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        Real.log ‖circleMap 0 r θ - z‖) =
      ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        Real.log ‖circleMap 0 r θ - z‖ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    simpa only [zero_add, (by ring : -Real.pi + 2 * Real.pi = Real.pi)] using hPeriod
  rw [hAngle]
  exact (eq_inv_mul_iff_mul_eq₀ (by positivity : 2 * Real.pi ≠ 0)).mp hAverage.symm |>.symm

theorem unit_disk_integral_polar (f : ℂ → ℝ) (hf : Measurable f)
    (hInt : IntegrableOn f (Metric.closedBall 0 1) volume) :
    (∫ w : ℂ in Metric.closedBall 0 1, f w) =
      ∫ r : ℝ in Ioc 0 1, r *
        ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ) := by
  let g : ℂ → ℝ := (Metric.closedBall (0 : ℂ) 1).indicator f
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let F : ℝ × ℝ → ℝ := fun p => p.1 * g (Complex.polarCoord.symm p)
  have hg : Measurable g := hf.indicator measurableSet_closedBall
  have hgInt : Integrable g volume := hInt.integrable_indicator measurableSet_closedBall
  have hFMeas : Measurable F := by
    have hMap : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    exact measurable_fst.mul (hg.comp hMap)
  have hFInt : IntegrableOn F T volume := by
    refine ⟨hFMeas.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hAe : (fun p : ℝ × ℝ => ENNReal.ofReal ‖F p‖) =ᵐ[volume.restrict T]
        (fun p => ENNReal.ofReal p.1 • ENNReal.ofReal ‖g (Complex.polarCoord.symm p)‖) := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
      have hp0 : 0 < p.1 := hp.1
      simp only [F, norm_mul, Real.norm_eq_abs, abs_of_pos hp0,
        ENNReal.ofReal_mul hp0.le, smul_eq_mul]
    rw [lintegral_congr_ae hAe]
    calc
      _ = ∫⁻ w : ℂ, ENNReal.ofReal ‖g w‖ := by
        simpa only [T, polarCoord_target, smul_eq_mul, Real.norm_eq_abs] using
          Complex.lintegral_comp_polarCoord_symm (fun w => ENNReal.ofReal ‖g w‖)
      _ < ∞ := (hasFiniteIntegral_iff_norm _).mp hgInt.hasFiniteIntegral
  have hPolar : (∫ w : ℂ in Metric.closedBall 0 1, f w) =
      ∫ p : ℝ × ℝ in T, F p := by
    rw [← integral_indicator measurableSet_closedBall,
      ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    rfl
  rw [hPolar]
  change (∫ p : ℝ × ℝ in T, F p ∂volume.prod volume) = _
  rw [setIntegral_prod F hFInt]
  have hPolarMap (r θ : ℝ) : Complex.polarCoord.symm (r, θ) =
      circleMap 0 r θ := by
    simp only [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hInner (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, F (r, θ)) =
        (Ioc (0 : ℝ) 1).indicator (fun r => r *
          ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) r := by
    have hr0 : 0 < r := hr
    by_cases hr1 : r ≤ 1
    · rw [Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr0, hr1⟩)]
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      have hMem : Complex.polarCoord.symm (r, θ) ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hr0] using hr1
      change r * (Metric.closedBall (0 : ℂ) 1).indicator f
        (Complex.polarCoord.symm (r, θ)) = r * f (circleMap 0 r θ)
      rw [Set.indicator_of_mem hMem, hPolarMap]
    · rw [Set.indicator_of_notMem (fun h => hr1 h.2)]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro θ _
      have hNotMem : Complex.polarCoord.symm (r, θ) ∉ Metric.closedBall (0 : ℂ) 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hr0] using hr1
      simp only [F, g, Set.indicator_of_notMem hNotMem, mul_zero]
  calc
    _ = ∫ r : ℝ in Ioi 0, (Ioc (0 : ℝ) 1).indicator (fun r => r *
        ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) r :=
      setIntegral_congr_fun measurableSet_Ioi hInner
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr Ioc_subset_Ioi_self]

theorem unit_disk_log_kernel_integral_polar (z : ℂ) :
    (∫ w : ℂ in Metric.closedBall 0 1, Real.log ‖z - w‖) =
      (2 * Real.pi) * ∫ r : ℝ in Ioc 0 1, r * Real.log (max r ‖z‖) := by
  have hInt : IntegrableOn (fun w : ℂ => Real.log ‖z - w‖)
      (Metric.closedBall 0 1) volume := by
    simpa only [norm_sub_rev] using
      planar_log_kernel_integrableOn_closedBall z (by norm_num : (0 : ℝ) < 1)
  have hMeas : Measurable (fun w : ℂ => Real.log ‖z - w‖) :=
    Real.measurable_log.comp ((measurable_const.sub measurable_id).norm)
  rw [unit_disk_integral_polar (fun w : ℂ => Real.log ‖z - w‖) hMeas hInt]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hAngle : (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
      Real.log ‖z - circleMap 0 r θ‖) =
        (2 * Real.pi) * Real.log (max r ‖z‖) := by
    calc
      _ = ∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
          Real.log ‖circleMap 0 r θ - z‖ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro θ _
        dsimp only
        rw [norm_sub_rev]
      _ = _ := angular_log_kernel_integral z hr.1
  dsimp only
  rw [hAngle]
  ring

end CircularLaw
