import CircularLaw.PlanarDisk
import CircularLaw.PlanarDensityScale

/-!
# Area domination after uniform disk smoothing

Convolving a law with uniform disk noise converts a small-ball bound
for that law into a density bound. Translation invariance and Tonelli
prove the correspondence for arbitrary probability laws.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution

namespace CircularLaw

theorem planar_disk_translate_integral (s : Set ℂ) (x : ℂ) (r : ℝ) :
    (∫⁻ y, s.indicator (fun _ => (1 : ℝ≥0∞)) (x + y)
      ∂volume.restrict (Metric.closedBall 0 r)) =
      ∫⁻ y, (Metric.closedBall x r).indicator (s.indicator (fun _ => 1)) y ∂volume := by
  rw [← lintegral_indicator measurableSet_closedBall]
  let f : ℂ → ℝ≥0∞ := (Metric.closedBall x r).indicator (s.indicator (fun _ => 1))
  calc
    _ = ∫⁻ y, f (x + y) ∂volume := by
      apply lintegral_congr
      intro y
      have hBall : y ∈ Metric.closedBall 0 r ↔ x + y ∈ Metric.closedBall x r := by
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, add_sub_cancel_left]
      dsimp only [f]
      by_cases hy : y ∈ Metric.closedBall 0 r
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hBall.mp hy)]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hBall.mpr h))]
    _ = _ := lintegral_add_left_eq_self f x

theorem probability_conv_restrict_disk_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {r : ℝ} {u : ℝ≥0∞} (hBall : ∀ z, μ (Metric.closedBall z r) ≤ u) :
    μ ∗ volume.restrict (Metric.closedBall 0 r) ≤ u • volume := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [← lintegral_indicator_one hs, Measure.lintegral_conv (measurable_one.indicator hs)]
  simp only [Pi.one_def]
  simp_rw [planar_disk_translate_integral]
  have hF : Measurable (fun p : ℂ × ℂ =>
      (Metric.closedBall p.1 r).indicator (s.indicator (fun _ => (1 : ℝ≥0∞))) p.2) := by
    have hExpr : (fun p : ℂ × ℂ =>
        (Metric.closedBall p.1 r).indicator (s.indicator (fun _ => (1 : ℝ≥0∞))) p.2) =
        fun p => if ‖p.2 - p.1‖ ≤ r then s.indicator (fun _ => 1) p.2 else 0 := by
      funext p
      by_cases h : ‖p.2 - p.1‖ ≤ r
      · rw [Set.indicator_of_mem (show p.2 ∈ Metric.closedBall p.1 r from h)]
        exact (if_pos h).symm
      · rw [Set.indicator_of_notMem (show p.2 ∉ Metric.closedBall p.1 r from h)]
        exact (if_neg h).symm
    rw [hExpr]
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      ((measurable_one.indicator hs).comp measurable_snd) measurable_const
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ y, s.indicator (fun _ => (1 : ℝ≥0∞)) y * u ∂volume := by
      apply lintegral_mono
      intro y
      dsimp only
      have hInner : (fun x => (Metric.closedBall x r).indicator
          (s.indicator (fun _ => (1 : ℝ≥0∞))) y) =
          (Metric.closedBall y r).indicator (fun _ => s.indicator (fun _ => 1) y) := by
        funext x
        have hBallSwap : y ∈ Metric.closedBall x r ↔ x ∈ Metric.closedBall y r := by
          simp only [Metric.mem_closedBall, dist_comm]
        by_cases hx : y ∈ Metric.closedBall x r
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hBallSwap.mp hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (fun h => hx (hBallSwap.mpr h))]
      rw [hInner, lintegral_indicator_const measurableSet_closedBall]
      exact mul_le_mul_right (hBall y) _
    _ = (u • volume) s := by
      rw [← Pi.one_def, lintegral_mul_const _ (measurable_one.indicator hs),
        lintegral_indicator_one hs, Measure.smul_apply, smul_eq_mul, mul_comm]

theorem probability_disk_smoothing_le_area (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {r u : ℝ}
    (hBall : ∀ z, μ (Metric.closedBall z r) ≤ ENNReal.ofReal u) :
    μ ∗ planarDiskLaw r ≤ ENNReal.ofReal (u / (r ^ 2 * Real.pi)) • volume := by
  rw [planarDiskLaw, Measure.conv_smul_right]
  have h : ENNReal.ofReal ((r ^ 2 * Real.pi)⁻¹) •
      (μ ∗ volume.restrict (Metric.closedBall 0 r)) ≤
      ENNReal.ofReal ((r ^ 2 * Real.pi)⁻¹) • (ENNReal.ofReal u • volume) := by
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (probability_conv_restrict_disk_le μ hBall s) _
  rw [smul_smul, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (r ^ 2 * Real.pi)⁻¹)] at h
  convert h using 1
  congr 2
  ring

end CircularLaw
