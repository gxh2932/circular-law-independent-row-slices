import CircularLaw.DiskSmoothing
import CircularLaw.IndependentSecondMoment

/-!
# Comparing a sum with its smoothed law

A rectangle of small-ball events maps into the larger small ball of
the convolution. Summandwise smoothing agrees with smoothing the actual
sum law, by characteristic functions and their uniqueness theorem.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution BigOperators

namespace CircularLaw

theorem convolution_closedBall_lower (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (z : ℂ) (t R : ℝ) :
    μ (Metric.closedBall z t) * ν (Metric.closedBall 0 R) ≤
      (μ ∗ ν) (Metric.closedBall z (t + R)) := by
  have hSub : Metric.closedBall z t ×ˢ Metric.closedBall (0 : ℂ) R ⊆
      (fun p : ℂ × ℂ => p.1 + p.2) ⁻¹' Metric.closedBall z (t + R) := by
    intro p hp
    change ‖p.1 + p.2 - z‖ ≤ t + R
    have h1 : ‖p.1 - z‖ ≤ t := hp.1
    have h2 : ‖p.2‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hp.2
    have heq : p.1 + p.2 - z = (p.1 - z) + p.2 := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have h := measure_mono (μ := μ.prod ν) hSub
  rw [Measure.prod_prod] at h
  simpa only [Measure.conv, Measure.map_apply measurable_add measurableSet_closedBall] using h

theorem productSumLaw_conv {ι : Type*} [Fintype ι]
    (μ ν : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    productSumLaw (fun i => μ i ∗ ν i) = productSumLaw μ ∗ productSumLaw ν := by
  apply Measure.ext_of_charFun
  funext t
  simp only [charFun_productSumLaw, charFun_conv, Finset.prod_mul_distrib]

theorem planarDisk_smoothed_sum_small_ball {m : ℕ} (μ : Fin m → Measure ℂ)
    [∀ i, IsProbabilityMeasure (μ i)] (hm : 1 ≤ m)
    {r t u : ℝ} (hr : 0 < r) (hu : 0 < u) (ht : 0 ≤ t)
    (hBall : ∀ i z, μ i (Metric.closedBall z r) ≤ ENNReal.ofReal u) (z : ℂ) :
    productSumLaw μ (Metric.closedBall z t) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) *
        ((200 * (u / (r ^ 2 * Real.pi)) / (m : ℝ)) *
          ((t + 2 * Real.sqrt (m : ℝ) * r) ^ 2 * Real.pi))) := by
  haveI := planarDiskLaw_probability hr
  have hDensity : ∀ i, μ i ∗ planarDiskLaw r ≤
      ENNReal.ofReal (u / (r ^ 2 * Real.pi)) • volume :=
    fun i => probability_disk_smoothing_le_area _ (hBall i)
  have hUpper := probability_sum_closedBall_le hm (fun i => μ i ∗ planarDiskLaw r)
    (by positivity : 0 < u / (r ^ 2 * Real.pi)) hDensity
    (by positivity : 0 ≤ t + 2 * Real.sqrt (m : ℝ) * r) z
  rw [productSumLaw_conv] at hUpper
  have hLower := convolution_closedBall_lower (productSumLaw μ)
    (productSumLaw (fun _ : Fin m => planarDiskLaw r)) z t (2 * Real.sqrt (m : ℝ) * r)
  have h := (mul_le_mul_right (planarDisk_sum_small_ball_lower hm hr) _).trans
    (hLower.trans hUpper)
  have hInv : ENNReal.ofReal (4 / 3 : ℝ) * ENNReal.ofReal (3 / 4 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    norm_num
  have hMul := mul_le_mul_right h (ENNReal.ofReal (4 / 3 : ℝ))
  rw [← mul_assoc, mul_right_comm _ _ (ENNReal.ofReal (3 / 4 : ℝ)), hInv, one_mul,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3)] at hMul
  exact hMul

end CircularLaw
