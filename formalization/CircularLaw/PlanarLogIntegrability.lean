import CircularLaw.SpectralLogPotential
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Local integrability of the planar logarithmic kernel

Polar coordinates supply the area factor. The singularity at zero has
finite absolute integral on every bounded disk; translations and finite
atomic sums then give locally integrable actual ESD potentials.
-/

noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal

namespace CircularLaw

theorem radial_absolute_log_bound {r : ℝ} (hr : 0 < r) :
    r * |Real.log r| ≤ r ^ 2 + 1 := by
  have hInv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hAbs : |Real.log r| ≤ r + r⁻¹ := by
    rw [abs_le]
    constructor
    · linarith [Real.neg_inv_le_log hr.le]
    · linarith [Real.log_le_self hr.le]
  have hMul := mul_le_mul_of_nonneg_left hAbs hr.le
  calc
    r * |Real.log r| ≤ r * (r + r⁻¹) := hMul
    _ = r ^ 2 + 1 := by rw [mul_add, mul_inv_cancel₀ hr.ne']; ring

theorem planar_log_norm_integrableOn_closedBall {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.closedBall 0 R) volume := by
  have hs : MeasurableSet (Metric.closedBall (0 : ℂ) R) := measurableSet_closedBall
  let f : ℂ → ℝ≥0∞ := (Metric.closedBall (0 : ℂ) R).indicator
    (fun z => ENNReal.ofReal |Real.log ‖z‖|)
  let rect : Set (ℝ × ℝ) := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  have hRect : MeasurableSet rect := measurableSet_Ioc.prod measurableSet_Ioo
  have hRectFinite : volume rect < ∞ := by
    apply lt_of_le_of_lt (measure_mono (show rect ⊆ Icc 0 R ×ˢ Icc (-Real.pi) Real.pi from
      fun _ h => ⟨⟨h.1.1.le, h.1.2⟩, ⟨h.2.1.le, h.2.2.le⟩⟩))
    exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hBound : (∫⁻ z : ℂ, f z) ≤
      ENNReal.ofReal (R ^ 2 + 1) * volume rect := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
    calc
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) ≤
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
            rect.indicator (fun _ => ENNReal.ofReal (R ^ 2 + 1)) p := by
        apply setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        have hp0 : 0 < p.1 := hp.1
        by_cases hpR : p.1 ≤ R
        · have hMem : p ∈ rect := ⟨⟨hp0, hpR⟩, hp.2⟩
          rw [Set.indicator_of_mem hMem]
          simp only [f, Set.indicator_apply, Metric.mem_closedBall, dist_zero_right,
            Complex.norm_polarCoord_symm, abs_of_pos hp0, hpR, if_true, smul_eq_mul]
          rw [← ENNReal.ofReal_mul hp0.le]
          apply ENNReal.ofReal_le_ofReal
          exact (radial_absolute_log_bound hp0).trans (by nlinarith)
        · have hNotMem : p ∉ rect := fun h => hpR h.1.2
          rw [Set.indicator_of_notMem hNotMem]
          simp [f, Metric.mem_closedBall,
            abs_of_pos hp0, hpR]
      _ ≤ ∫⁻ p : ℝ × ℝ, rect.indicator (fun _ => ENNReal.ofReal (R ^ 2 + 1)) p :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal (R ^ 2 + 1) * volume rect := by
        rw [lintegral_indicator hRect, lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  constructor
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    rw [← lintegral_indicator hs]
    exact hBound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRectFinite)

theorem planar_log_kernel_integrableOn_closedBall (w : ℂ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z : ℂ => Real.log ‖z - w‖) (Metric.closedBall 0 R) volume := by
  have hS : 0 < R + ‖w‖ := add_pos_of_pos_of_nonneg hR (norm_nonneg w)
  have hInt := (planar_log_norm_integrableOn_closedBall hS).integrable_indicator
    measurableSet_closedBall
  have hTranslated := hInt.comp_sub_right w
  apply hTranslated.integrableOn.congr_fun _ measurableSet_closedBall
  intro z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hMem : z - w ∈ Metric.closedBall (0 : ℂ) (R + ‖w‖) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le z w).trans (by linarith)
  exact Set.indicator_of_mem hMem _

theorem planar_log_kernel_locallyIntegrable (w : ℂ) :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z - w‖) volume := by
  intro x
  refine ⟨Metric.closedBall (0 : ℂ) (‖x‖ + 1), ?_,
    planar_log_kernel_integrableOn_closedBall w (by positivity)⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

theorem spectral_log_potential_locallyIntegrable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : LocallyIntegrable (spectralLogPotential A) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  have hSum (s : Multiset ℂ) :
      IntegrableOn (fun z : ℂ => (s.map (fun w => Real.log ‖z - w‖)).sum) k volume := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons w s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact ((planar_log_kernel_locallyIntegrable w).integrableOn_isCompact hk).add ih
  have hDiv : IntegrableOn
      (fun z : ℂ => (A.charpoly.roots.map (fun w => Real.log ‖z - w‖)).sum / n) k volume :=
    (hSum A.charpoly.roots).div_const (n : ℝ)
  exact hDiv.congr_fun (fun z _ => (empiricalSpectralMeasure_integral A
    (fun w => Real.log ‖z - w‖)).symm) hk.measurableSet

theorem normalized_log_determinant_locallyIntegrable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : LocallyIntegrable (normalizedLogDeterminant A) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  exact ((spectral_log_potential_locallyIntegrable A).integrableOn_isCompact hk).congr_fun_ae
    (ae_restrict_of_ae (spectral_log_potential_eq_log_determinant_ae A))

end CircularLaw
