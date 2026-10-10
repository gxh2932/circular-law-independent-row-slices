import CircularLaw.PlanarLogIntegrability
import CircularLaw.EigenvalueFirstMoment

/-!
# Square integrability of planar logarithmic potentials

The radial area factor controls the squared logarithmic singularity.
The statements use actual finite ESDs, including repeated eigenvalues.
-/

noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal

namespace CircularLaw

theorem planar_radial_absolute_lintegral_bound (g : ℝ → ℝ) (R C : ℝ)
    (hBound : ∀ r : ℝ, 0 < r → r ≤ R → r * |g r| ≤ C) :
    (∫⁻ z : ℂ in Metric.closedBall 0 R, ENNReal.ofReal |g ‖z‖|) ≤
      ENNReal.ofReal C * volume (Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) := by
  let rect : Set (ℝ × ℝ) := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  have hRect : MeasurableSet rect := measurableSet_Ioc.prod measurableSet_Ioo
  let f : ℂ → ℝ≥0∞ := (Metric.closedBall (0 : ℂ) R).indicator
    (fun z => ENNReal.ofReal |g ‖z‖|)
  rw [← lintegral_indicator measurableSet_closedBall]
  change (∫⁻ z : ℂ, f z) ≤ _
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  calc
    (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) ≤
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          rect.indicator (fun _ => ENNReal.ofReal C) p := by
      apply setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      by_cases hpR : p.1 ≤ R
      · rw [Set.indicator_of_mem (show p ∈ rect from ⟨⟨hp0, hpR⟩, hp.2⟩)]
        simp only [f, Set.indicator_apply, Metric.mem_closedBall, dist_zero_right,
          Complex.norm_polarCoord_symm, abs_of_pos hp0, hpR, if_true, smul_eq_mul]
        rw [← ENNReal.ofReal_mul hp0.le]
        exact ENNReal.ofReal_le_ofReal (hBound p.1 hp0 hpR)
      · rw [Set.indicator_of_notMem (show p ∉ rect from fun h => hpR h.1.2)]
        simp [f, Metric.mem_closedBall, abs_of_pos hp0, hpR]
    _ ≤ ∫⁻ p : ℝ × ℝ, rect.indicator (fun _ => ENNReal.ofReal C) p :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal C * volume rect := by
      rw [lintegral_indicator hRect, lintegral_const]
      simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter]

theorem planar_radial_integrableOn_closedBall_of_bound (g : ℝ → ℝ)
    (hg : Measurable g) (R C : ℝ)
    (hBound : ∀ r : ℝ, 0 < r → r ≤ R → r * |g r| ≤ C) :
    IntegrableOn (fun z : ℂ => g ‖z‖) (Metric.closedBall 0 R) volume := by
  have hFinite : volume (Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) < ∞ := by
    apply lt_of_le_of_lt (measure_mono (show Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi ⊆
      Icc 0 R ×ˢ Icc (-Real.pi) Real.pi from
      fun _ h => ⟨⟨h.1.1.le, h.1.2⟩, ⟨h.2.1.le, h.2.2.le⟩⟩))
    exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  constructor
  · exact (hg.comp measurable_norm).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact (planar_radial_absolute_lintegral_bound g R C hBound).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFinite)

theorem radial_squared_log_bound {r : ℝ} (hr : 0 < r) :
    r * (Real.log r) ^ 2 ≤ 8 * (r ^ 2 + 1) := by
  have h := radial_absolute_log_bound (Real.sqrt_pos.mpr hr)
  have hSq := pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg r) (abs_nonneg (Real.log (Real.sqrt r)))) h 2
  rw [mul_pow, Real.sq_sqrt hr.le, sq_abs, Real.log_sqrt hr.le, div_pow] at hSq
  norm_num at hSq
  nlinarith [sq_nonneg (r - 1)]

theorem planar_squared_log_norm_integrableOn_closedBall (R : ℝ) :
    IntegrableOn (fun z : ℂ => (Real.log ‖z‖) ^ 2) (Metric.closedBall 0 R) volume := by
  apply planar_radial_integrableOn_closedBall_of_bound (fun r => (Real.log r) ^ 2)
    (Real.measurable_log.pow_const 2) R (8 * (R ^ 2 + 1))
  intro r hr hrR
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (radial_squared_log_bound hr).trans (by nlinarith)

theorem planar_squared_log_kernel_integrableOn_closedBall (w : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => (Real.log ‖z - w‖) ^ 2) (Metric.closedBall 0 R) volume := by
  have hInt := (planar_squared_log_norm_integrableOn_closedBall (R + ‖w‖)).integrable_indicator
    measurableSet_closedBall
  have hTranslated := hInt.comp_sub_right w
  apply hTranslated.integrableOn.congr_fun _ measurableSet_closedBall
  intro z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hMem : z - w ∈ Metric.closedBall (0 : ℂ) (R + ‖w‖) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le z w).trans (by linarith)
  exact Set.indicator_of_mem hMem _

theorem planar_squared_log_kernel_locallyIntegrable (w : ℂ) :
    LocallyIntegrable (fun z : ℂ => (Real.log ‖z - w‖) ^ 2) volume := by
  intro x
  refine ⟨Metric.closedBall (0 : ℂ) (‖x‖ + 1), ?_,
    planar_squared_log_kernel_integrableOn_closedBall w (‖x‖ + 1)⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

theorem spectral_log_potential_square_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (spectralLogPotential A z) ^ 2 ≤
      (A.charpoly.roots.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRoots : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots]
    simp
  have h := multiset_sum_sq_le_card_mul_sum_sq
    (A.charpoly.roots.map (fun w => Real.log ‖z - w‖))
  simp only [Multiset.card_map, hRoots, Multiset.map_map] at h
  rw [spectralLogPotential, empiricalSpectralMeasure_integral, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  calc
    _ ≤ (n : ℝ) * (A.charpoly.roots.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum := h
    _ = _ := by field_simp

theorem spectral_log_potential_squared_locallyIntegrable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    LocallyIntegrable (fun z => (spectralLogPotential A z) ^ 2) volume := by
  by_cases hn : n = 0
  · subst n
    simp only [spectralLogPotential, empiricalSpectralMeasure_integral, Nat.cast_zero, div_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact (integrable_zero ℂ ℝ volume).locallyIntegrable
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  rw [locallyIntegrable_iff]
  intro k hk
  have hSum (s : Multiset ℂ) :
      IntegrableOn (fun z : ℂ => (s.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum) k volume := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons w s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact ((planar_squared_log_kernel_locallyIntegrable w).integrableOn_isCompact hk).add ih
  have hMajor : IntegrableOn
      (fun z : ℂ => (A.charpoly.roots.map (fun w => (Real.log ‖z - w‖) ^ 2)).sum / n) k volume :=
    (hSum A.charpoly.roots).div_const (n : ℝ)
  have hMeas : Measurable (spectralLogPotential A) := by
    have hEq : spectralLogPotential A =
        fun z => (A.charpoly.roots.map (fun w => Real.log ‖z - w‖)).sum / n := by
      funext z
      exact empiricalSpectralMeasure_integral A _
    rw [hEq]
    induction A.charpoly.roots using Multiset.induction_on with
    | empty => simp
    | @cons w s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, add_div]
      exact ((Real.measurable_log.comp (measurable_id.sub_const w).norm).div_const _).add ih
  apply hMajor.mono' (hMeas.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact spectral_log_potential_square_bound hnPos A z)

end CircularLaw
