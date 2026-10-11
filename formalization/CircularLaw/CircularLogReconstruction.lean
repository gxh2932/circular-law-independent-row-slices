import CircularLaw.CircularLogPotential
import CircularLaw.SpectralLogReconstruction

/-!
# Reconstruction of the actual circular measure from its potential

Fubini applies to the logarithmic kernel against a compactly supported
continuous test. Uniform section bounds on the unit disk discharge the
joint integrability hypothesis. The checked planar fundamental solution
therefore reconstructs the actual circular measure with factor `2*pi`.
-/

noncomputable section
open Classical MeasureTheory Set
open scoped Laplacian Topology

namespace CircularLaw

theorem planar_log_kernel_absolute_integral_disk_bound (w : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ z : ℂ in Metric.closedBall 0 R, |Real.log ‖z - w‖|) ≤
      32 * Real.pi + (2 * R ^ 2 + 2 * ‖w‖ ^ 2 + 1) *
        volume.real (Metric.closedBall (0 : ℂ) R) := by
  have hLog := (planar_log_kernel_integrableOn_closedBall w hR).norm
  have hSq := planar_squared_log_kernel_integrableOn_closedBall w R
  have hConst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (Metric.closedBall 0 R) volume :=
    integrableOn_const ((isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne)
  have hBound : (∫ z : ℂ in Metric.closedBall 0 R, |Real.log ‖z - w‖|) ≤
      ∫ z : ℂ in Metric.closedBall 0 R, (Real.log ‖z - w‖) ^ 2 + 1 := by
    apply setIntegral_mono_on hLog (hSq.add hConst) measurableSet_closedBall
    intro z _
    have h := sq_nonneg (|Real.log ‖z - w‖| - 1)
    change |Real.log ‖z - w‖| ≤ (Real.log ‖z - w‖) ^ 2 + 1
    nlinarith [sq_abs (Real.log ‖z - w‖), sq_nonneg (Real.log ‖z - w‖)]
  rw [integral_add hSq hConst, setIntegral_const] at hBound
  simp only [smul_eq_mul, mul_one] at hBound
  have hSqBound := log_kernel_square_integral_disk_bound w R
  linarith

theorem compact_log_kernel_absolute_integral_bound (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hSupport : HasCompactSupport ψ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (hBound : ∀ z, |ψ z| ≤ C)
    (hDisk : Function.support ψ ⊆ Metric.closedBall 0 R) (w : ℂ) :
    (∫ z : ℂ, ‖Real.log ‖z - w‖ * ψ z‖) ≤
      C * (32 * Real.pi + (2 * R ^ 2 + 2 * ‖w‖ ^ 2 + 1) *
        volume.real (Metric.closedBall (0 : ℂ) R)) := by
  have hTestInt : Integrable (fun z : ℂ => Real.log ‖z - w‖ * ψ z) volume := by
    simpa only [smul_eq_mul] using
      (planar_log_kernel_locallyIntegrable w).integrable_smul_right_of_hasCompactSupport hψ hSupport
  have hLog := (planar_log_kernel_integrableOn_closedBall w hR).norm.const_mul C
  have hRestriction : (∫ z : ℂ in Metric.closedBall 0 R, ‖Real.log ‖z - w‖ * ψ z‖) =
      ∫ z : ℂ, ‖Real.log ‖z - w‖ * ψ z‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hψz : ψ z = 0 := by
      apply Function.notMem_support.mp
      exact fun h => hz (hDisk h)
    rw [hψz, mul_zero, norm_zero]
  rw [← hRestriction]
  calc
    _ ≤ ∫ z : ℂ in Metric.closedBall 0 R, C * |Real.log ‖z - w‖| := by
      apply setIntegral_mono_on hTestInt.norm.integrableOn hLog measurableSet_closedBall
      intro z _
      simp only [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hBound z) (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = C * ∫ z : ℂ in Metric.closedBall 0 R, |Real.log ‖z - w‖| := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (planar_log_kernel_absolute_integral_disk_bound w hR) hC

theorem circular_log_kernel_compact_test_joint_integrable (ψ : ℂ → ℝ)
    (hψ : Continuous ψ) (hSupport : HasCompactSupport ψ) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖ * ψ p.1)
      (volume.prod circularMeasure) := by
  let F : ℂ × ℂ → ℝ := fun p => Real.log ‖p.1 - p.2‖ * ψ p.1
  have hMeas : Measurable F :=
    (Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).mul
      (hψ.measurable.comp measurable_fst)
  obtain ⟨C, hC⟩ := hSupport.exists_bound_of_continuous hψ
  obtain ⟨R, hR⟩ := hSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let C' : ℝ := max C 0
  let R' : ℝ := max R 1
  have hRPos : 0 < R' := zero_lt_one.trans_le (le_max_right _ _)
  have hBound : ∀ z, |ψ z| ≤ C' := fun z => (hC z).trans (le_max_left _ _)
  have hDisk : Function.support ψ ⊆ Metric.closedBall 0 R' := by
    intro z hz
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR (subset_tsupport ψ hz))
  let K : ℝ := C' * (32 * Real.pi + (2 * R' ^ 2 + 3) *
    volume.real (Metric.closedBall (0 : ℂ) R'))
  apply (integrable_prod_iff' hMeas.aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro w
    simpa only [F, smul_eq_mul] using
      (planar_log_kernel_locallyIntegrable w).integrable_smul_right_of_hasCompactSupport hψ hSupport
  · apply (integrable_const K).mono'
      hMeas.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [circular_measure_ae_unit_disk] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have hwNorm : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hwSq : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    have h := compact_log_kernel_absolute_integral_bound ψ hψ hSupport C' R'
      (le_max_right _ _) hRPos hBound hDisk w
    have hArea : 0 ≤ volume.real (Metric.closedBall (0 : ℂ) R') := measureReal_nonneg
    dsimp only [F, K]
    exact h.trans (mul_le_mul_of_nonneg_left (by nlinarith) (le_max_right _ _))

theorem circular_log_laplacian_test_integrable (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hSupport : HasCompactSupport φ) :
    Integrable (fun z : ℂ => circularLogPotential z * (Δ φ) z) volume := by
  simpa only [smul_eq_mul] using
    circular_log_potential_locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (planar_laplacian_continuous φ hφ) (planar_laplacian_compact_support φ hSupport hφ)

theorem circular_log_reconstructs_test_integral (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, circularLogPotential z * (Δ φ) z) =
      (2 * Real.pi) * ∫ w : ℂ, φ w ∂circularMeasure := by
  have hJoint := circular_log_kernel_compact_test_joint_integrable (Δ φ)
    (planar_laplacian_continuous φ hφ) (planar_laplacian_compact_support φ hSupport hφ)
  calc
    _ = ∫ z : ℂ, ∫ w : ℂ, Real.log ‖z - w‖ * (Δ φ) z ∂circularMeasure := by
      simp only [circularLogPotential, integral_mul_const]
    _ = ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ * (Δ φ) p.1 ∂volume.prod circularMeasure :=
      (integral_prod _ hJoint).symm
    _ = ∫ w : ℂ, (∫ z : ℂ, Real.log ‖z - w‖ * (Δ φ) z) ∂circularMeasure :=
      integral_prod_symm _ hJoint
    _ = ∫ w : ℂ, (2 * Real.pi) * φ w ∂circularMeasure := by
      simp only [planar_log_fundamental_solution φ hφ hSupport]
    _ = _ := integral_const_mul _ _

theorem circular_paper_potential_reconstructs_test_integral (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, circularPaperPotential z * (Δ φ) z) =
      -(2 * Real.pi) * ∫ w : ℂ, φ w ∂circularMeasure := by
  simp only [circularPaperPotential, neg_mul, integral_neg,
    circular_log_reconstructs_test_integral φ hφ hSupport]

theorem log_determinant_circular_test_difference {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, (Δ φ) z * (normalizedLogDeterminant A z - circularLogPotential z)) =
      (2 * Real.pi) * ((∫ w : ℂ, φ w ∂empiricalSpectralMeasure A) -
        ∫ w : ℂ, φ w ∂circularMeasure) := by
  have hDetInt : Integrable (fun z : ℂ => normalizedLogDeterminant A z * (Δ φ) z) volume := by
    simpa only [smul_eq_mul] using
      (normalized_log_determinant_locallyIntegrable A).integrable_smul_right_of_hasCompactSupport
        (planar_laplacian_continuous φ hφ) (planar_laplacian_compact_support φ hSupport hφ)
  simp_rw [mul_sub, mul_comm ((Δ φ) _)]
  rw [integral_sub hDetInt (circular_log_laplacian_test_integrable φ hφ hSupport),
    log_determinant_reconstructs_test_integral A φ hφ hSupport,
    circular_log_reconstructs_test_integral φ hφ hSupport]

end CircularLaw
