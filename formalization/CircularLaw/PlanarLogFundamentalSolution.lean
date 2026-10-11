import CircularLaw.PlanarGreenIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The logarithmic fundamental solution at zero

Dominated convergence passes from the smoothed logarithm to `log norm`.
Green's identity and the actual positive-kernel limit then give the
distributional identity, tested against every compactly supported C2
function, with its exact `2*pi` factor.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology Laplacian

namespace CircularLaw

theorem smoothed_planar_log_absolute_bound {ε : ℝ} (hε : ε ≠ 0)
    (hεSmall : ε ^ 2 ≤ 1) {z : ℂ} (hz : z ≠ 0) :
    |smoothedPlanarLog ε z| ≤ |Real.log ‖z‖| + (‖z‖ ^ 2 + 1) := by
  have hzPos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hDen := smoothed_planar_log_denominator_pos hε z
  have hLower : Real.log ‖z‖ ≤ smoothedPlanarLog ε z := by
    have h := Real.strictMonoOn_log.monotoneOn
      (show ‖z‖ ^ 2 ∈ Ioi (0 : ℝ) from sq_pos_of_pos hzPos) hDen
      (by nlinarith [sq_nonneg ε] : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2)
    rw [Real.log_pow] at h
    norm_num at h
    unfold smoothedPlanarLog
    nlinarith
  have hUpper : smoothedPlanarLog ε z ≤ ‖z‖ ^ 2 + 1 := by
    have h := Real.log_le_self hDen.le
    unfold smoothedPlanarLog
    nlinarith [sq_nonneg ‖z‖]
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (Real.log ‖z‖), sq_nonneg ‖z‖]
  · nlinarith [abs_nonneg (Real.log ‖z‖)]

theorem smoothed_planar_log_pointwise_limit {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c : ℝ => smoothedPlanarLog c⁻¹ z) atTop (𝓝 (Real.log ‖z‖)) := by
  have hε : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hDen : Tendsto (fun c : ℝ => ‖z‖ ^ 2 + c⁻¹ ^ 2) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa using tendsto_const_nhds.add (hε.pow 2)
  have hzPos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hLog := (Real.continuousAt_log (by positivity : ‖z‖ ^ 2 ≠ 0)).tendsto.comp hDen
  have h := hLog.const_mul (1 / 2)
  simpa only [smoothedPlanarLog, Real.log_pow, Nat.cast_ofNat,
    one_div, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul] using h

theorem smoothed_planar_log_compact_test_limit (φ : ℂ → ℝ) (hφ : Continuous φ)
    (hSupport : HasCompactSupport φ) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, smoothedPlanarLog c⁻¹ z * φ z)
      atTop (𝓝 (∫ z : ℂ, Real.log ‖z‖ * φ z)) := by
  let bound : ℂ → ℝ := fun z => |φ z| * |Real.log ‖z‖| +
    |φ z| * (‖z‖ ^ 2 + 1)
  have hAbsφ : Continuous (fun z => |φ z|) := hφ.norm
  have hAbsSupport : HasCompactSupport (fun z => |φ z|) := hSupport.norm
  have hLogInt : Integrable (fun z => |φ z| * |Real.log ‖z‖|) volume := by
    have h := (planar_log_kernel_locallyIntegrable 0).integrable_smul_left_of_hasCompactSupport
      hAbsφ hAbsSupport
    simpa only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_abs] using h.norm
  have hSmoothInt : Integrable (fun z : ℂ => |φ z| * (‖z‖ ^ 2 + 1)) volume :=
    (hAbsφ.mul (by fun_prop)).integrable_of_hasCompactSupport hAbsSupport.mul_right
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (c : ℝ) (z : ℂ) => smoothedPlanarLog c⁻¹ z * φ z)
    (f := fun z : ℂ => Real.log ‖z‖ * φ z) bound ?_ ?_ (hLogInt.add hSmoothInt) ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact ((smoothed_planar_log_contDiff (inv_ne_zero hc.ne')).continuous.mul hφ).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (1 : ℝ)] with c hc
    change 1 ≤ c at hc
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    have hcPos : 0 < c := by linarith
    have hεSmall : c⁻¹ ^ 2 ≤ 1 := by
      have hInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hcPos.le
      have hInvLe : c⁻¹ ≤ 1 := (inv_le_one₀ hcPos).mpr hc
      nlinarith
    rw [Real.norm_eq_abs, abs_mul]
    change |smoothedPlanarLog c⁻¹ z| * |φ z| ≤ bound z
    have h := mul_le_mul_of_nonneg_right
      (smoothed_planar_log_absolute_bound (inv_ne_zero hcPos.ne') hεSmall hz) (abs_nonneg (φ z))
    dsimp [bound]
    nlinarith
  · filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact (smoothed_planar_log_pointwise_limit hz).mul_const (φ z)

theorem planar_log_fundamental_solution_zero (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hSupport : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z‖ * (Δ φ) z) = (2 * Real.pi) * φ 0 := by
  have hLeft := smoothed_planar_log_compact_test_limit (Δ φ)
    (planar_laplacian_continuous φ hφ) (planar_laplacian_compact_support φ hSupport hφ)
  have hφInt : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hSupport
  have hRight := smoothed_planar_log_laplacian_test_limit φ hφInt hφ.continuous.continuousAt
  have hEq : (fun c : ℝ => ∫ z : ℂ, smoothedPlanarLog c⁻¹ z * (Δ φ) z) =ᶠ[atTop]
      (fun c : ℝ => ∫ z : ℂ, (Δ (smoothedPlanarLog c⁻¹)) z * φ z) := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact planar_green_identity φ (smoothedPlanarLog c⁻¹) hφ
      ((smoothed_planar_log_contDiff (inv_ne_zero hc.ne')).of_le (by simp)) hSupport
  exact tendsto_nhds_unique hLeft (hRight.congr' hEq.symm)

theorem planar_laplacian_translation (φ : ℂ → ℝ) (w z : ℂ) :
    (Δ (fun x => φ (x + w))) z = (Δ φ) (z + w) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_comp_add_right]

theorem planar_log_fundamental_solution (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hSupport : HasCompactSupport φ) (w : ℂ) :
    (∫ z : ℂ, Real.log ‖z - w‖ * (Δ φ) z) = (2 * Real.pi) * φ w := by
  have hShift : ContDiff ℝ 2 (fun z : ℂ => φ (z + w)) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have hShiftSupport : HasCompactSupport (fun z : ℂ => φ (z + w)) :=
    hSupport.comp_homeomorph (Homeomorph.addRight w)
  have h := planar_log_fundamental_solution_zero (fun z : ℂ => φ (z + w)) hShift hShiftSupport
  simp only [planar_laplacian_translation, zero_add] at h
  have hTranslation := integral_add_right_eq_self
    (fun z : ℂ => Real.log ‖z - w‖ * (Δ φ) z) w (μ := volume)
  simp only [add_sub_cancel_right] at hTranslation
  exact hTranslation.symm.trans h

theorem planar_log_laplacian_test_integrable (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hSupport : HasCompactSupport φ) (w : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z - w‖ * (Δ φ) z) volume := by
  simpa only [smul_eq_mul] using
    (planar_log_kernel_locallyIntegrable w).integrable_smul_right_of_hasCompactSupport
      (planar_laplacian_continuous φ hφ) (planar_laplacian_compact_support φ hSupport hφ)

end CircularLaw
