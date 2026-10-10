import CircularLaw.PlanarLogApproximateIdentity
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of the smoothed planar logarithm

All derivatives below are the actual real Fréchet derivatives on the
complex plane. The Laplacian is mathlib's trace of the second derivative.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology RealInnerProductSpace Laplacian

namespace CircularLaw

def smoothedPlanarLog (ε : ℝ) (z : ℂ) : ℝ :=
  (1 / 2) * Real.log (‖z‖ ^ 2 + ε ^ 2)

def smoothedPlanarLogComponent (ε : ℝ) (v z : ℂ) : ℝ :=
  inner ℝ v z / (‖z‖ ^ 2 + ε ^ 2)

theorem smoothed_planar_log_denominator_pos {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    0 < ‖z‖ ^ 2 + ε ^ 2 := by
  nlinarith [sq_pos_of_ne_zero hε, sq_nonneg ‖z‖]

theorem smoothed_planar_log_contDiff {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ⊤ (smoothedPlanarLog ε) := by
  have hLog : ContDiff ℝ ⊤ (fun z : ℂ => Real.log (‖z‖ ^ 2 + ε ^ 2)) :=
    ((contDiff_norm_sq ℝ).add contDiff_const).log
      (fun z => (smoothed_planar_log_denominator_pos hε z).ne')
  exact contDiff_const.mul hLog

theorem smoothed_planar_log_hasFDerivAt {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    HasFDerivAt (smoothedPlanarLog ε)
      ((‖z‖ ^ 2 + ε ^ 2)⁻¹ • innerSL ℝ z) z := by
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).log
    (smoothed_planar_log_denominator_pos hε z).ne').const_mul (1 / 2)
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

theorem smoothed_planar_log_fderiv {ε : ℝ} (hε : ε ≠ 0) (z v : ℂ) :
    fderiv ℝ (smoothedPlanarLog ε) z v = smoothedPlanarLogComponent ε v z := by
  rw [(smoothed_planar_log_hasFDerivAt hε z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
    smoothedPlanarLogComponent, div_eq_mul_inv]
  rw [real_inner_comm]
  ring

theorem smoothed_planar_log_component_hasFDerivAt {ε : ℝ} (hε : ε ≠ 0) (z v : ℂ) :
    HasFDerivAt (smoothedPlanarLogComponent ε v)
      ((‖z‖ ^ 2 + ε ^ 2)⁻¹ • innerSL ℝ v -
        (2 * inner ℝ v z / (‖z‖ ^ 2 + ε ^ 2) ^ 2) • innerSL ℝ z) z := by
  have hInv := (hasDerivAt_inv (smoothed_planar_log_denominator_pos hε z).ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2))
  have h : HasFDerivAt (smoothedPlanarLogComponent ε v)
      (inner ℝ v z • (-((‖z‖ ^ 2 + ε ^ 2) ^ 2)⁻¹ • 2 • innerSL ℝ z) +
        (‖z‖ ^ 2 + ε ^ 2)⁻¹ • innerSL ℝ v) z := by
    simpa only [smoothedPlanarLogComponent, div_eq_mul_inv, Function.comp_apply,
      innerSL_apply_apply] using (innerSL ℝ v).hasFDerivAt.mul hInv
  convert h using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    smul_eq_mul, innerSL_apply_apply]
  field_simp
  ring

theorem smoothed_planar_log_component_second {ε : ℝ} (hε : ε ≠ 0) (z v : ℂ) :
    fderiv ℝ (smoothedPlanarLogComponent ε v) z v =
      ‖v‖ ^ 2 / (‖z‖ ^ 2 + ε ^ 2) -
        2 * (inner ℝ v z) ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  rw [(smoothed_planar_log_component_hasFDerivAt hε z v).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [real_inner_comm z v]
  ring

theorem planar_laplacian_eq_coordinate_second_derivatives (f : ℂ → ℝ)
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    (Δ f) z = fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply (hd z) (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply (hd z) (differentiableAt_const Complex.I)]
  simp

theorem smoothed_planar_log_laplacian {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (Δ (smoothedPlanarLog ε)) z = 2 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  rw [planar_laplacian_eq_coordinate_second_derivatives _
    ((smoothed_planar_log_contDiff hε).of_le (by simp))]
  have hOne : (fun w => fderiv ℝ (smoothedPlanarLog ε) w 1) =
      smoothedPlanarLogComponent ε 1 := by
    funext w
    exact smoothed_planar_log_fderiv hε w 1
  have hI : (fun w => fderiv ℝ (smoothedPlanarLog ε) w Complex.I) =
      smoothedPlanarLogComponent ε Complex.I := by
    funext w
    exact smoothed_planar_log_fderiv hε w Complex.I
  rw [hOne, hI, smoothed_planar_log_component_second hε,
    smoothed_planar_log_component_second hε]
  simp [Complex.inner]
  have hSq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hDen := (smoothed_planar_log_denominator_pos hε z).ne'
  field_simp
  nlinarith [hSq]

theorem smoothed_planar_log_laplacian_scaled_kernel {c : ℝ} (hc : 0 < c) (z : ℂ) :
    (Δ (smoothedPlanarLog c⁻¹)) z =
      (2 * Real.pi) * (c ^ 2 * planarLogApproximationKernel (c • z)) := by
  rw [smoothed_planar_log_laplacian (inv_ne_zero hc.ne')]
  unfold planarLogApproximationKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hDen : ‖z‖ ^ 2 + c⁻¹ ^ 2 ≠ 0 :=
    (smoothed_planar_log_denominator_pos (inv_ne_zero hc.ne') z).ne'
  have hDen' : 1 + (c * ‖z‖) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem smoothed_planar_log_laplacian_test_limit (φ : ℂ → ℝ)
    (hφ : Integrable φ volume) (hφ0 : ContinuousAt φ 0) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, (Δ (smoothedPlanarLog c⁻¹)) z * φ z)
      atTop (𝓝 ((2 * Real.pi) * φ 0)) := by
  have hLimit := (planar_log_approximation_kernel_test_limit φ hφ hφ0).const_mul (2 * Real.pi)
  apply hLimit.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  simp_rw [smoothed_planar_log_laplacian_scaled_kernel hc, mul_assoc, integral_const_mul]

end CircularLaw
