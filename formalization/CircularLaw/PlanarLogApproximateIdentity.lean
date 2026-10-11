import CircularLaw.PlanarLogIntegrability
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The positive planar kernel of the smoothed logarithm

The kernel `1 / (pi * (1 + norm(z)^2)^2)` has mass one with the actual
complex-plane area measure. Its dilations approximate evaluation at zero.
This is the positive-kernel half of the logarithmic fundamental-solution
argument; the differential and integration-by-parts identities are separate.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology

namespace CircularLaw

def planarLogApproximationKernel (z : ℂ) : ℝ :=
  (1 / Real.pi) * (1 + ‖z‖ ^ 2)⁻¹ ^ 2

theorem planar_log_approximation_kernel_nonneg (z : ℂ) :
    0 ≤ planarLogApproximationKernel z := by
  unfold planarLogApproximationKernel
  positivity

theorem radial_log_kernel_primitive_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s : ℝ => (-1 / 2) * (1 + s ^ 2)⁻¹)
      (r / (1 + r ^ 2) ^ 2) r := by
  have h := ((((hasDerivAt_id r).pow 2).const_add 1).inv
    (by positivity : 1 + r ^ 2 ≠ 0)).const_mul (-1 / 2)
  simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one, mul_one, Nat.cast_ofNat] at h
  convert h using 1
  field_simp

theorem radial_log_kernel_primitive_tendsto_zero :
    Tendsto (fun r : ℝ => (-1 / 2) * (1 + r ^ 2)⁻¹) atTop (𝓝 0) := by
  have hSq : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hDen : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 hSq
  simpa using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hDen)

theorem radial_log_kernel_integrable :
    IntegrableOn (fun r : ℝ => r / (1 + r ^ 2) ^ 2) (Ioi 0) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun r _ => radial_log_kernel_primitive_hasDerivAt r)
    (fun r hr => div_nonneg hr.le (sq_nonneg _)) radial_log_kernel_primitive_tendsto_zero

theorem radial_log_kernel_integral :
    (∫ r : ℝ in Ioi 0, r / (1 + r ^ 2) ^ 2) = 1 / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r _ => radial_log_kernel_primitive_hasDerivAt r)
    (fun r hr => div_nonneg hr.le (sq_nonneg _)) radial_log_kernel_primitive_tendsto_zero
  norm_num at h ⊢
  exact h

theorem planar_log_approximation_kernel_mass :
    (∫ z : ℂ, planarLogApproximationKernel z) = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hFun : (fun p : ℝ × ℝ => p.1 •
      planarLogApproximationKernel (Complex.polarCoord.symm p)) =
      (fun p : ℝ × ℝ => (p.1 / (1 + p.1 ^ 2) ^ 2) * (1 / Real.pi)) := by
    funext p
    simp only [planarLogApproximationKernel, Complex.norm_polarCoord_symm,
      sq_abs, smul_eq_mul]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [hFun]
  change (∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    (p.1 / (1 + p.1 ^ 2) ^ 2) * (1 / Real.pi) ∂(volume.prod volume)) = 1
  rw [setIntegral_prod_mul (fun r : ℝ => r / (1 + r ^ 2) ^ 2)
    (fun _ : ℝ => 1 / Real.pi), radial_log_kernel_integral, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
  simp only [smul_eq_mul]
  field_simp
  norm_num

theorem planar_log_approximation_kernel_integrable :
    Integrable planarLogApproximationKernel volume :=
  integrable_of_integral_eq_one planar_log_approximation_kernel_mass

theorem planar_log_approximation_kernel_decay :
    Tendsto (fun z : ℂ => ‖z‖ ^ Module.finrank ℝ ℂ * planarLogApproximationKernel z)
      (Bornology.cobounded ℂ) (𝓝 0) := by
  have hSq : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Bornology.cobounded ℂ) atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cobounded_atTop
  have hDen : Tendsto (fun z : ℂ => 1 + ‖z‖ ^ 2) (Bornology.cobounded ℂ) atTop :=
    tendsto_atTop_add_const_left _ 1 hSq
  have hUpper : Tendsto (fun z : ℂ => (1 / Real.pi) * (1 + ‖z‖ ^ 2)⁻¹)
      (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hDen)
  apply squeeze_zero (fun _ => by unfold planarLogApproximationKernel; positivity) _ hUpper
  intro z
  rw [Complex.finrank_real_complex]
  unfold planarLogApproximationKernel
  have hDenPos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hBound : ‖z‖ ^ 2 * ((1 + ‖z‖ ^ 2)⁻¹ ^ 2) ≤ (1 + ‖z‖ ^ 2)⁻¹ := by
    field_simp
    nlinarith
  have hMul := mul_le_mul_of_nonneg_left hBound (by positivity : 0 ≤ 1 / Real.pi)
  nlinarith

theorem planar_log_approximation_kernel_test_limit (φ : ℂ → ℝ)
    (hφ : Integrable φ volume) (hφ0 : ContinuousAt φ 0) :
    Tendsto (fun c : ℝ => ∫ z : ℂ,
      (c ^ 2 * planarLogApproximationKernel (c • z)) * φ z)
      atTop (𝓝 (φ 0)) := by
  simpa only [Complex.finrank_real_complex, smul_eq_mul] using
    tendsto_integral_comp_smul_smul_of_integrable
      planar_log_approximation_kernel_nonneg planar_log_approximation_kernel_mass
      planar_log_approximation_kernel_decay hφ hφ0

end CircularLaw
