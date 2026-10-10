import CircularLaw.PeriodicCosine
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Gaussian cosine integrals in arbitrary planar directions

Rotation preserves planar volume. The integral in a single direction factors
into a real cosine integral and a transverse Gaussian integral. A change of
scale then applies the checked periodic-kernel estimate.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace CircularLaw

def planarCosineKernel (b a : ℝ) (v t : ℂ) : ℝ :=
  Real.exp (-b * ‖t‖ ^ 2) * Real.exp (-a * (1 - Real.cos ⟪v, t⟫))

def realCosineKernel (b a ρ x : ℝ) : ℝ :=
  Real.exp (-b * x ^ 2) * Real.exp (-a * (1 - Real.cos (ρ * x)))

theorem planarCosineKernel_integrable {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (v : ℂ) :
    Integrable (planarCosineKernel b a v) volume := by
  apply (planarGaussian_integrable hb).mono'
  · unfold planarCosineKernel
    fun_prop
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_pos (by unfold planarCosineKernel; positivity)]
    apply mul_le_of_le_one_right (Real.exp_pos _).le
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
      (sub_nonneg.mpr (Real.cos_le_one _)))

theorem planarCosineKernel_axis_factor (b a ρ : ℝ) (t : ℂ) :
    planarCosineKernel b a (ρ : ℂ) t =
      realCosineKernel b a ρ t.re * Real.exp (-b * t.im ^ 2) := by
  have hInner : ⟪(ρ : ℂ), t⟫ = ρ * t.re := by
    simp only [Complex.inner, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, mul_comm]
  rw [planarCosineKernel, hInner, Complex.sq_norm, Complex.normSq_apply,
    show -b * (t.re * t.re + t.im * t.im) = -b * t.re ^ 2 + -b * t.im ^ 2 by ring,
    Real.exp_add, realCosineKernel]
  ring

theorem planarCosineKernel_axis_integral (b a ρ : ℝ) :
    (∫ t : ℂ, planarCosineKernel b a (ρ : ℂ) t) =
      (∫ x : ℝ, realCosineKernel b a ρ x) * Real.sqrt (Real.pi / b) := by
  have h := Complex.volume_preserving_equiv_real_prod.symm.integral_comp'
    (planarCosineKernel b a (ρ : ℂ))
  rw [← h]
  simp only [Complex.measurableEquivRealProd_symm_apply, planarCosineKernel_axis_factor]
  change (∫ x : ℝ × ℝ, realCosineKernel b a ρ x.1 * Real.exp (-b * x.2 ^ 2)
    ∂volume.prod volume) = _
  rw [integral_prod_mul (realCosineKernel b a ρ) (fun y : ℝ => Real.exp (-b * y ^ 2)),
    integral_gaussian]

theorem planarCosineKernel_rotation (b a ρ : ℝ) (u : Circle) (t : ℂ) :
    planarCosineKernel b a (ρ • (u : ℂ)) (rotation u t) =
      planarCosineKernel b a (ρ : ℂ) t := by
  have hInner : ⟪(u : ℂ), rotation u t⟫ = t.re := by
    have h := (rotation u).inner_map_map (1 : ℂ) t
    simpa only [rotation_apply, mul_one, Complex.inner, map_one, mul_one] using h
  have hAxis : ⟪(ρ : ℂ), t⟫ = ρ * t.re := by
    simp only [Complex.inner, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, mul_comm]
  simp only [planarCosineKernel, (rotation u).norm_map, real_inner_smul_left, hInner, hAxis]

theorem planarCosineKernel_rotation_integral (b a ρ : ℝ) (u : Circle) :
    (∫ t : ℂ, planarCosineKernel b a (ρ • (u : ℂ)) t) =
      (∫ x : ℝ, realCosineKernel b a ρ x) * Real.sqrt (Real.pi / b) := by
  have h := (rotation u).measurePreserving.integral_comp
    (rotation u).toHomeomorph.measurableEmbedding (planarCosineKernel b a (ρ • (u : ℂ)))
  rw [← h]
  simp only [planarCosineKernel_rotation, planarCosineKernel_axis_integral]

theorem realCosineKernel_rescale {b a ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    realCosineKernel b a ρ x =
      gaussianCosineKernel (b / (ρ / (2 * Real.pi)) ^ 2) a ((ρ / (2 * Real.pi)) * x) := by
  have hScale : ρ / (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have hGauss : -(b / (ρ / (2 * Real.pi)) ^ 2) * ((ρ / (2 * Real.pi)) * x) ^ 2 =
      -b * x ^ 2 := by field_simp
  have hAngle : 2 * Real.pi * ((ρ / (2 * Real.pi)) * x) = ρ * x := by field_simp
  simp only [realCosineKernel, gaussianCosineKernel, periodicCosineKernel, hGauss, hAngle]

theorem realCosineKernel_integral_le {b a ρ : ℝ} (hb : 0 < b) (ha : 0 < a) (hρ : 0 < ρ) :
    (∫ x : ℝ, realCosineKernel b a ρ x) ≤
      (ρ / (2 * Real.pi))⁻¹ *
        ((1 + 2 * Real.sqrt (Real.pi / ((b / (ρ / (2 * Real.pi)) ^ 2) / 4))) *
          Real.sqrt (Real.pi / (8 * a))) := by
  simp_rw [realCosineKernel_rescale hρ]
  rw [Measure.integral_comp_mul_left, abs_of_pos (by positivity : 0 < (ρ / (2 * Real.pi))⁻¹),
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (gaussianCosineKernel_integral_le (by positivity : 0 < b / (ρ / (2 * Real.pi)) ^ 2) ha)
    (by positivity)

theorem planarCosineKernel_scaled_direction_integral_le {b a ρ : ℝ}
    (hb : 0 < b) (ha : 0 < a) (hρ : 0 < ρ) (u : Circle) :
    (∫ t : ℂ, planarCosineKernel b a (ρ • (u : ℂ)) t) ≤
      ((ρ / (2 * Real.pi))⁻¹ *
        ((1 + 2 * Real.sqrt (Real.pi / ((b / (ρ / (2 * Real.pi)) ^ 2) / 4))) *
          Real.sqrt (Real.pi / (8 * a)))) * Real.sqrt (Real.pi / b) := by
  rw [planarCosineKernel_rotation_integral]
  exact mul_le_mul_of_nonneg_right (realCosineKernel_integral_le hb ha hρ) (Real.sqrt_nonneg _)

def planarDirectionUnit (v : ℂ) (hv : v ≠ 0) : Circle :=
  ⟨‖v‖⁻¹ • v, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

theorem planarDirectionUnit_reconstruct (v : ℂ) (hv : v ≠ 0) :
    ‖v‖ • (planarDirectionUnit v hv : ℂ) = v := by
  change ‖v‖ • (‖v‖⁻¹ • v) = v
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

theorem planarCosineKernel_integral_le {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (v : ℂ) (hv : v ≠ 0) :
    (∫ t : ℂ, planarCosineKernel b a v t) ≤
      ((‖v‖ / (2 * Real.pi))⁻¹ *
        ((1 + 2 * Real.sqrt (Real.pi / ((b / (‖v‖ / (2 * Real.pi)) ^ 2) / 4))) *
          Real.sqrt (Real.pi / (8 * a)))) * Real.sqrt (Real.pi / b) := by
  have h := planarCosineKernel_scaled_direction_integral_le hb ha (norm_pos_iff.mpr hv)
    (planarDirectionUnit v hv)
  rw [planarDirectionUnit_reconstruct] at h
  exact h

theorem gaussian_period_scale_sqrt {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (Real.pi / ((b / c ^ 2) / 4)) = 2 * c * Real.sqrt (Real.pi / b) := by
  have hEq : Real.pi / ((b / c ^ 2) / 4) = (2 * c) ^ 2 * (Real.pi / b) := by
    field_simp
    ring
  rw [hEq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem planarCosineKernel_integral_le_clean {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (v : ℂ) (hv : v ≠ 0) :
    (∫ t : ℂ, planarCosineKernel b a v t) ≤
      (2 * Real.pi / ‖v‖ + 4 * Real.sqrt (Real.pi / b)) *
        Real.sqrt (Real.pi / (8 * a)) * Real.sqrt (Real.pi / b) := by
  have hc : 0 < ‖v‖ / (2 * Real.pi) := by positivity
  have h := planarCosineKernel_integral_le hb ha v hv
  rw [gaussian_period_scale_sqrt hb hc] at h
  have hEq : ((‖v‖ / (2 * Real.pi))⁻¹ *
      ((1 + 2 * (2 * (‖v‖ / (2 * Real.pi)) * Real.sqrt (Real.pi / b))) *
        Real.sqrt (Real.pi / (8 * a)))) * Real.sqrt (Real.pi / b) =
      (2 * Real.pi / ‖v‖ + 4 * Real.sqrt (Real.pi / b)) *
        Real.sqrt (Real.pi / (8 * a)) * Real.sqrt (Real.pi / b) := by
    field_simp
    ring
  rwa [hEq] at h

end CircularLaw
