import CircularLaw.FourierLevels
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Pointwise and L2 Fourier transforms

Mathlib's Plancherel theorem is stated for `Lp`. This file identifies that
transform almost everywhere with the classical integral when the input
is both integrable and square integrable, using equality against smooth
compactly supported test functions.
-/

noncomputable section
open MeasureTheory Real FourierTransform
open scoped SchwartzMap FourierTransform ENNReal RealInnerProductSpace

namespace CircularLaw

theorem lp_integral_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (v : Lp ℂ 2 μ) : (∫ x, ‖v x‖ ^ 2 ∂μ) = ‖v‖ ^ 2 := by
  calc
    _ = ∫ x, (inner ℂ (v x) (v x)).re ∂μ := by
      congr 1
      funext x
      exact norm_sq_eq_re_inner (𝕜 := ℂ) (v x)
    _ = (∫ x, inner ℂ (v x) (v x) ∂μ).re := integral_re (L2.integrable_inner (𝕜 := ℂ) v v)
    _ = (inner ℂ v v).re := congrArg Complex.re (L2.inner_def v v).symm
    _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

section FourierBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem continuous_pointwise_fourier {f : E → ℂ} (hf : Integrable f volume) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

theorem pointwise_fourier_test {f : E → ℂ} (hf : Integrable f volume)
    (g : 𝓢(E, ℂ)) :
    (∫ x, g x * 𝓕 f x) = ∫ x, 𝓕 g x * f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ E) (ν := volume) Real.continuous_fourierChar continuous_inner hf g.integrable
  change (∫ x, 𝓕 f x * g x) = ∫ x, f x *
    VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E).flip g x at h
  have hflip : (innerₗ E).flip = innerₗ E := by
    ext x y
    exact real_inner_comm x y
  rw [hflip] at h
  simpa only [mul_comm, ← SchwartzMap.fourier_coe] using h

/-- No regularity assumption is added to `L1 ∩ L2`: distributional
uniqueness supplies the pointwise representative of the L2 transform. -/
theorem lp_fourier_ae_pointwise {f : E → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    (fun x => (𝓕 (h2.toLp f)) x) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h2.toLp f))).locallyIntegrable (by norm_num))
    (continuous_pointwise_fourier hf).locallyIntegrable
  intro g hg hc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg₂ := Complex.ofRealCLM.contDiff.comp hg
  let G : 𝓢(E, ℂ) := hg₁.toSchwartzMap hg₂
  have htd := congrArg (fun T : 𝓢'(E, ℂ) => T G)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at htd
  have hleft : (∫ x, (𝓕 G) x * (h2.toLp f) x) = ∫ x, (𝓕 G) x * f x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  have htest := pointwise_fourier_test hf G
  calc
    _ = ∫ x, G x • (𝓕 (h2.toLp f)) x := by simp [G]
    _ = ∫ x, (𝓕 G) x * (h2.toLp f) x := by simpa only [smul_eq_mul] using htd.symm
    _ = ∫ x, (𝓕 G) x * f x := hleft
    _ = ∫ x, G x * 𝓕 f x := htest.symm
    _ = _ := by simp [G]

theorem pointwise_fourier_memLp {f : E → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  (Lp.memLp (𝓕 (h2.toLp f))).ae_eq (lp_fourier_ae_pointwise hf h2)

theorem integral_norm_sq_toLp {f : E → ℂ} (h2 : MemLp f 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = ‖h2.toLp f‖ ^ 2 := by
  rw [← lp_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with x hx
  rw [hx]

/-- Classical Plancherel for integrable square-integrable inputs,
including nonsmooth bounded densities. -/
theorem pointwise_plancherel {f : E → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    (∫ x, ‖𝓕 f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ x, ‖(𝓕 (h2.toLp f)) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [lp_fourier_ae_pointwise hf h2] with x hx
      rw [hx]
    _ = ‖𝓕 (h2.toLp f)‖ ^ 2 := lp_integral_norm_sq _
    _ = ‖h2.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = _ := (integral_norm_sq_toLp h2).symm

end FourierBridge
end CircularLaw
