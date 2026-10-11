import CircularLaw.BoundedDensity

/-!
# Almost-everywhere Fourier inversion and density bounds

The L2 inverse transform is identified with the classical inverse integral.
This supplies inversion almost everywhere for L1/L2 inputs whose Fourier
integral is integrable, without assuming continuity of the input density.
-/

noncomputable section
open MeasureTheory Real FourierTransform
open scoped SchwartzMap FourierTransform ENNReal RealInnerProductSpace

namespace CircularLaw

section InverseBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem continuous_pointwise_fourierInv {f : E → ℂ} (hf : Integrable f volume) :
    Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous (L := -(innerₗ E))
    Real.continuous_fourierChar continuous_inner.neg hf

theorem pointwise_fourierInv_test {f : E → ℂ} (hf : Integrable f volume)
    (g : 𝓢(E, ℂ)) :
    (∫ x, g x * 𝓕⁻ f x) = ∫ x, 𝓕⁻ g x * f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -(innerₗ E)) (ν := volume) Real.continuous_fourierChar continuous_inner.neg
    hf g.integrable
  change (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x *
    VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ E)).flip g x at h
  have hflip : (-(innerₗ E)).flip = -(innerₗ E) := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  rw [hflip] at h
  change (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ (g : E → ℂ) x at h
  simpa only [mul_comm, ← SchwartzMap.fourierInv_coe] using h

theorem lp_fourierInv_ae_pointwise {f : E → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    (fun x => (𝓕⁻ (h2.toLp f)) x) =ᵐ[volume] 𝓕⁻ f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (h2.toLp f))).locallyIntegrable (by norm_num))
    (continuous_pointwise_fourierInv hf).locallyIntegrable
  intro g hg hc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg₂ := Complex.ofRealCLM.contDiff.comp hg
  let G : 𝓢(E, ℂ) := hg₁.toSchwartzMap hg₂
  have htd := congrArg (fun T : 𝓢'(E, ℂ) => T G)
    (Lp.fourierInv_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at htd
  have hleft : (∫ x, (𝓕⁻ G) x * (h2.toLp f) x) = ∫ x, (𝓕⁻ G) x * f x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  have htest := pointwise_fourierInv_test hf G
  calc
    _ = ∫ x, G x • (𝓕⁻ (h2.toLp f)) x := by simp [G]
    _ = ∫ x, (𝓕⁻ G) x * (h2.toLp f) x := by simpa only [smul_eq_mul] using htd.symm
    _ = ∫ x, (𝓕⁻ G) x * f x := hleft
    _ = ∫ x, G x * 𝓕⁻ f x := htest.symm
    _ = _ := by simp [G]

theorem pointwise_fourier_inversion_ae {f : E → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) (hF : Integrable (𝓕 f) volume) :
    f =ᵐ[volume] 𝓕⁻ (𝓕 f) := by
  have hF2 := pointwise_fourier_memLp hf h2
  have heq : hF2.toLp (𝓕 f) = 𝓕 (h2.toLp f) := by
    apply Lp.ext
    exact hF2.coeFn_toLp.trans (lp_fourier_ae_pointwise hf h2).symm
  have hinv := lp_fourierInv_ae_pointwise hF hF2
  rw [heq, fourierInv_fourier_eq] at hinv
  exact h2.coeFn_toLp.symm.trans hinv

theorem norm_pointwise_fourierInv_le (f : E → ℂ) (x : E) :
    ‖𝓕⁻ f x‖ ≤ ∫ t, ‖f t‖ := by
  rw [Real.fourierInv_eq]
  exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])

end InverseBridge

theorem bounded_density_le_fourier_integral {p : ℂ → ℝ} (hp : UnitBoundedDensity p)
    (hF : Integrable (𝓕 (fun x => (p x : ℂ))) volume) :
    ∀ᵐ x ∂volume, p x ≤ ∫ t, ‖𝓕 (fun x => (p x : ℂ)) t‖ := by
  filter_upwards [pointwise_fourier_inversion_ae hp.integrable.ofReal
    (unit_bounded_density_complex_memLp hp) hF] with x hx
  calc
    p x ≤ |p x| := le_abs_self _
    _ = ‖(p x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖𝓕⁻ (𝓕 (fun y => (p y : ℂ))) x‖ := congrArg norm hx
    _ ≤ _ := norm_pointwise_fourierInv_le _ _

end CircularLaw
