import CircularLaw.ConvexProductMedian
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Integrating Gaussian median tails and recentering at the mean

The layer-cake identity gives a dimension-free absolute first moment.
It also proves integrability, so no integrability premise is added to
the manuscript concentration theorem.
-/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussian_median_absolute_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {K : ℝ} (hK : 0 < K) (m : ℝ)
    (hTail : ∀ t : ℝ, 0 < t →
      μ.real {ω | t * K ≤ |f ω - m|} ≤ 4 * Real.exp (-t ^ 2 / 256)) :
    Integrable (fun ω => |f ω - m| / K) μ ∧
      (∫ ω, |f ω - m| / K ∂μ) ≤ 64 := by
  let g := fun ω => |f ω - m| / K
  have hg : Measurable g := (hf.sub measurable_const).abs.div_const K
  have hNonneg : 0 ≤ᵐ[μ] g := ae_of_all μ (fun ω => div_nonneg (abs_nonneg _) hK.le)
  have hGaussInt : Integrable (fun t : ℝ => 4 * Real.exp (-t ^ 2 / 256))
      (volume.restrict (Set.Ioi 0)) := by
    convert (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 256)).integrableOn.const_mul 4 using 1
    ext t
    congr 2
    ring
  have hGauss : (∫ t : ℝ in Set.Ioi 0, 4 * Real.exp (-t ^ 2 / 256)) ≤ 64 := by
    rw [integral_const_mul]
    have hEq : (∫ t : ℝ in Set.Ioi 0, Real.exp (-t ^ 2 / 256)) =
        Real.sqrt (Real.pi / (1 / 256)) / 2 := by
      convert integral_gaussian_Ioi (1 / 256) using 1
      congr 1
      ext t
      congr 1
      ring
    rw [hEq]
    have hSqrt : Real.sqrt (Real.pi / (1 / 256)) ≤ 32 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_lt_four]⟩
    linarith
  have hLin : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal 64 := by
    rw [lintegral_eq_lintegral_meas_le μ hNonneg hg.aemeasurable]
    apply le_trans _ (ENNReal.ofReal_le_ofReal hGauss)
    rw [ofReal_integral_eq_lintegral_ofReal hGaussInt
      (ae_of_all _ (fun t => by positivity))]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hSet : {ω | t ≤ g ω} = {ω | t * K ≤ |f ω - m|} := by
      ext ω
      exact le_div_iff₀ hK
    rw [hSet, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hTail t ht)
  have hgInt : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable hNonneg).mp
      (ne_of_lt (hLin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hgInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hNonneg hg.aestronglyMeasurable]
  simpa using ENNReal.toReal_mono ENNReal.ofReal_ne_top hLin

theorem gaussian_median_mean_distance (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {K : ℝ} (hK : 0 < K) (m : ℝ)
    (hTail : ∀ t : ℝ, 0 < t →
      μ.real {ω | t * K ≤ |f ω - m|} ≤ 4 * Real.exp (-t ^ 2 / 256)) :
    Integrable f μ ∧ |(∫ ω, f ω ∂μ) - m| ≤ 64 * K := by
  obtain ⟨hgInt, hgBound⟩ := gaussian_median_absolute_moment μ hf hK m hTail
  have hAbsInt : Integrable (fun ω => |f ω - m|) μ := by
    convert hgInt.mul_const K using 1
    ext ω
    exact (div_mul_cancel₀ _ hK.ne').symm
  have hDiffInt : Integrable (fun ω => f ω - m) μ := by
    apply (integrable_norm_iff (hf.sub measurable_const).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hAbsInt
  have hfInt : Integrable f μ := by
    convert hDiffInt.add (integrable_const m) using 1
    ext ω
    change f ω = f ω - m + m
    ring
  refine ⟨hfInt, ?_⟩
  have hAbsBound : (∫ ω, |f ω - m| ∂μ) ≤ 64 * K := by
    have hMul := mul_le_mul_of_nonneg_right hgBound hK.le
    rw [← integral_mul_const] at hMul
    simpa only [div_mul_cancel₀ _ hK.ne'] using hMul
  have h := abs_integral_le_integral_abs (f := fun ω => f ω - m) (μ := μ)
  rw [integral_sub hfInt (integrable_const m), integral_const, probReal_univ, one_smul] at h
  exact h.trans hAbsBound

theorem gaussian_mean_tail_of_median_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {K : ℝ} (hK : 0 < K) (m : ℝ)
    (hTail : ∀ t : ℝ, 0 < t →
      μ.real {ω | t * K ≤ |f ω - m|} ≤ 4 * Real.exp (-t ^ 2 / 256))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t * K ≤ |f ω - (∫ v, f v ∂μ)|} ≤
      (4 * Real.exp 16) * Real.exp (-(1 / 1024) * t ^ 2) := by
  have hDistance := (gaussian_median_mean_distance μ hf hK m hTail).2
  by_cases hSmall : t ≤ 128
  · have hExponent : 0 ≤ 16 - (1 / 1024) * t ^ 2 := by nlinarith
    have hExp : 1 ≤ Real.exp (16 - (1 / 1024) * t ^ 2) :=
      Real.one_le_exp_iff.mpr hExponent
    have hProb : μ.real {ω | t * K ≤ |f ω - (∫ v, f v ∂μ)|} ≤ 1 := measureReal_le_one
    rw [mul_assoc, ← Real.exp_add]
    have hEq : 16 + -(1 / 1024) * t ^ 2 = 16 - (1 / 1024) * t ^ 2 := by ring
    rw [hEq]
    exact hProb.trans (by nlinarith [Real.exp_pos (16 - (1 / 1024) * t ^ 2)])
  · have hCover : {ω | t * K ≤ |f ω - (∫ v, f v ∂μ)|} ⊆
        {ω | (t / 2) * K ≤ |f ω - m|} := by
      intro ω hω
      change t * K ≤ |f ω - (∫ v, f v ∂μ)| at hω
      change (t / 2) * K ≤ |f ω - m|
      have hTriangle : |f ω - (∫ v, f v ∂μ)| ≤ |f ω - m| + |(∫ v, f v ∂μ) - m| := by
        simpa only [sub_add_sub_cancel, abs_sub_comm] using
          abs_add_le (f ω - m) (m - (∫ v, f v ∂μ))
      have hBudget : 64 * K ≤ (t / 2) * K := by nlinarith
      linarith
    have h := (measureReal_mono hCover).trans (hTail (t / 2) (by linarith))
    have hEq : -(t / 2) ^ 2 / 256 = -(1 / 1024) * t ^ 2 := by ring
    rw [hEq] at h
    apply h.trans
    have hExp : 1 ≤ Real.exp (16 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith [Real.exp_pos (-(1 / 1024) * t ^ 2)]

end CircularLaw
