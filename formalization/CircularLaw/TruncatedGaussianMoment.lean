import CircularLaw.GaussianMedianMean

/-!
# First moments with a large Gaussian-tail prefactor

After a cutoff absorbs the prefactor, the positive excess has a plain
Gaussian tail. Layer-cake bounds its first moment independently of that
prefactor. This is the square-root-logarithm estimate used for slice rows.
-/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussian_positive_excess_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {A c R : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hR : 0 ≤ R)
    (hAbsorb : A * Real.exp (-c * R ^ 2) ≤ 1)
    (hTail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ f ω} ≤ A * Real.exp (-c * t ^ 2))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ max (f ω - R) 0} ≤ Real.exp (-c * t ^ 2) := by
  have hCover : {ω | t ≤ max (f ω - R) 0} ⊆ {ω | R + t ≤ f ω} := by
    intro ω hω
    change t ≤ max (f ω - R) 0 at hω
    change R + t ≤ f ω
    by_cases h : 0 ≤ f ω - R
    · rw [max_eq_left h] at hω
      linarith
    · rw [max_eq_right (le_of_not_ge h)] at hω
      linarith
  calc
    _ ≤ A * Real.exp (-c * (R + t) ^ 2) :=
      (measureReal_mono hCover).trans (hTail (R + t) (by linarith))
    _ ≤ A * Real.exp (-c * R ^ 2 + -c * t ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hR ht.le]
    _ = (A * Real.exp (-c * R ^ 2)) * Real.exp (-c * t ^ 2) := by
      rw [Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-c * t ^ 2) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hAbsorb (Real.exp_pos _).le

theorem gaussian_tail_first_moment_cutoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hfInt : Integrable f μ)
    {A c R : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hR : 0 ≤ R)
    (hAbsorb : A * Real.exp (-c * R ^ 2) ≤ 1)
    (hTail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ f ω} ≤ A * Real.exp (-c * t ^ 2)) :
    (∫ ω, f ω ∂μ) ≤ R + Real.sqrt (Real.pi / c) / 2 := by
  let g := fun ω => max (f ω - R) 0
  have hg : Measurable g := (hf.sub measurable_const).max measurable_const
  have hgInt : Integrable g μ := (hfInt.sub (integrable_const R)).pos_part
  have hgNonneg : 0 ≤ᵐ[μ] g := ae_of_all μ (fun ω => le_max_right _ _)
  have hGaussInt := (integrable_exp_neg_mul_sq hc).integrableOn (s := Set.Ioi (0 : ℝ))
  have hLin : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / c) / 2) := by
    rw [lintegral_eq_lintegral_meas_le μ hgNonneg hg.aemeasurable,
      ← integral_gaussian_Ioi c,
      ofReal_integral_eq_lintegral_ofReal hGaussInt (ae_of_all _ (fun t => (Real.exp_pos _).le))]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (gaussian_positive_excess_tail μ hA hc hR hAbsorb hTail ht)
  have hgBound : (∫ ω, g ω ∂μ) ≤ Real.sqrt (Real.pi / c) / 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae hgNonneg hg.aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.sqrt (Real.pi / c) / 2)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hLin
  have hIntegral : (∫ ω, f ω ∂μ) ≤ R + (∫ ω, g ω ∂μ) := by
    have h := integral_mono hfInt ((integrable_const R).add hgInt)
      (fun ω => (show f ω ≤ R + g ω from by dsimp [g]; linarith [le_max_left (f ω - R) 0]))
    simpa only [Pi.add_apply, integral_add (integrable_const R) hgInt, integral_const, probReal_univ, one_smul] using h
  exact hIntegral.trans (by linarith)

end CircularLaw
