import CircularLaw.LogComparisonGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating the good/bad logarithmic distance comparison

The two distances may have any joint law. Only their first moments and
individual deviations from the common reference center are used.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem log_comparison_exception_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} {m : ℝ} (hm : 0 < m) :
    μ.real {ω | f ω < m / 2 ∨ g ω < m / 2} ≤
      μ.real {ω | m / 2 ≤ |f ω - m|} + μ.real {ω | m / 2 ≤ |g ω - m|} := by
  have hCover : {ω | f ω < m / 2 ∨ g ω < m / 2} ⊆
      {ω | m / 2 ≤ |f ω - m|} ∪ {ω | m / 2 ≤ |g ω - m|} := by
    intro ω hω
    rcases hω with hω | hω
    · left
      change m / 2 ≤ |f ω - m|
      rw [abs_of_nonpos (by linarith)]
      linarith
    · right
      change m / 2 ≤ |g ω - m|
      rw [abs_of_nonpos (by linarith)]
      linarith
  exact (measureReal_mono hCover).trans (measureReal_union_le _ _)

theorem log_comparison_expectation_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {η U m : ℝ} (hη : 0 < η) (hηU : η ≤ U) (hm : 0 < m)
    (hBounds : ∀ᵐ ω ∂μ, η ≤ f ω ∧ f ω ≤ U ∧ η ≤ g ω ∧ g ω ≤ U)
    (hfInt : Integrable (fun ω => |f ω - m|) μ)
    (hgInt : Integrable (fun ω => |g ω - m|) μ) :
    (∫ ω, |Real.log (f ω) - Real.log (g ω)| ∂μ) ≤
      (2 / m) * ((∫ ω, |f ω - m| ∂μ) + (∫ ω, |g ω - m| ∂μ)) +
        Real.log (U / η) *
          (μ.real {ω | m / 2 ≤ |f ω - m|} + μ.real {ω | m / 2 ≤ |g ω - m|}) := by
  let δ := Real.log (U / η)
  let B := {ω | f ω < m / 2 ∨ g ω < m / 2}
  let L := fun ω => |Real.log (f ω) - Real.log (g ω)|
  have hδ : 0 ≤ δ := Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa only [one_mul] using hηU))
  have hB : MeasurableSet B :=
    (measurableSet_lt hf measurable_const).union (measurableSet_lt hg measurable_const)
  have hL : Measurable L := (hf.log.sub hg.log).abs
  have hLInt : Integrable L μ := (integrable_const δ).mono' hL.aestronglyMeasurable (by
    filter_upwards [hBounds] with ω hω
    simp only [L, Real.norm_eq_abs, abs_abs]
    exact abs_log_sub_log_le_range hη hω.1 hω.2.2.1 hω.2.1 hω.2.2.2)
  have hBadInt : Integrable (B.indicator (fun _ => δ)) μ := (integrable_const δ).indicator hB
  have hGoodInt : Integrable (fun ω => (2 / m) * (|f ω - m| + |g ω - m|)) μ :=
    (hfInt.add hgInt).const_mul (2 / m)
  have hIntegral := integral_mono_ae hLInt (hGoodInt.add hBadInt) (by
    filter_upwards [hBounds] with ω hω
    simpa only [L, B, δ, Set.indicator_apply, Set.mem_setOf_eq, Pi.add_apply] using
      log_comparison_good_bad_pointwise hη hm hω.1 hω.2.2.1 hω.2.1 hω.2.2.2)
  have hBad := log_comparison_exception_probability (f := f) (g := g) μ hm
  have hWeighted := mul_le_mul_of_nonneg_left hBad hδ
  simp only [Pi.add_apply] at hIntegral
  rw [integral_add hGoodInt hBadInt, integral_const_mul, integral_add hfInt hgInt,
    integral_indicator_const δ hB, smul_eq_mul] at hIntegral
  change _ ≤ _ + μ.real B * δ at hIntegral
  change δ * μ.real B ≤ _ at hWeighted
  change _ ≤ _
  dsimp only [δ] at hIntegral hWeighted
  nlinarith

end CircularLaw
