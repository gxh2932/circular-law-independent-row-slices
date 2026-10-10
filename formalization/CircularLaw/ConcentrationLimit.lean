import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Passing two-event concentration bounds through almost-sure limits

Fatou on the product of two copies treats strict separated events. A
positive slack then gives the closed-event bound, preserving atoms and
allowing an arbitrary underlying probability space.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology ENNReal

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem two_event_open_bound_of_ae_limit (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {fseq : ℕ → Ω → ℝ} (hf : Measurable f) (hseq : ∀ q, Measurable (fseq q))
    (hLimit : ∀ᵐ ω ∂μ, Tendsto (fun q => fseq q ω) atTop (𝓝 (f ω)))
    (s u : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ q, μ.real {ω | fseq q ω < s} * μ.real {ω | u < fseq q ω} ≤ B) :
    μ.real {ω | f ω < s} * μ.real {ω | u < f ω} ≤ B := by
  let S : Set (Ω × Ω) := {ω | f ω < s} ×ˢ {ω | u < f ω}
  let Sq : ℕ → Set (Ω × Ω) := fun q => {ω | fseq q ω < s} ×ˢ {ω | u < fseq q ω}
  let g : Ω × Ω → ℝ≥0∞ := S.indicator (fun _ => 1)
  let I : ℕ → Ω × Ω → ℝ≥0∞ := fun q => (Sq q).indicator (fun _ => 1)
  have hS : MeasurableSet S := (measurableSet_lt hf measurable_const).prod (measurableSet_lt measurable_const hf)
  have hSq (q : ℕ) : MeasurableSet (Sq q) :=
    (measurableSet_lt (hseq q) measurable_const).prod (measurableSet_lt measurable_const (hseq q))
  have hMeas (q : ℕ) : Measurable (I q) := measurable_const.indicator (hSq q)
  have hPoint : ∀ᵐ z ∂μ.prod μ, g z ≤ liminf (fun q => I q z) atTop := by
    filter_upwards [(measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hLimit,
      (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hLimit] with z hFirst hSecond
    by_cases hz : z ∈ S
    · have hEv : ∀ᶠ q in atTop, z ∈ Sq q := by
        filter_upwards [hFirst.eventually (eventually_lt_nhds hz.1),
          hSecond.eventually (eventually_gt_nhds hz.2)] with q hq1 hq2
        exact ⟨hq1, hq2⟩
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [hEv] with q hq
      simp only [g, I, Set.indicator_of_mem hz, Set.indicator_of_mem hq, le_refl]
    · simpa only [g, Set.indicator_of_notMem hz] using
        (zero_le (liminf (fun q => I q z) atTop))
  have hIntegral (q : ℕ) : (∫⁻ z, I q z ∂μ.prod μ) ≤ ENNReal.ofReal B := by
    have hReal : (μ.prod μ).real (Sq q) ≤ B := by
      rw [measureReal_prod_prod]
      exact hBound q
    change (∫⁻ z, (Sq q).indicator 1 z ∂μ.prod μ) ≤ ENNReal.ofReal B
    rw [lintegral_indicator_one (hSq q)]
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal hReal
  have hFatou := (lintegral_mono_ae hPoint).trans (lintegral_liminf_le hMeas)
  have hLiminf : liminf (fun q => ∫⁻ z, I q z ∂μ.prod μ) atTop ≤ ENNReal.ofReal B := by
    simpa only [liminf_const] using liminf_le_liminf (f := atTop) (Eventually.of_forall hIntegral)
  have hENN : (μ.prod μ) S ≤ ENNReal.ofReal B := by
    have hVal : (∫⁻ z, g z ∂μ.prod μ) = (μ.prod μ) S := by
      change (∫⁻ z, S.indicator 1 z ∂μ.prod μ) = (μ.prod μ) S
      exact lintegral_indicator_one hS
    exact hVal ▸ hFatou.trans hLiminf
  have hReal : (μ.prod μ).real S ≤ B := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa only [S, measureReal_prod_prod] using hReal

end CircularLaw
