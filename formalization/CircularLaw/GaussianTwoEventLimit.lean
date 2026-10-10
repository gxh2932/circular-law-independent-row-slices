import CircularLaw.ConcentrationLimit
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Closed Gaussian two-event bounds survive almost-sure approximation

Strict-event Fatou followed by positive slack handles all endpoint atoms.
The rate and leading constant do not depend on the approximation index.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussian_open_two_events_of_ae_limit (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {fseq : ℕ → Ω → ℝ} (hf : Measurable f) (hseq : ∀ q, Measurable (fseq q))
    (hLimit : ∀ᵐ ω ∂μ, Tendsto (fun q => fseq q ω) atTop (𝓝 (f ω)))
    {K : ℝ}
    (hBound : ∀ q (s t : ℝ), 0 ≤ t →
      μ.real {ω | fseq q ω ≤ s} * μ.real {ω | s + t * K ≤ fseq q ω} ≤ Real.exp (-t ^ 2 / 256))
    (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | f ω < s} * μ.real {ω | s + t * K < f ω} ≤ Real.exp (-t ^ 2 / 256) := by
  apply two_event_open_bound_of_ae_limit μ hf hseq hLimit s (s + t * K) (Real.exp_pos _).le
  intro q
  apply le_trans _ (hBound q s t ht)
  apply mul_le_mul
  · exact measureReal_mono (fun ω h => (show fseq q ω ≤ s from le_of_lt h))
  · exact measureReal_mono (fun ω h => (show s + t * K ≤ fseq q ω from le_of_lt h))
  · exact measureReal_nonneg
  · exact measureReal_nonneg

theorem gaussian_closed_two_events_of_ae_limit (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {fseq : ℕ → Ω → ℝ} (hf : Measurable f) (hseq : ∀ q, Measurable (fseq q))
    (hLimit : ∀ᵐ ω ∂μ, Tendsto (fun q => fseq q ω) atTop (𝓝 (f ω)))
    {K : ℝ} (hK : 0 < K)
    (hBound : ∀ q (s t : ℝ), 0 ≤ t →
      μ.real {ω | fseq q ω ≤ s} * μ.real {ω | s + t * K ≤ fseq q ω} ≤ Real.exp (-t ^ 2 / 256))
    (s : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | f ω ≤ s} * μ.real {ω | s + t * K ≤ f ω} ≤ Real.exp (-t ^ 2 / 256) := by
  have hTau : Tendsto (fun δ : ℝ => t - 2 * δ / K) (𝓝[>] 0) (𝓝 t) := by
    have hCont : Continuous (fun δ : ℝ => t - 2 * δ / K) := by fun_prop
    simpa only [mul_zero, zero_div, sub_zero] using
      (hCont.continuousAt (x := 0)).tendsto.mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hGauss : Tendsto (fun δ : ℝ => Real.exp (-(t - 2 * δ / K) ^ 2 / 256))
      (𝓝[>] 0) (𝓝 (Real.exp (-t ^ 2 / 256))) := by
    have hCont : Continuous (fun δ : ℝ => Real.exp (-(t - 2 * δ / K) ^ 2 / 256)) := by fun_prop
    simpa only [mul_zero, zero_div, sub_zero] using
      (hCont.continuousAt (x := 0)).tendsto.mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply ge_of_tendsto hGauss
  filter_upwards [self_mem_nhdsWithin, hTau.eventually (eventually_gt_nhds ht)] with δ hδ hPositive
  have hδ0 : 0 < δ := hδ
  have hCutoff : s + δ + (t - 2 * δ / K) * K = s + t * K - δ := by
    field_simp [hK.ne']
    ring
  have hFirst : μ.real {ω | f ω ≤ s} ≤ μ.real {ω | f ω < s + δ} := by
    apply measureReal_mono _ (measure_ne_top μ _)
    intro ω hω
    change f ω ≤ s at hω
    change f ω < s + δ
    linarith
  have hSecond : μ.real {ω | s + t * K ≤ f ω} ≤
      μ.real {ω | s + δ + (t - 2 * δ / K) * K < f ω} := by
    rw [hCutoff]
    apply measureReal_mono _ (measure_ne_top μ _)
    intro ω hω
    change s + t * K ≤ f ω at hω
    change s + t * K - δ < f ω
    linarith
  exact (mul_le_mul hFirst hSecond measureReal_nonneg measureReal_nonneg).trans
    (gaussian_open_two_events_of_ae_limit μ hf hseq hLimit hBound (s + δ) hPositive.le)

end CircularLaw
