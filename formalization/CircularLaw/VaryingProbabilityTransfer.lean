import CircularLaw.VaryingProbabilityConvergence

/-!
# Transferring probability convergence through a uniform vanishing error

The sample spaces may vary with dimension. An eventual pointwise error
bound tending to zero transfers the same deterministic probability limit.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_probability_of_uniform_error {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f g : ∀ n, Ω n → ℝ} {a : ℝ} {e : ℕ → ℝ}
    (hf : VaryingConvergesInProbability μ f a) (he : Tendsto e atTop (𝓝 0))
    (hBound : ∀ᶠ n in atTop, ∀ ω, |g n ω - f n ω| ≤ e n) :
    VaryingConvergesInProbability μ g a := by
  intro epsilon hEpsilon
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hf (epsilon / 2) (by linarith))
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hBound, he.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < epsilon / 2))]
    with n hn heN
  apply measureReal_mono
  · intro ω hω
    change epsilon / 2 < |f n ω - a|
    by_contra h
    have hTriangle := abs_sub_le (g n ω) (f n ω) a
    have hfN := le_of_not_gt h
    change epsilon < |g n ω - a| at hω
    have hError := hn ω
    linarith
  · finiteness

theorem varying_probability_of_vanishing_tolerances {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f : ∀ n, Ω n → ℝ} {a : ℝ}
    {tolerance probabilityBound : ℕ → ℝ}
    (hTolerance : Tendsto tolerance atTop (𝓝 0))
    (hProbability : Tendsto probabilityBound atTop (𝓝 0))
    (hBound : ∀ᶠ n in atTop,
      (μ n).real {ω | tolerance n < |f n ω - a|} ≤ probabilityBound n) :
    VaryingConvergesInProbability μ f a := by
  intro epsilon hEpsilon
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hProbability
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hBound, hTolerance.eventually (gt_mem_nhds hEpsilon)] with n hn ht
  apply le_trans (measureReal_mono (μ := μ n) ?_) hn
  intro ω hω
  exact ht.trans hω

end CircularLaw
