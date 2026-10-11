import CircularLaw.LogarithmicStages
import CircularLaw.VaryingProbabilityTransfer

/-!
# Probability limits along a shared slow selector

A stage-dependent random variable converges along a selector when the
fixed-stage deviation bounds hold at the selected stage and the stage
limits converge. This supplies the additional limit in the common slow
choice used by the logarithmic-potential squeeze.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_probability_of_slow_stage_limits {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (g : ℕ → ∀ n, Ω n → ℝ)
    (a : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ)
    (hQ : Tendsto q atTop atTop) (hA : Tendsto a atTop (𝓝 A))
    (hCurrent : ∀ᶠ n in atTop,
      (μ n).real {ω | diagonalAccuracy (q n) < |g (q n) n ω - a (q n)|} ≤
        diagonalAccuracy (q n)) :
    VaryingConvergesInProbability μ (fun n ω => g (q n) n ω) A := by
  have hAccuracy := diagonalAccuracy_tendsto.comp hQ
  have hError := ((hA.comp hQ).sub_const A).abs
  have hTolerance : Tendsto (fun n => diagonalAccuracy (q n) + |a (q n) - A|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using hAccuracy.add hError
  apply varying_probability_of_vanishing_tolerances μ hTolerance hAccuracy
  filter_upwards [hCurrent] with n hn
  apply le_trans (measureReal_mono (μ := μ n) ?_) hn
  intro ω hω
  change diagonalAccuracy (q n) < |g (q n) n ω - a (q n)|
  change diagonalAccuracy (q n) + |a (q n) - A| < |g (q n) n ω - A| at hω
  have hTriangle := abs_sub_le (g (q n) n ω) (a (q n)) A
  linarith

end CircularLaw
