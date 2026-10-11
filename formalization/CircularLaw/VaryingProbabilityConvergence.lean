import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Probability limits on varying sample spaces

Empirical singular-value laws can live on a different probability space
at each dimension. Convergence and tightness below use their actual event
probabilities, with no common-space or finite-sample restriction.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

def VaryingConvergesInProbability {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (f : ∀ n, Ω n → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ε < |f n ω - a|}) atTop (𝓝 0)

def VaryingBoundedInProbability {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (f : ∀ n, Ω n → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ n in atTop, (μ n).real {ω | M < |f n ω|} < δ

theorem varying_probability_sub {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    {f g : ∀ n, Ω n → ℝ} {a b : ℝ}
    (hf : VaryingConvergesInProbability μ f a) (hg : VaryingConvergesInProbability μ g b) :
    VaryingConvergesInProbability μ (fun n ω => f n ω - g n ω) (a - b) := by
  intro ε hε
  have hBound (n : ℕ) :
      (μ n).real {ω | ε < |(f n ω - g n ω) - (a - b)|} ≤
        (μ n).real {ω | ε / 2 < |f n ω - a|} + (μ n).real {ω | ε / 2 < |g n ω - b|} := by
    apply (measureReal_mono (μ := μ n) (s₂ :=
      {ω | ε / 2 < |f n ω - a|} ∪ {ω | ε / 2 < |g n ω - b|}) ?_).trans
      (measureReal_union_le _ _)
    intro ω hω
    change ε / 2 < |f n ω - a| ∨ ε / 2 < |g n ω - b|
    by_contra h
    push_neg at h
    have hAbs := abs_sub_le (f n ω - a) 0 (g n ω - b)
    simp only [sub_zero, zero_sub, abs_neg] at hAbs
    have hEq : (f n ω - g n ω) - (a - b) = (f n ω - a) - (g n ω - b) := by ring
    rw [← hEq] at hAbs
    change ε < |(f n ω - g n ω) - (a - b)| at hω
    linarith
  have hSum := (hf (ε / 2) (by linarith)).add (hg (ε / 2) (by linarith))
  simp only [add_zero] at hSum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg)) (Eventually.of_forall hBound)

theorem varying_probability_of_error_bound {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f : ∀ n, Ω n → ℝ} {a : ℝ}
    (hBound : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, (μ n).real {ω | ε < |f n ω - a|} < δ) :
    VaryingConvergesInProbability μ f a := by
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [hBound ε hε δ hδ] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hn

theorem varying_probability_event_of_subset {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {A B : ∀ n, Set (Ω n)} (hAB : ∀ n, A n ⊆ B n)
    (hB : Tendsto (fun n => (μ n).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real (A n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall (fun _ => measureReal_nonneg))
    (Eventually.of_forall (fun n => measureReal_mono (hAB n)))

end CircularLaw
