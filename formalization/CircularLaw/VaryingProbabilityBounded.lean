import CircularLaw.VaryingProbabilityConvergence
import Mathlib.Tactic

/-!
# Algebra and domination of quantities bounded in probability

These statements keep the actual probability law at every dimension.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_bounded_probability_add {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f g : ∀ n, Ω n → ℝ}
    (hf : VaryingBoundedInProbability μ f) (hg : VaryingBoundedInProbability μ g) :
    VaryingBoundedInProbability μ (fun n ω => f n ω + g n ω) := by
  intro δ hδ
  obtain ⟨M, hM, hEventF⟩ := hf (δ / 2) (by linarith)
  obtain ⟨N, hN, hEventG⟩ := hg (δ / 2) (by linarith)
  refine ⟨M + N, add_pos hM hN, ?_⟩
  filter_upwards [hEventF, hEventG] with n hnF hnG
  have hSubset : {ω | M + N < |f n ω + g n ω|} ⊆
      {ω | M < |f n ω|} ∪ {ω | N < |g n ω|} := by
    intro ω hω
    change M < |f n ω| ∨ N < |g n ω|
    by_contra h
    push_neg at h
    change M + N < |f n ω + g n ω| at hω
    linarith [abs_add_le (f n ω) (g n ω)]
  exact ((measureReal_mono (μ := μ n) hSubset).trans (measureReal_union_le _ _)).trans_lt
    (by linarith)

theorem varying_bounded_probability_const_mul {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f : ∀ n, Ω n → ℝ}
    (hf : VaryingBoundedInProbability μ f) (c : ℝ) :
    VaryingBoundedInProbability μ (fun n ω => c * f n ω) := by
  intro δ hδ
  obtain ⟨M, hM, hEvent⟩ := hf δ hδ
  refine ⟨|c| * M + 1, by positivity, ?_⟩
  filter_upwards [hEvent] with n hn
  apply lt_of_le_of_lt _ hn
  apply measureReal_mono
  · intro ω hω
    change |c| * M + 1 < |c * f n ω| at hω
    change M < |f n ω|
    rw [abs_mul] at hω
    by_contra h
    have hMul := mul_le_mul_of_nonneg_left (le_of_not_gt h) (abs_nonneg c)
    linarith
  · finiteness

theorem varying_bounded_probability_of_abs_le {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f g : ∀ n, Ω n → ℝ}
    (hg : VaryingBoundedInProbability μ g)
    (hBound : ∀ᶠ n in atTop, ∀ ω, |f n ω| ≤ |g n ω|) :
    VaryingBoundedInProbability μ f := by
  intro δ hδ
  obtain ⟨M, hM, hEvent⟩ := hg δ hδ
  refine ⟨M, hM, ?_⟩
  filter_upwards [hEvent, hBound] with n hn hBn
  apply lt_of_le_of_lt _ hn
  apply measureReal_mono
  · intro ω hω
    exact hω.trans_le (hBn ω)
  · finiteness

end CircularLaw
