import CircularLaw.VaryingProbabilityConvergence

/-!
# Deterministic limits inherit bounds outside events of vanishing probability
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_probability_limit_le_of_bound_outside_bad {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f : ∀ n, Ω n → ℝ} {a C : ℝ}
    (hLimit : VaryingConvergesInProbability μ f a) (bad : ∀ n, Set (Ω n))
    (hBad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0))
    (hBound : ∀ᶠ n in atTop, ∀ x, x ∉ bad n → f n x ≤ C) : a ≤ C := by
  by_contra h
  have hGap : 0 < (a - C) / 2 := by linarith
  have hSum := hBad.add (hLimit ((a - C) / 2) hGap)
  simp only [add_zero] at hSum
  have hBelow := hSum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hSmall⟩ := (hBound.and hBelow).exists
  have hCover : Set.univ ⊆ bad n ∪ {x | (a - C) / 2 < |f n x - a|} := by
    intro x _
    by_cases hx : x ∈ bad n
    · exact Or.inl hx
    · apply Or.inr
      change (a - C) / 2 < |f n x - a|
      have hUpper := hn x hx
      have hAbs := le_abs_self (a - f n x)
      rw [abs_sub_comm] at hAbs
      linarith
  have hOne : 1 ≤ (μ n).real (bad n) + (μ n).real {x | (a - C) / 2 < |f n x - a|} := by
    simpa only [probReal_univ] using
      (measureReal_mono (μ := μ n) hCover).trans (measureReal_union_le _ _)
  linarith

end CircularLaw
