import CircularLaw.VaryingProbabilityConvergence

/-!
# Deterministic probability limits are unique on varying spaces

If two different real limits existed, one of their deviation events
would contain every sample. Their probabilities cannot both tend to
zero under actual probability measures.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem varying_probability_limit_unique {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {f : ∀ n, Ω n → ℝ} {a b : ℝ}
    (ha : VaryingConvergesInProbability μ f a) (hb : VaryingConvergesInProbability μ f b) :
    a = b := by
  by_contra hNe
  have hDist : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hNe)
  let ε := |a - b| / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hLower (n : ℕ) :
      1 ≤ (μ n).real {x | ε < |f n x - a|} + (μ n).real {x | ε < |f n x - b|} := by
    have hSubset : Set.univ ⊆ {x | ε < |f n x - a|} ∪ {x | ε < |f n x - b|} := by
      intro x _
      change ε < |f n x - a| ∨ ε < |f n x - b|
      by_contra h
      push_neg at h
      have hTriangle := abs_sub_le a (f n x) b
      rw [abs_sub_comm a (f n x)] at hTriangle
      dsimp [ε] at h
      linarith
    calc
      _ = (μ n).real Set.univ := probReal_univ.symm
      _ ≤ (μ n).real ({x | ε < |f n x - a|} ∪ {x | ε < |f n x - b|}) :=
        measureReal_mono hSubset (measure_ne_top _ _)
      _ ≤ _ := measureReal_union_le _ _
  have hLimit := (ha ε hε).add (hb ε hε)
  simp only [add_zero] at hLimit
  obtain ⟨n, hn⟩ := (hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  exact not_le_of_gt hn (hLower n)

end CircularLaw
