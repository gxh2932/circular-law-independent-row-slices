import CircularLaw.RetainedPrefixSmallValues

/-!
# Retained-prefix lower bounds with varying array dimensions

The sequence index and the array dimension need not coincide. The exact
removed fraction and limiting linear mass bound control the retained
small-value event on the actual varying probability spaces.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem indexed_empirical_prefix_small_probability_tendsto {Ω : ℕ → Type*} {q : ℕ → ℕ}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin (q n) → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hAnti : ∀ n ω, Antitone (s n ω)) {a b eta : ℝ} (hab : a < b) (hEta : 0 < eta)
    (hFraction : ∀ᶠ n in atTop, eta ≤ (q n - ell n : ℕ) / (q n : ℝ))
    (hLimit : (∫ t, smallValueCutoff a b t ∂ν) ≤ eta / 2) :
    Tendsto (fun n => (μ n).real {ω | empiricalPrefixHasSmall (s n ω) (ell n) a})
      atTop (𝓝 0) := by
  have hCutoff := hWeak (smallValueCutoff a b) (continuous_smallValueCutoff a b)
    ⟨1, fun t => by
      rw [abs_of_nonneg (smallValueCutoff_bounds a b t).1]
      exact (smallValueCutoff_bounds a b t).2⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hCutoff (eta / 4) (by linarith))
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hFraction] with n hn
  apply measureReal_mono
  · intro ω hω
    have hMean := hn.trans
      (smallValueCutoff_mean_ge_removed_fraction (s n ω) (hAnti n ω) hab hω)
    have hAbs := le_abs_self
      (empiricalNonnegativeMean (s n ω) (smallValueCutoff a b) - ∫ t, smallValueCutoff a b t ∂ν)
    change eta / 4 < |empiricalNonnegativeMean (s n ω) (smallValueCutoff a b) -
      ∫ t, smallValueCutoff a b t ∂ν|
    linarith
  · finiteness

theorem indexed_empirical_prefix_lower_bound_of_linear_mass {Ω : ℕ → Type*} {q : ℕ → ℕ}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin (q n) → ℝ≥0)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (ell : ℕ → ℕ)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hAnti : ∀ n ω, Antitone (s n ω)) {C eta : ℝ} (hC : 0 < C) (hEta : 0 < eta)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    (hFraction : ∀ᶠ n in atTop, eta ≤ (q n - ell n : ℕ) / (q n : ℝ)) :
    Tendsto (fun n => (μ n).real
      {ω | empiricalPrefixHasSmall (s n ω) (ell n) (eta / (4 * C))}) atTop (𝓝 0) := by
  have hGap : eta / (4 * C) < eta / (2 * C) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hProduct := mul_pos hEta hC
    nlinarith
  apply indexed_empirical_prefix_small_probability_tendsto μ s ν ell hWeak hAnti hGap hEta hFraction
  calc
    _ ≤ ν.real {x : ℝ≥0 | (x : ℝ) < eta / (2 * C)} :=
      smallValueCutoff_integral_le_mass ν hGap
    _ ≤ C * (eta / (2 * C)) := hMass _ (by positivity)
    _ = eta / 2 := by field_simp


end CircularLaw
