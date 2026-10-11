import CircularLaw.ReplacementPrinciple

/-! # Transfer of an actual spectral limit through the proved replacement principle -/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CircularLaw

theorem bl_distance_limit_probability_transfer {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (ν : Measure ℂ)
    (hComparison : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω))}) atTop (𝓝 0))
    (hLimitB : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (B n ω)) ν}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) ν}) atTop (𝓝 0) := by
  intro ε hε
  have hHalf : 0 < ε / 2 := half_pos hε
  have hSum := (hComparison (ε / 2) hHalf).add (hLimitB (ε / 2) hHalf)
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  apply Eventually.of_forall
  intro n
  apply (measureReal_mono (μ := μ n) (s₂ :=
    {ω | ENNReal.ofReal (ε / 2) < boundedLipschitzDistance
      (empiricalSpectralMeasure (A n ω)) (empiricalSpectralMeasure (B n ω))} ∪
    {ω | ENNReal.ofReal (ε / 2) < boundedLipschitzDistance (empiricalSpectralMeasure (B n ω)) ν})
    ?_).trans (measureReal_union_le _ _)
  intro ω hω
  by_contra hNot
  have hGood : boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω)) ≤ ENNReal.ofReal (ε / 2) ∧
      boundedLipschitzDistance (empiricalSpectralMeasure (B n ω)) ν ≤ ENNReal.ofReal (ε / 2) := by
    simpa only [mem_union, mem_setOf_eq, not_or, not_lt] using hNot
  have hBound := (boundedLipschitzDistance_triangle (empiricalSpectralMeasure (A n ω))
    (empiricalSpectralMeasure (B n ω)) ν).trans (add_le_add hGood.1 hGood.2)
  rw [← ENNReal.ofReal_add hHalf.le hHalf.le, add_halves] at hBound
  exact not_lt_of_ge hBound hω

theorem matrix_replacement_limit_transfer {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ) (ν : Measure ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hLog : ∀ᵐ z : ℂ ∂volume, VaryingConvergesInProbability μ
      (fun n ω => normalizedLogDeterminant (A n ω) z - normalizedLogDeterminant (B n ω) z) 0)
    (hLimitB : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (B n ω)) ν}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) ν}) atTop (𝓝 0) :=
  bl_distance_limit_probability_transfer μ A B ν
    (matrix_replacement_principle μ A B hA hB hEnergyA hEnergyB hLog) hLimitB

end CircularLaw
