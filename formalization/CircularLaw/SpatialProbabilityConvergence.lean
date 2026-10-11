import CircularLaw.SpatialBadArea

/-!
# Spatial integral convergence on varying probability spaces

Pointwise convergence in probability almost everywhere and square
integrals bounded in probability imply absolute spatial integral
convergence. The proof uses actual joint event probabilities, Fubini,
dominated convergence, Markov and a deterministic Young split.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology

namespace CircularLaw

theorem spatial_absolute_integral_tendsto_zero_in_probability {Ω : ℕ → Type*} {X : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace X]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (f : ∀ n, Ω n → X → ℝ)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hSq : ∀ n ω, Integrable (fun x => (f n ω x) ^ 2) ν)
    (hPointwise : ∀ᵐ x ∂ν, VaryingConvergesInProbability μ (fun n ω => f n ω x) 0)
    (hSquareBound : VaryingBoundedInProbability μ (fun n ω => ∫ x, (f n ω x) ^ 2 ∂ν)) :
    VaryingConvergesInProbability μ (fun n ω => ∫ x, |f n ω x| ∂ν) 0 := by
  apply varying_probability_of_error_bound μ
  intro ε hε δ hδ
  obtain ⟨M, hM, hEvent⟩ := hSquareBound (δ / 2) (by linarith)
  let η : ℝ := ε / (4 * (ν.real univ + 1))
  let c : ℝ := ε / (4 * (M + 1))
  let t : ℝ := c * ε
  have hMass : 0 ≤ ν.real univ := measureReal_nonneg
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 < t := mul_pos hc hε
  have hηBudget : η * ν.real univ ≤ ε / 4 := by
    have hEq : η * (ν.real univ + 1) = ε / 4 := by
      dsimp [η]
      field_simp
    nlinarith
  have hcBudget : c * M ≤ ε / 4 := by
    have hEq : c * (M + 1) = ε / 4 := by
      dsimp [c]
      field_simp
    nlinarith
  have htBudget : (1 / (4 * c)) * t = ε / 4 := by
    have hcN : c ≠ 0 := hc.ne'
    dsimp [t]
    field_simp
  have hArea := spatial_bad_area_tendsto_zero_in_probability μ ν f hf hPointwise hη
  have hAreaEvent : ∀ᶠ n in atTop, (μ n).real
      {ω | t < |ν.real {x | η < |f n ω x|} - 0|} < δ / 2 :=
    (hArea t ht).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards [hEvent, hAreaEvent] with n hn hAreaN
  have hSubset : {ω | ε < |(∫ x, |f n ω x| ∂ν) - 0|} ⊆
      {ω | M < |∫ x, (f n ω x) ^ 2 ∂ν|} ∪
      {ω | t < |ν.real {x | η < |f n ω x|} - 0|} := by
    intro ω hω
    change M < |∫ x, (f n ω x) ^ 2 ∂ν| ∨ t < |ν.real {x | η < |f n ω x|} - 0|
    by_contra h
    push_neg at h
    have hSqNonneg : 0 ≤ ∫ x, (f n ω x) ^ 2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
    have hAbsNonneg : 0 ≤ ∫ x, |f n ω x| ∂ν := integral_nonneg (fun _ => abs_nonneg _)
    have hEnergy : (∫ x, (f n ω x) ^ 2 ∂ν) ≤ M := by
      simpa only [abs_of_nonneg hSqNonneg] using h.1
    have hBad : ν.real {x | η < |f n ω x|} ≤ t := by
      simpa only [sub_zero, abs_of_nonneg measureReal_nonneg] using h.2
    have hSplit := spatial_absolute_integral_split_bound ν (f n ω)
      ((hf n).comp measurable_prodMk_left) (hSq n ω) hη.le hc
    have hSquareTerm := mul_le_mul_of_nonneg_left hEnergy hc.le
    have hBadTerm := mul_le_mul_of_nonneg_left hBad
      (by positivity : (0 : ℝ) ≤ 1 / (4 * c))
    rw [htBudget] at hBadTerm
    change ε < |(∫ x, |f n ω x| ∂ν) - 0| at hω
    rw [sub_zero, abs_of_nonneg hAbsNonneg] at hω
    linarith
  have hProbability := (measureReal_mono (μ := μ n) hSubset).trans (measureReal_union_le _ _)
  exact hProbability.trans_lt (by linarith)

theorem spatial_integral_tendsto_zero_in_probability {Ω : ℕ → Type*} {X : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace X]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (f : ∀ n, Ω n → X → ℝ)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hSq : ∀ n ω, Integrable (fun x => (f n ω x) ^ 2) ν)
    (hPointwise : ∀ᵐ x ∂ν, VaryingConvergesInProbability μ (fun n ω => f n ω x) 0)
    (hSquareBound : VaryingBoundedInProbability μ (fun n ω => ∫ x, (f n ω x) ^ 2 ∂ν)) :
    VaryingConvergesInProbability μ (fun n ω => ∫ x, f n ω x ∂ν) 0 := by
  have hAbs := spatial_absolute_integral_tendsto_zero_in_probability μ ν f hf hSq hPointwise hSquareBound
  intro ε hε
  apply varying_probability_event_of_subset μ _ (hAbs ε hε)
  intro n ω hω
  have hIntegral := abs_integral_le_integral_abs (f := f n ω) (μ := ν)
  have hNonneg : 0 ≤ ∫ x, |f n ω x| ∂ν := integral_nonneg (fun _ => abs_nonneg _)
  change ε < |(∫ x, f n ω x ∂ν) - 0| at hω
  rw [sub_zero] at hω
  change ε < |(∫ x, |f n ω x| ∂ν) - 0|
  simpa only [sub_zero, abs_of_nonneg hNonneg] using (hω.trans_le hIntegral)

theorem spatial_bounded_test_integral_tendsto_zero_in_probability {Ω : ℕ → Type*} {X : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace X]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (f : ∀ n, Ω n → X → ℝ)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hSq : ∀ n ω, Integrable (fun x => (f n ω x) ^ 2) ν)
    (hPointwise : ∀ᵐ x ∂ν, VaryingConvergesInProbability μ (fun n ω => f n ω x) 0)
    (hSquareBound : VaryingBoundedInProbability μ (fun n ω => ∫ x, (f n ω x) ^ 2 ∂ν))
    (φ : X → ℝ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, |φ x| ≤ C) :
    VaryingConvergesInProbability μ (fun n ω => ∫ x, φ x * f n ω x ∂ν) 0 := by
  have hAbs := spatial_absolute_integral_tendsto_zero_in_probability μ ν f hf hSq hPointwise hSquareBound
  intro ε hε
  have hRatio : 0 < ε / (C + 1) := div_pos hε (by linarith)
  apply varying_probability_event_of_subset μ _ (hAbs (ε / (C + 1)) hRatio)
  intro n ω hω
  have hInt := (integrable_of_integrable_square ν (f n ω)
    ((hf n).comp measurable_prodMk_left) (hSq n ω)).abs
  have hBound : |∫ x, φ x * f n ω x ∂ν| ≤ C * ∫ x, |f n ω x| ∂ν := by
    have h := norm_integral_le_of_norm_le (hInt.const_mul C)
      (ae_of_all ν (fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hφ x) (abs_nonneg _)))
    simpa only [Real.norm_eq_abs, integral_const_mul] using h
  have hNonneg : 0 ≤ ∫ x, |f n ω x| ∂ν := integral_nonneg (fun _ => abs_nonneg _)
  change ε < |(∫ x, φ x * f n ω x ∂ν) - 0| at hω
  rw [sub_zero] at hω
  change ε / (C + 1) < |(∫ x, |f n ω x| ∂ν) - 0|
  rw [sub_zero, abs_of_nonneg hNonneg, div_lt_iff₀ (by linarith : (0 : ℝ) < C + 1)]
  nlinarith

end CircularLaw
