import CircularLaw.SpatialSquareGeometry

/-!
# Pointwise probability convergence controls spatial bad area

Fubini identifies the expected area of a large-amplitude region with the
spatial integral of its actual event probabilities. Dominated convergence
and Markov then show that the bad area tends to zero in probability,
even when the sample space changes with dimension.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology

namespace CircularLaw

theorem measurable_spatial_bad_area {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : Ω → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (η : ℝ) :
    Measurable (fun ω => ν.real {x | η < |f ω x|}) := by
  have hAbs : Measurable (fun p : Ω × X => |f p.1 p.2|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hSet : MeasurableSet {p : Ω × X | η < |f p.1 p.2|} :=
    measurableSet_lt measurable_const hAbs
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left (ν := ν) hSet)

theorem measurable_spatial_event_probability {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (η : ℝ) :
    Measurable (fun x => μ.real {ω | η < |f ω x|}) := by
  have hAbs : Measurable (fun p : Ω × X => |f p.1 p.2|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hSet : MeasurableSet {p : Ω × X | η < |f p.1 p.2|} :=
    measurableSet_lt measurable_const hAbs
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_right (μ := μ) hSet)

theorem spatial_bad_area_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (f : Ω → X → ℝ) (hf : Measurable (Function.uncurry f)) (η : ℝ) :
    Integrable (fun ω => ν.real {x | η < |f ω x|}) μ := by
  apply (integrable_const (ν.real univ)).mono'
    (measurable_spatial_bad_area ν f hf η).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_mono (subset_univ _)

theorem spatial_bad_area_expectation {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (f : Ω → X → ℝ) (hf : Measurable (Function.uncurry f)) (η : ℝ) :
    (∫ ω, ν.real {x | η < |f ω x|} ∂μ) = ∫ x, μ.real {ω | η < |f ω x|} ∂ν := by
  let S : Set (Ω × X) := {p | η < |f p.1 p.2|}
  have hAbs : Measurable (fun p : Ω × X => |f p.1 p.2|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hS : MeasurableSet S := measurableSet_lt measurable_const hAbs
  have hIndicator : Integrable (S.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hS
  have hSwap := integral_integral_swap (f := fun ω x => S.indicator (fun _ => (1 : ℝ)) (ω, x))
    hIndicator
  have hLeft (ω : Ω) : (∫ x, S.indicator (fun _ => (1 : ℝ)) (ω, x) ∂ν) =
      ν.real {x | η < |f ω x|} := by
    change (∫ x, ({x | η < |f ω x|}).indicator (fun _ => (1 : ℝ)) x ∂ν) = _
    exact integral_indicator_one (measurableSet_lt measurable_const
      (by simpa only [Real.norm_eq_abs] using (hf.comp measurable_prodMk_left).norm))
  have hRight (x : X) : (∫ ω, S.indicator (fun _ => (1 : ℝ)) (ω, x) ∂μ) =
      μ.real {ω | η < |f ω x|} := by
    change (∫ ω, ({ω | η < |f ω x|}).indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
    exact integral_indicator_one (measurableSet_lt measurable_const
      (by simpa only [Real.norm_eq_abs] using (hf.comp measurable_prodMk_right).norm))
  simpa only [hLeft, hRight] using hSwap

theorem spatial_bad_area_expectation_tendsto_zero {Ω : ℕ → Type*} {X : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace X]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (f : ∀ n, Ω n → X → ℝ)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hPointwise : ∀ᵐ x ∂ν, VaryingConvergesInProbability μ (fun n ω => f n ω x) 0)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => ∫ ω, ν.real {x | η < |f n ω x|} ∂μ n) atTop (𝓝 0) := by
  have hDominated := tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
    (fun n => (measurable_spatial_event_probability (μ n) (f n) (hf n) η).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all ν (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one (μ := μ n)))
    (show ∀ᵐ x ∂ν, Tendsto (fun n => (μ n).real {ω | η < |f n ω x|}) atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [hPointwise] with x hx
      simpa only [sub_zero] using hx η hη)
  have hEq : (fun n => ∫ ω, ν.real {x | η < |f n ω x|} ∂μ n) =
      fun n => ∫ x, (μ n).real {ω | η < |f n ω x|} ∂ν := by
    funext n
    exact spatial_bad_area_expectation (μ n) ν (f n) (hf n) η
  rw [hEq]
  simpa only [integral_zero] using hDominated

theorem spatial_bad_area_tendsto_zero_in_probability {Ω : ℕ → Type*} {X : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace X]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν] (f : ∀ n, Ω n → X → ℝ)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hPointwise : ∀ᵐ x ∂ν, VaryingConvergesInProbability μ (fun n ω => f n ω x) 0)
    {η : ℝ} (hη : 0 < η) :
    VaryingConvergesInProbability μ (fun n ω => ν.real {x | η < |f n ω x|}) 0 := by
  intro t ht
  have hMean := spatial_bad_area_expectation_tendsto_zero μ ν f hf hPointwise hη
  have hUpper := hMean.div_const t
  simp only [zero_div] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  apply Eventually.of_forall
  intro n
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (μ n) (fun _ => measureReal_nonneg))
    (spatial_bad_area_integrable (μ n) ν (f n) (hf n) η) t
  apply (le_div_iff₀ ht).mpr
  rw [mul_comm]
  apply le_trans _ hMarkov
  apply mul_le_mul_of_nonneg_left _ ht.le
  apply measureReal_mono
  · intro ω hω
    change t < |ν.real {x | η < |f n ω x|} - 0| at hω
    change t ≤ ν.real {x | η < |f n ω x|}
    simpa only [sub_zero, abs_of_nonneg measureReal_nonneg] using hω.le
  · finiteness

end CircularLaw
