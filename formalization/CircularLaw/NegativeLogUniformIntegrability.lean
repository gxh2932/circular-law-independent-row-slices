import CircularLaw.ExtendedEmpiricalLog

/-!
# Full negative logarithmic uniform-integrability lemma

The hypotheses are the manuscript's weak convergence, finite logarithmic
limit and tight second moments. Both conclusions use the literal empirical
measure and extended logarithmic values, with infinity at zero. All finite
mean, truncation, probability-limit and bottom-index inputs are proved.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CircularLaw

theorem negative_log_tail_measure_threshold {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T →
      Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
        ∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure (s n ω)}) atTop (𝓝 0) := by
  obtain ⟨T0, hT0, hTail⟩ := empirical_negative_log_UI_threshold μ s ν hWeak hLog hν hMoment hε
  refine ⟨T0, hT0, ?_⟩
  intro T hT
  have hEq : (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      ∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure (s n ω)}) =ᶠ[atTop]
      (fun n => (μ n).real {ω | EmpiricalNegativeLogTailEvent (s n ω) T ε}) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    congr 1
    ext ω
    exact empiricalNegativeLogTail_lintegral_event (by omega) (s n ω) (hT0.le.trans hT) hε
  exact (tendsto_congr' hEq).mpr (hTail T hT)

theorem negative_log_tail_measure_limsup {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => limsup (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      ∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure (s n ω)}) atTop) atTop (𝓝 0) := by
  obtain ⟨T0, _, hTail⟩ := negative_log_tail_measure_threshold μ s ν hWeak hLog hν hMoment hε
  have hEq : (fun T : ℝ => limsup (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      ∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure (s n ω)}) atTop) =ᶠ[atTop]
      (fun _ => 0) := (eventually_ge_atTop T0).mono (fun T hT => (hTail T hT).limsup_eq)
  exact (tendsto_congr' hEq).mpr tendsto_const_nhds

theorem bottom_negative_log_extended_convergence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    (r : ℕ → ℕ) (hr : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      empiricalExtendedBottomNegativeLog (s n ω) (r n)}) atTop (𝓝 0) := by
  have hEq : (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      empiricalExtendedBottomNegativeLog (s n ω) (r n)}) =ᶠ[atTop]
      (fun n => (μ n).real {ω | EmpiricalBottomLogTailEvent (s n ω) (r n) ε}) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    congr 1
    ext ω
    exact empiricalExtendedBottomNegativeLog_event (by omega) (s n ω) (r n) hε
  exact (tendsto_congr' hEq).mpr (empirical_bottom_log_convergence μ s ν hWeak hLog hν hMoment r hr hε)

/-- Both source conclusions for nonnegative decreasing random arrays.
    The finite-log hypothesis records the actual Lebesgue integral semantics;
    its convergence condition treats zero entries as minus infinity. -/
def NegativeLogUniformIntegrabilityLemma : Prop :=
  ∀ (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)),
    (∀ n, IsProbabilityMeasure (μ n)) →
    ∀ (s : ∀ n, Ω n → Fin n → ℝ≥0),
    (∀ n j, Measurable (fun ω => s n ω j)) → (∀ n ω, Antitone (s n ω)) →
    ∀ (ν : Measure ℝ≥0), IsProbabilityMeasure ν → FiniteLogarithmicIntegral ν →
    EmpiricalWeakConvergenceInProbability μ s ν → EmpiricalLogConvergenceInProbability μ s ν →
    VaryingBoundedInProbability μ (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)) →
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun T : ℝ => limsup (fun n => (μ n).real {ω | ENNReal.ofReal ε <
        ∫⁻ t, extendedNegativeLogTail T t ∂empiricalNonnegativeMeasure (s n ω)}) atTop) atTop (𝓝 0)) ∧
    (∀ r : ℕ → ℕ, Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
        empiricalExtendedBottomNegativeLog (s n ω) (r n)}) atTop (𝓝 0))

theorem negative_log_uniform_integrability_lemma : NegativeLogUniformIntegrabilityLemma := by
  intro Ω _ μ hμ s _hs _hSorted ν _hProbν hν hWeak hLog hMoment
  letI := hμ
  exact ⟨fun _ hε => negative_log_tail_measure_limsup μ s ν hWeak hLog hν hMoment hε,
    fun r hr _ hε => bottom_negative_log_extended_convergence μ s ν hWeak hLog hν hMoment r hr hε⟩

end CircularLaw
