import CircularLaw.EmpiricalLogGeometry
import CircularLaw.VaryingProbabilityConvergence

/-!
# Weak and logarithmic convergence of the actual empirical laws

Weak convergence in probability is expressed by bounded continuous test
functions. A finite logarithmic limit is encoded with the zero event:
an empirical logarithmic integral with any zero entry is minus infinity.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

def EmpiricalWeakConvergenceInProbability {Ω : ℕ → Type*} {q : ℕ → ℕ}
    [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (s : ∀ n, Ω n → Fin (q n) → ℝ≥0) (ν : Measure ℝ≥0) : Prop :=
  ∀ f : ℝ≥0 → ℝ, Continuous f → (∃ C : ℝ, ∀ t, |f t| ≤ C) →
    VaryingConvergesInProbability μ (fun n ω => empiricalNonnegativeMean (s n ω) f) (∫ t, f t ∂ν)

def EmpiricalLogConvergenceInProbability {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | empiricalHasZero (s n ω) ∨
    ε < |empiricalNonnegativeMean (s n ω) (fun t => Real.log (t : ℝ)) - ∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν|})
    atTop (𝓝 0)

theorem empirical_log_convergence_real {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => Real.log (t : ℝ)))
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) := by
  intro ε hε
  exact varying_probability_event_of_subset μ (fun _ _ h => Or.inr h) (hLog ε hε)

theorem empirical_zero_probability_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν) :
    Tendsto (fun n => (μ n).real {ω | empiricalHasZero (s n ω)}) atTop (𝓝 0) :=
  varying_probability_event_of_subset μ (fun _ _ h => Or.inl h) (hLog 1 zero_lt_one)

theorem empirical_log_convergence_of_real_and_zero_probability {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hReal : VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => Real.log (t : ℝ)))
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν))
    (hZero : Tendsto (fun n => (μ n).real {ω | empiricalHasZero (s n ω)}) atTop (𝓝 0)) :
    EmpiricalLogConvergenceInProbability μ s ν := by
  intro epsilon hEpsilon
  have hSum := hZero.add (hReal epsilon hEpsilon)
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  exact Eventually.of_forall (fun _ => measureReal_union_le _ _)

theorem empirical_weak_clipped_positive {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} {s : ∀ n, Ω n → Fin n → ℝ≥0} {ν : Measure ℝ≥0}
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν) {T : ℝ} (hT : 0 ≤ T) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (clippedPositiveLog T))
      (∫ t, clippedPositiveLog T t ∂ν) :=
  hWeak _ (continuous_clippedPositiveLog T) ⟨T, fun t => by
    rw [abs_of_nonneg (clippedPositiveLog_bounds hT t).1]
    exact (clippedPositiveLog_bounds hT t).2⟩

theorem empirical_weak_clipped_negative {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} {s : ∀ n, Ω n → Fin n → ℝ≥0} {ν : Measure ℝ≥0}
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν) {T : ℝ} (hT : 0 ≤ T) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (clippedNegativeLog T))
      (∫ t, clippedNegativeLog T t ∂ν) :=
  hWeak _ (continuous_clippedNegativeLog T) ⟨T, fun t => by
    rw [abs_of_nonneg (clippedNegativeLog_bounds hT t).1]
    exact (clippedNegativeLog_bounds hT t).2⟩

end CircularLaw
