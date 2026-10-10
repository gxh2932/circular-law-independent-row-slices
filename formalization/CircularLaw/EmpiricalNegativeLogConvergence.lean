import CircularLaw.EmpiricalPositiveLogConvergence

/-!
# Total negative logarithms converge in probability

The checked positive-log limit and the source full-log limit imply the
negative-part limit by exact finite-mean and integral decompositions.
The source log limit also makes the probability of any zero value vanish.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem empirical_negative_log_convergence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2))) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) hermitizationNegativeLog)
      (∫ t, hermitizationNegativeLog t ∂ν) := by
  have hPositive := empirical_positive_log_convergence μ s ν hWeak hν.2 hMoment
  have hRealLog := empirical_log_convergence_real μ s ν hLog
  have h := varying_probability_sub μ hPositive hRealLog
  have hFunctions : (fun n ω => empiricalNonnegativeMean (s n ω) hermitizationPositiveLog -
      empiricalNonnegativeMean (s n ω) (fun t => Real.log (t : ℝ))) =
      (fun n ω => empiricalNonnegativeMean (s n ω) hermitizationNegativeLog) := by
    funext n ω
    rw [empirical_log_decomposition]
    ring
  have hLimit : (∫ t, hermitizationPositiveLog t ∂ν) -
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) = ∫ t, hermitizationNegativeLog t ∂ν := by
    rw [hermitization_log_integral_decomposition hν.2]
    ring
  rw [hFunctions, hLimit] at h
  exact h

theorem empirical_negative_log_excess_convergence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : ∀ n, Ω n → Fin n → ℝ≥0) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {T : ℝ} (hT : 0 ≤ T) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) hermitizationNegativeLog -
        empiricalNonnegativeMean (s n ω) (clippedNegativeLog T))
      ((∫ t, hermitizationNegativeLog t ∂ν) - ∫ t, clippedNegativeLog T t ∂ν) :=
  varying_probability_sub μ (empirical_negative_log_convergence μ s ν hWeak hLog hν hMoment)
    (empirical_weak_clipped_negative hWeak hT)

end CircularLaw
