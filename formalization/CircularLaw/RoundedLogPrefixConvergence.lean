import CircularLaw.RoundedNegativePrefixConvergence
import CircularLaw.EmpiricalPositivePrefixConvergence

/-!
# The full signed logarithmic potential of a slowly retained prefix

The negative prefix converges along the checked slow stage choice. Tight
second moments give the positive prefix limit along the same choice.
Their difference is the literal negative logarithmic prefix potential.
The retained-zero event is explicitly proved to have vanishing probability.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace CircularLaw

theorem empirical_prefix_mean_sub {n ell : ℕ} (s : Fin n → ℝ≥0) (hElln : ell ≤ n)
    (f g : ℝ≥0 → ℝ) :
    empiricalNonnegativePrefixMean s hElln (fun t => f t - g t) =
      empiricalNonnegativePrefixMean s hElln f - empiricalNonnegativePrefixMean s hElln g := by
  simp only [empiricalNonnegativePrefixMean, Finset.sum_sub_distrib, sub_div]

def roundedLogPotentialPrefixMean {n : ℕ} (s : Fin n → ℝ≥0) (epsilon : ℝ)
    (hEpsilon : 0 ≤ epsilon) : ℝ :=
  empiricalNonnegativePrefixMean s (bernoulli_squeeze_prefix_le hEpsilon)
    (fun t => -Real.log (t : ℝ))

theorem roundedLogPotentialPrefixMean_decomposition {n : ℕ} (s : Fin n → ℝ≥0)
    (epsilon : ℝ) (hEpsilon : 0 ≤ epsilon) :
    roundedLogPotentialPrefixMean s epsilon hEpsilon = roundedNegativePrefixMean s epsilon hEpsilon -
      empiricalNonnegativePrefixMean s (bernoulli_squeeze_prefix_le hEpsilon) hermitizationPositiveLog := by
  have hFun : (fun t : ℝ≥0 => -Real.log (t : ℝ)) =
      fun t => hermitizationNegativeLog t - hermitizationPositiveLog t := by
    funext t
    have h := hermitization_log_decomposition t
    linarith
  unfold roundedLogPotentialPrefixMean
  rw [hFun, empirical_prefix_mean_sub]
  rfl

theorem exists_slow_rounded_log_prefix_convergence_with_constraints {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hAnti : ∀ n ω, Antitone (s n ω)) (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    {K : ℕ} (hK : Real.log (4 * C) ≤ (K : ℝ))
    (Q : ℕ → ℕ → Prop) (hQEventual : ∀ k, ∀ᶠ n in atTop, Q k n) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧
      VaryingConvergesInProbability μ
        (fun n ω => roundedLogPotentialPrefixMean (s n ω) (logarithmicStageFraction C K (q n))
          (logarithmicStageFraction_pos hC K (q n)).le)
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) ∧
      Tendsto (fun n => (μ n).real {ω | empiricalPrefixHasZero (s n ω)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, Q (q n) n := by
  obtain ⟨q, hMono, hQ, hNegative, hZero, hConstraint⟩ :=
    exists_slow_rounded_negative_prefix_convergence_with_constraints
      μ s ν hWeak hAnti hν hC hMass hK Q hQEventual
  refine ⟨q, hMono, hQ, ?_, hZero, hConstraint⟩
  have hEpsilon : Tendsto (fun n => logarithmicStageFraction C K (q n)) atTop (𝓝 0) :=
    (logarithmicStageFraction_tendsto C K).comp hQ
  have hNonneg := fun n => (logarithmicStageFraction_pos hC K (q n)).le
  have hRemoved := bernoulli_squeeze_prefix_removed_fraction_tendsto hNonneg hEpsilon
  have hPositive := empirical_prefix_positive_log_convergence μ s ν
    (fun n => bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))
    (fun n => bernoulli_squeeze_prefix_le (hNonneg n)) hWeak hν.2 hRemoved hMoment
  have hBoth := varying_probability_sub μ hNegative hPositive
  have hLimit : (∫ t, hermitizationNegativeLog t ∂ν) - (∫ t, hermitizationPositiveLog t ∂ν) =
      -(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) := by
    rw [hermitization_log_integral_decomposition hν.2]
    ring
  rw [hLimit] at hBoth
  simpa only [roundedLogPotentialPrefixMean_decomposition] using hBoth

theorem exists_slow_rounded_log_prefix_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hAnti : ∀ n ω, Antitone (s n ω)) (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    {K : ℕ} (hK : Real.log (4 * C) ≤ (K : ℝ)) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧
      VaryingConvergesInProbability μ
        (fun n ω => roundedLogPotentialPrefixMean (s n ω) (logarithmicStageFraction C K (q n))
          (logarithmicStageFraction_pos hC K (q n)).le)
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν)) ∧
      Tendsto (fun n => (μ n).real {ω | empiricalPrefixHasZero (s n ω)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) := by
  obtain ⟨q, hMono, hQ, hLog, hZero, _⟩ :=
    exists_slow_rounded_log_prefix_convergence_with_constraints
      μ s ν hWeak hAnti hν hMoment hC hMass hK (fun _ _ => True)
      (fun _ => Eventually.of_forall (fun _ => trivial))
  exact ⟨q, hMono, hQ, hLog, hZero⟩

end CircularLaw
