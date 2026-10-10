import CircularLaw.LogarithmicStages
import CircularLaw.PrefixNegativeDeviation

/-!
# A checked slow choice giving the full negative-prefix limit

The full negative logarithms in the actual two-floor prefix converge
along a positive decreasing fraction chosen sufficiently slowly. The
proof uses weak convergence, the limiting linear small-value mass bound
and a finite limiting logarithmic integral, without assuming empirical
full logarithmic convergence. Retained zeros have vanishing probability.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def negativePrefixStageTolerance (C : ℝ) (K : ℕ) (ν : Measure ℝ≥0) (k : ℕ) : ℝ :=
  (5 / 4 : ℝ) * (logarithmicStageFraction C K k * logarithmicStageCutoff K k) +
    2 * diagonalAccuracy k +
    |(∫ t, clippedNegativeLog (logarithmicStageCutoff K k) t ∂ν) -
      ∫ t, hermitizationNegativeLog t ∂ν|

theorem negativePrefixStageTolerance_tendsto (C : ℝ) (K : ℕ) (ν : Measure ℝ≥0)
    (hν : FiniteLogarithmicIntegral ν) :
    Tendsto (negativePrefixStageTolerance C K ν) atTop (𝓝 0) := by
  have hIntegral := (clippedNegativeLog_integral_tendsto hν).comp
    (logarithmicStageCutoff_tendsto K)
  have hError := (hIntegral.sub_const (∫ t, hermitizationNegativeLog t ∂ν)).abs
  have hProduct := (logarithmicStageFraction_mul_cutoff_tendsto C K).const_mul (5 / 4 : ℝ)
  have hAccuracy := diagonalAccuracy_tendsto.const_mul 2
  simpa only [negativePrefixStageTolerance, Function.comp_apply, sub_self, abs_zero,
    mul_zero, zero_add] using (hProduct.add hAccuracy).add hError

theorem exists_slow_rounded_negative_prefix_convergence_with_constraints {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hAnti : ∀ n ω, Antitone (s n ω)) (hν : FiniteLogarithmicIntegral ν)
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    {K : ℕ} (hK : Real.log (4 * C) ≤ (K : ℝ))
    (Q : ℕ → ℕ → Prop) (hQEventual : ∀ k, ∀ᶠ n in atTop, Q k n) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧
      VaryingConvergesInProbability μ
        (fun n ω => roundedNegativePrefixMean (s n ω) (logarithmicStageFraction C K (q n))
          (logarithmicStageFraction_pos hC K (q n)).le)
        (∫ t, hermitizationNegativeLog t ∂ν) ∧
      Tendsto (fun n => (μ n).real {ω | empiricalPrefixHasZero (s n ω)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, Q (q n) n := by
  let A := ∫ t, hermitizationNegativeLog t ∂ν
  let a := fun k => ∫ t, clippedNegativeLog (logarithmicStageCutoff K k) t ∂ν
  let P := fun k n =>
    (μ n).real {ω | empiricalPrefixHasSmall (s n ω)
      (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K k))
      (Real.exp (-(logarithmicStageCutoff K k : ℝ)))} < diagonalAccuracy k ∧
    (μ n).real {ω | diagonalAccuracy k <
      |empiricalNonnegativeMean (s n ω) (clippedNegativeLog (logarithmicStageCutoff K k)) - a k|} <
        diagonalAccuracy k ∧
    2 * (logarithmicStageCutoff K k : ℝ) / n ≤ diagonalAccuracy k ∧ 0 < n
  have hP : ∀ k, ∀ᶠ n in atTop, P k n := by
    intro k
    have hEta := logarithmicStageFraction_pos hC K k
    have hEtaOne := logarithmicStageFraction_le_one hC hK k
    have hFraction : ∀ᶠ n in atTop, logarithmicStageFraction C K k ≤
        (n - bernoulliSqueezePrefixLength n (logarithmicStageFraction C K k) : ℕ) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact bernoulli_squeeze_removed_fraction_lower (by omega) hEta.le hEtaOne
    have hSmall := empirical_prefix_lower_bound_of_linear_mass μ s ν
      (fun n => bernoulliSqueezePrefixLength n (logarithmicStageFraction C K k))
      hWeak hAnti hC hEta hMass hFraction
    rw [logarithmicStageFraction_threshold hC K k] at hSmall
    have hClip := (empirical_weak_clipped_negative hWeak
      (Nat.cast_nonneg (logarithmicStageCutoff K k))) (diagonalAccuracy k) (diagonalAccuracy_pos k)
    have hRound : Tendsto (fun n : ℕ => 2 * (logarithmicStageCutoff K k : ℝ) / n)
        atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hSmall.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
      hClip.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
      hRound.eventually (gt_mem_nhds (diagonalAccuracy_pos k)), eventually_ge_atTop 1]
      with n hnSmall hnClip hnRound hn
    exact ⟨hnSmall, hnClip, hnRound.le, by omega⟩
  obtain ⟨q, hMono, hQ, hBoth⟩ := exists_monotone_slow_diagonal
    (fun k n => P k n ∧ Q k n) (fun k => (hP k).and (hQEventual k))
  have hCurrent := hBoth.mono (fun _ h => h.1)
  have hConstraint := hBoth.mono (fun _ h => h.2)
  refine ⟨q, hMono, hQ, ?_, ?_, hConstraint⟩
  · have hTolerance := (negativePrefixStageTolerance_tendsto C K ν hν).comp hQ
    have hProbability := (diagonalAccuracy_tendsto.const_mul 2).comp hQ
    apply varying_probability_of_vanishing_tolerances μ
      (show Tendsto (fun n => negativePrefixStageTolerance C K ν (q n)) atTop (𝓝 0) from
        hTolerance)
      (show Tendsto (fun n => 2 * diagonalAccuracy (q n)) atTop (𝓝 0) from by
        simpa only [Function.comp_apply, mul_zero] using hProbability)
    filter_upwards [hCurrent] with n hn
    have hGeom := rounded_prefix_negative_deviation_probability_bound (μ n) (s n) hn.2.2.2
      (logarithmicStageFraction_pos hC K (q n)).le
      (logarithmicStageFraction_le_one hC hK (q n))
      (Nat.cast_nonneg (logarithmicStageCutoff K (q n)))
      (diagonalAccuracy (q n)) (a (q n)) A
    have hThreshold : (5 / 4 : ℝ) * (logarithmicStageFraction C K (q n) *
        logarithmicStageCutoff K (q n)) + 2 * (logarithmicStageCutoff K (q n) : ℝ) / n +
        diagonalAccuracy (q n) + |a (q n) - A| ≤ negativePrefixStageTolerance C K ν (q n) := by
      change _ ≤ (5 / 4 : ℝ) * (logarithmicStageFraction C K (q n) *
        logarithmicStageCutoff K (q n)) + 2 * diagonalAccuracy (q n) + |a (q n) - A|
      have hRound := hn.2.2.1
      linarith
    have hSubset : {ω | negativePrefixStageTolerance C K ν (q n) <
        |roundedNegativePrefixMean (s n ω) (logarithmicStageFraction C K (q n))
          (logarithmicStageFraction_pos hC K (q n)).le - A|} ⊆
        {ω | (5 / 4 : ℝ) * (logarithmicStageFraction C K (q n) * logarithmicStageCutoff K (q n)) +
          2 * (logarithmicStageCutoff K (q n) : ℝ) / n + diagonalAccuracy (q n) + |a (q n) - A| <
            |roundedNegativePrefixMean (s n ω) (logarithmicStageFraction C K (q n))
              (logarithmicStageFraction_pos hC K (q n)).le - A|} := by
      intro ω hω
      exact hThreshold.trans_lt hω
    have hMeasure := (measureReal_mono (μ := μ n) hSubset).trans hGeom
    exact hMeasure.trans (by have hSmall := hn.1; have hClip := hn.2.1; linarith)
  · have hAccuracy := diagonalAccuracy_tendsto.comp hQ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAccuracy
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [hCurrent] with n hn
    apply le_trans (measureReal_mono (μ := μ n) ?_) hn.1.le
    intro ω hω
    exact empirical_prefix_zero_subset_small (s n ω)
      (Real.exp_pos (-(logarithmicStageCutoff K (q n) : ℝ))) hω

theorem exists_slow_rounded_negative_prefix_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hAnti : ∀ n ω, Antitone (s n ω)) (hν : FiniteLogarithmicIntegral ν)
    {C : ℝ} (hC : 0 < C)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t)
    {K : ℕ} (hK : Real.log (4 * C) ≤ (K : ℝ)) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧
      VaryingConvergesInProbability μ
        (fun n ω => roundedNegativePrefixMean (s n ω) (logarithmicStageFraction C K (q n))
          (logarithmicStageFraction_pos hC K (q n)).le)
        (∫ t, hermitizationNegativeLog t ∂ν) ∧
      Tendsto (fun n => (μ n).real {ω | empiricalPrefixHasZero (s n ω)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction C K (q n)))}) atTop (𝓝 0) := by
  obtain ⟨q, hMono, hQ, hNegative, hZero, _⟩ :=
    exists_slow_rounded_negative_prefix_convergence_with_constraints
      μ s ν hWeak hAnti hν hC hMass hK (fun _ _ => True)
      (fun _ => Eventually.of_forall (fun _ => trivial))
  exact ⟨q, hMono, hQ, hNegative, hZero⟩

end CircularLaw
