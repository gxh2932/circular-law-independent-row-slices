import CircularLaw.GaussianSmallValueQuantiles
import CircularLaw.OrderedSmallValueTests
import CircularLaw.VaryingProbabilityUpperBound

/-!
# Every actual shifted Gaussian weak limit has linear mass near zero

The quantile estimate bounds every continuous small-value test outside
an event of vanishing probability. A deterministic weak-limit integral
inherits this bound. A continuous cutoff then gives the mass estimate
`nu([0,t)) <= 48*t` for every positive `t`, uniformly in the shift.
Existence of the general shifted weak limit remains a separate input.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped NNReal BigOperators Topology

namespace CircularLaw

theorem gaussian_weak_limit_small_value_test_bound (z : ℂ) (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν)
    {eta : ℝ} (hEta : 0 < eta) (hEtaUpper : eta < 1 / 3)
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (hBounds : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hZero : ∀ t : ℝ≥0, eta / 8 ≤ (t : ℝ) → f t = 0) :
    (∫ t, f t ∂ν) ≤ 2 * eta := by
  have hBound : ∃ C : ℝ, ∀ t, |f t| ≤ C := by
    refine ⟨1, fun t => ?_⟩
    rw [abs_of_nonneg (hBounds t).1]
    exact (hBounds t).2
  apply varying_probability_limit_le_of_bound_outside_bad gaussianSquareMatrixLaw
    (hWeak f hf hBound) (gaussianSmallQuantileBad eta z)
    (gaussian_small_quantile_bad_probability_tendsto hEta hEtaUpper z)
  filter_upwards [gaussian_quantile_parameters_eventually hEta hEtaUpper] with n hn
  intro x hBad
  let q := gaussianQuantileDeletion eta n
  let j : Fin n := ⟨n - 2 * q, by dsimp [q]; omega⟩
  let s := squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)
  have hAnti : Antitone s := by
    intro i k hik
    exact_mod_cast orderedSquareSingularValues_antitone (normalizedShiftedGaussianMatrix z x) hik
  have hLower : eta / 8 ≤ (s j : ℝ) := by
    change eta / 8 ≤ orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j
    exact le_of_not_gt (fun h => hBad ⟨j, rfl, h⟩)
  have hTail : n - j.val = 2 * q := by dsimp [j]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hFloor : (q : ℝ) ≤ eta * n := Nat.floor_le (by positivity)
  apply (ordered_small_value_test_mean_le_tail_fraction s hAnti f hBounds hZero j hLower).trans
  rw [hTail, Nat.cast_mul, Nat.cast_ofNat]
  apply (div_le_iff₀ hnR).mpr
  nlinarith

theorem small_value_cutoff_mass_le_integral (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {a b : ℝ} (hab : a < b) :
    ν.real {t : ℝ≥0 | (t : ℝ) < a} ≤ ∫ t, smallValueCutoff a b t ∂ν := by
  have hSet : MeasurableSet {t : ℝ≥0 | (t : ℝ) < a} :=
    measurableSet_lt NNReal.continuous_coe.measurable measurable_const
  have hInt := (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) ν).indicator hSet
  have hBound : ∀ t : ℝ≥0, Set.indicator {x : ℝ≥0 | (x : ℝ) < a} (fun _ => (1 : ℝ)) t ≤
      smallValueCutoff a b t := by
    intro t
    by_cases ht : (t : ℝ) < a
    · rw [Set.indicator_of_mem (show t ∈ {x : ℝ≥0 | (x : ℝ) < a} from ht),
        smallValueCutoff_eq_one hab t ht.le]
    · rw [Set.indicator_of_notMem (show t ∉ {x : ℝ≥0 | (x : ℝ) < a} from ht)]
      exact (smallValueCutoff_bounds a b t).1
  have h := integral_mono_ae hInt (smallValueCutoff_integrable ν a b) (ae_of_all ν hBound)
  rw [integral_indicator_const (1 : ℝ) hSet, smul_eq_mul, mul_one] at h
  exact h

theorem gaussian_shifted_weak_limit_small_mass (z : ℂ) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν)
    {t : ℝ} (ht : 0 < t) : ν.real {r : ℝ≥0 | (r : ℝ) < t} ≤ 48 * t := by
  by_cases hSmall : t < 1 / 48
  · have hBound := gaussian_weak_limit_small_value_test_bound z ν hWeak
      (eta := 16 * t) (by positivity) (by nlinarith)
      (smallValueCutoff t (2 * t)) (continuous_smallValueCutoff _ _)
      (smallValueCutoff_bounds _ _)
      (fun r hr => smallValueCutoff_eq_zero (by linarith) r (by linarith))
    exact ((small_value_cutoff_mass_le_integral ν (by linarith : t < 2 * t)).trans hBound).trans
      (by nlinarith)
  · have hOne : ν.real {r : ℝ≥0 | (r : ℝ) < t} ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := ν) (Set.subset_univ {r : ℝ≥0 | (r : ℝ) < t}))
    exact hOne.trans (by linarith)

end CircularLaw
