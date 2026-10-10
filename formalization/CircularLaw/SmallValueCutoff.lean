import CircularLaw.EmpiricalWeakConvergence
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A continuous cutoff and the retained-prefix singular-value bound

The cutoff is one below `a` and zero above `b>a`. Its limiting integral
is bounded by the mass below `b`. An ordered array with a small retained
value has a whole tail below `a`, so its cutoff mean is bounded from below
by the exact tail fraction. No positivity of the discarded values is
required.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal BigOperators

namespace CircularLaw

def smallValueCutoff (a b : ℝ) (t : ℝ≥0) : ℝ :=
  max 0 (min 1 ((b - (t : ℝ)) / (b - a)))

theorem continuous_smallValueCutoff (a b : ℝ) : Continuous (smallValueCutoff a b) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.sub NNReal.continuous_coe).div_const (b - a)))

theorem smallValueCutoff_bounds (a b : ℝ) (t : ℝ≥0) :
    0 ≤ smallValueCutoff a b t ∧ smallValueCutoff a b t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem smallValueCutoff_eq_one {a b : ℝ} (hab : a < b) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ a) : smallValueCutoff a b t = 1 := by
  have hRatio : 1 ≤ (b - (t : ℝ)) / (b - a) :=
    (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  exact (congrArg (max 0) (min_eq_left hRatio)).trans (max_eq_right zero_le_one)

theorem smallValueCutoff_eq_zero {a b : ℝ} (hab : a < b) (t : ℝ≥0)
    (ht : b ≤ (t : ℝ)) : smallValueCutoff a b t = 0 := by
  have hRatio : (b - (t : ℝ)) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le
  exact max_eq_left ((min_le_right _ _).trans hRatio)

theorem smallValueCutoff_integrable (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (a b : ℝ) :
    Integrable (smallValueCutoff a b) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_smallValueCutoff a b).measurable.aestronglyMeasurable
  exact ae_of_all ν (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (smallValueCutoff_bounds a b t).1]
    exact (smallValueCutoff_bounds a b t).2)

theorem smallValueCutoff_integral_le_mass (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    {a b : ℝ} (hab : a < b) :
    (∫ t, smallValueCutoff a b t ∂ν) ≤ ν.real {t | (t : ℝ) < b} := by
  have hSet : MeasurableSet {t : ℝ≥0 | (t : ℝ) < b} :=
    measurableSet_lt NNReal.continuous_coe.measurable measurable_const
  have hInt := (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) ν).indicator hSet
  have hBound : ∀ t : ℝ≥0, smallValueCutoff a b t ≤
      Set.indicator {x : ℝ≥0 | (x : ℝ) < b} (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : (t : ℝ) < b
    · rw [Set.indicator_of_mem (show t ∈ {x : ℝ≥0 | (x : ℝ) < b} from ht)]
      exact (smallValueCutoff_bounds a b t).2
    · rw [Set.indicator_of_notMem (show t ∉ {x : ℝ≥0 | (x : ℝ) < b} from ht),
        smallValueCutoff_eq_zero hab t (le_of_not_gt ht)]
  have h := integral_mono_ae (smallValueCutoff_integrable ν a b) hInt (ae_of_all ν hBound)
  rw [integral_indicator_const (1 : ℝ) hSet, smul_eq_mul, mul_one] at h
  exact h

theorem smallValueCutoff_mean_ge_tail_fraction {n : ℕ} (s : Fin n → ℝ≥0)
    (hAnti : Antitone s) {a b : ℝ} (hab : a < b) (j : Fin n)
    (hj : (s j : ℝ) ≤ a) :
    (n - j.val : ℕ) / (n : ℝ) ≤ empiricalNonnegativeMean s (smallValueCutoff a b) := by
  have hSum : (n - j.val : ℕ) ≤ ∑ i, smallValueCutoff a b (s i) := by
    calc
      _ = ∑ _i ∈ Finset.Ici j, (1 : ℝ) := by simp
      _ = ∑ i ∈ Finset.Ici j, smallValueCutoff a b (s i) := by
        apply Finset.sum_congr rfl
        intro i hi
        symm
        apply smallValueCutoff_eq_one hab
        exact (show (s i : ℝ) ≤ s j from by exact_mod_cast hAnti (Finset.mem_Ici.mp hi)).trans hj
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (smallValueCutoff_bounds a b (s i)).1)
  simpa only [empiricalNonnegativeMean, finiteMean, Fintype.card_fin] using
    div_le_div_of_nonneg_right hSum (Nat.cast_nonneg n)

end CircularLaw
