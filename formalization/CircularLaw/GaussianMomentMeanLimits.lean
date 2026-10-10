import CircularLaw.GaussianMomentCycleBound
import CircularLaw.DimensionPowerLimit

/-!
# Actual zero-shift Gaussian moment means converge at every order

The proved cycle bound makes every normalized pairing term at most one.
Terms at the maximal exponent tend to one and all other terms vanish.
Thus the actual even singular-moment mean converges to the exact number
of maximal-exponent permutations. `GaussianZeroCatalanMoments.lean` later
identifies this count with the Catalan number. `GaussianMomentConvergence.lean` proves
convergence of the actual random moments to these counts.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianZeroShiftSingularMomentMean (n k : ℕ) : ℝ :=
  ∫ x : GaussianSquareSample n, (∫ t, (t : ℝ) ^ (2 * (k + 1)) ∂gaussianSingularMeasure 0 x)
    ∂gaussianSquareMatrixLaw n

theorem gaussian_zero_shift_moment_mean_eq_cycle_sum (n k : ℕ) :
    gaussianZeroShiftSingularMomentMean n k =
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        (n : ℝ) ^ gaussianGramCycleExponent k σ / (n : ℝ) ^ (k + 2) := by
  rw [gaussianZeroShiftSingularMomentMean, gaussian_zero_shift_singular_moment_cycle_integral,
    Finset.sum_div]
  rfl

theorem gaussian_zero_shift_moment_mean_nonneg (n k : ℕ) :
    0 ≤ gaussianZeroShiftSingularMomentMean n k := by
  rw [gaussian_zero_shift_moment_mean_eq_cycle_sum]
  apply Finset.sum_nonneg
  intro σ _
  positivity

theorem gaussian_zero_shift_moment_mean_le_factorial {n : ℕ} (hn : 0 < n) (k : ℕ) :
    gaussianZeroShiftSingularMomentMean n k ≤ ((k + 1).factorial : ℝ) := by
  rw [gaussian_zero_shift_moment_mean_eq_cycle_sum]
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin (k + 1)), (1 : ℝ) :=
      Finset.sum_le_sum (fun σ _ =>
        dimension_power_ratio_le_one hn (gaussian_gram_cycle_exponent_bound k σ))
    _ = _ := by simp [Fintype.card_perm]

theorem gaussian_leading_moment_count_eq_indicator_sum (k : ℕ) :
    (gaussianLeadingMomentCount k : ℝ) =
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        if gaussianGramCycleExponent k σ = k + 2 then (1 : ℝ) else 0 := by
  rw [gaussianLeadingMomentCount, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

theorem gaussian_zero_shift_moment_mean_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => gaussianZeroShiftSingularMomentMean n k) atTop
      (𝓝 (gaussianLeadingMomentCount k : ℝ)) := by
  simp only [gaussian_zero_shift_moment_mean_eq_cycle_sum]
  rw [gaussian_leading_moment_count_eq_indicator_sum]
  exact tendsto_finset_sum Finset.univ (fun σ _ =>
    dimension_power_ratio_tendsto (gaussianGramCycleExponent k σ) (k + 2)
      (gaussian_gram_cycle_exponent_bound k σ))

end CircularLaw
