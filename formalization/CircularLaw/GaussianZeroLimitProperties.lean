import CircularLaw.GaussianZeroWeakLimit
import CircularLaw.EmpiricalWeakLimitUnique
import CircularLaw.GaussianEnergyConvergence

/-!
# Uniqueness and the first actual limiting Gaussian singular moments

The constructed zero-shift law is the unique finite weak limit. Comparing
the all-order moment calculation with the checked energy limit identifies
the second leading count as one. The limiting second and fourth singular
moments are consequently one and two.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

theorem gaussian_zero_shift_limit_unique (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x)) ν) :
    ν = gaussianZeroShiftSingularLimit :=
  empirical_weak_limit_unique gaussianSquareMatrixLaw
    (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x))
    ν gaussianZeroShiftSingularLimit hWeak gaussian_zero_shift_weak_convergence

theorem gaussian_leading_second_moment_count : gaussianLeadingMomentCount 0 = 1 := by
  have hEq : (fun n : ℕ => gaussianZeroShiftSingularMoment (n := n) 0) =
      (fun n : ℕ => gaussianSingularSecondMoment (n := n) 0) := by
    funext n x
    simp only [gaussianZeroShiftSingularMoment, Nat.zero_add, mul_one, gaussianSingularSecondMoment]
  have hMom := gaussian_zero_shift_moment_converges_in_probability 0
  rw [hEq] at hMom
  have h := varying_probability_limit_unique gaussianSquareMatrixLaw hMom
    gaussian_zero_shift_second_moment_converges_in_probability
  exact_mod_cast h

theorem gaussian_zero_shift_limit_second_moment :
    (∫ t, (t : ℝ) ^ 2 ∂gaussianZeroShiftSingularLimit) = 1 := by
  simpa only [Nat.zero_add, mul_one, gaussian_leading_second_moment_count, Nat.cast_one] using
    gaussian_zero_shift_limit_even_moments 0

theorem gaussian_zero_shift_limit_fourth_moment :
    (∫ t, (t : ℝ) ^ 4 ∂gaussianZeroShiftSingularLimit) = 2 := by
  simpa only [Nat.reduceAdd, Nat.reduceMul, gaussian_leading_fourth_moment_count, Nat.cast_ofNat] using
    gaussian_zero_shift_limit_even_moments 1

end CircularLaw
