import CircularLaw.GaussianShiftedAlternatingRecursion
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Formal power-series equations for actual shifted Gaussian moments

The even coefficients are the actual limiting Gram trace moments. The
odd coefficients use the negative alternating-word value. The checked
first-pair recurrences give both coupled equations and their cubic
elimination. These are formal series identities; evaluation at a spectral
parameter and identification of the logarithmic integral are separate
analytic obligations.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def gaussianShiftedOddValue (r : ℝ) (k : ℕ) : ℂ :=
  -gaussianShiftedAlternatingValue r (2 * k + 1)

theorem gaussian_shifted_odd_value_recursion (r : ℝ) (k : ℕ) :
    gaussianShiftedOddValue r k =
      (r : ℂ) * gaussianShiftedAlternatingValue r (2 * k) +
        ∑ j : Fin k, gaussianShiftedAlternatingValue r (2 * j.val) *
          gaussianShiftedOddValue r (k - j.val - 1) := by
  unfold gaussianShiftedOddValue
  rw [gaussian_shifted_alternating_odd_recursion, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

def gaussianShiftedEvenMomentSeries (r : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => gaussianShiftedAlternatingValue r (2 * k))

def gaussianShiftedOddMomentSeries (r : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (gaussianShiftedOddValue r)

theorem gaussian_shifted_even_series_coeff (r : ℝ) (k : ℕ) :
    PowerSeries.coeff k (gaussianShiftedEvenMomentSeries r) =
      gaussianShiftedMomentMeanLimit (r : ℂ) k := by
  rw [gaussianShiftedEvenMomentSeries, PowerSeries.coeff_mk,
    gaussian_shifted_alternating_value_even]

theorem gaussian_shifted_even_series_measure_moment (r : ℝ) (k : ℕ) :
    (PowerSeries.coeff k (gaussianShiftedEvenMomentSeries r)).re =
      ∫ t, (t : ℝ) ^ (2 * k) ∂gaussianShiftedSingularLimit (r : ℂ) := by
  rw [gaussian_shifted_even_series_coeff, gaussian_shifted_limit_even_moments]
  rfl

theorem power_series_coeff_product_fin (p q : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (p * q) =
      ∑ j : Fin (k + 1), PowerSeries.coeff j.val p * PowerSeries.coeff (k - j.val) q := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i p * PowerSeries.coeff j q) k,
    Fin.sum_univ_eq_sum_range
      (fun j => PowerSeries.coeff j p * PowerSeries.coeff (k - j) q) (k + 1)]

theorem gaussian_shifted_even_moment_series_equation (r : ℝ) :
    gaussianShiftedEvenMomentSeries r = 1 + PowerSeries.X *
      (PowerSeries.C (r : ℂ) * gaussianShiftedOddMomentSeries r +
        gaussianShiftedEvenMomentSeries r * gaussianShiftedEvenMomentSeries r) := by
  ext k
  cases k with
  | zero =>
    simp [gaussianShiftedEvenMomentSeries, gaussian_shifted_alternating_value_zero]
  | succ k =>
    simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false,
      zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
      power_series_coeff_product_fin, gaussianShiftedEvenMomentSeries,
      gaussianShiftedOddMomentSeries, PowerSeries.coeff_mk, gaussianShiftedOddValue]
    simpa only [mul_neg, neg_mul] using gaussian_shifted_alternating_even_recursion r k

theorem gaussian_shifted_odd_moment_series_equation (r : ℝ) :
    gaussianShiftedOddMomentSeries r =
      PowerSeries.C (r : ℂ) * gaussianShiftedEvenMomentSeries r +
        PowerSeries.X * (gaussianShiftedEvenMomentSeries r * gaussianShiftedOddMomentSeries r) := by
  ext k
  cases k with
  | zero =>
    simpa [gaussianShiftedEvenMomentSeries, gaussianShiftedOddMomentSeries,
      gaussian_shifted_alternating_value_zero] using gaussian_shifted_odd_value_recursion r 0
  | succ k =>
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      power_series_coeff_product_fin, gaussianShiftedEvenMomentSeries,
      gaussianShiftedOddMomentSeries, PowerSeries.coeff_mk]
    simpa only [show ∀ j : ℕ, k + 1 - j - 1 = k - j by omega] using
      gaussian_shifted_odd_value_recursion r (k + 1)

theorem gaussian_shifted_even_moment_series_cubic (r : ℝ) :
    PowerSeries.X ^ 2 * gaussianShiftedEvenMomentSeries r ^ 3 -
      2 * PowerSeries.X * gaussianShiftedEvenMomentSeries r ^ 2 +
        (1 + PowerSeries.X * (1 - PowerSeries.C (r : ℂ) ^ 2)) *
          gaussianShiftedEvenMomentSeries r - 1 = 0 := by
  have hEven := gaussian_shifted_even_moment_series_equation r
  have hOdd := gaussian_shifted_odd_moment_series_equation r
  linear_combination (1 - PowerSeries.X * gaussianShiftedEvenMomentSeries r) * hEven +
    PowerSeries.X * PowerSeries.C (r : ℂ) * hOdd

end CircularLaw
