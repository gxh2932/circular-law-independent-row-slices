import CircularLaw.GaussianShiftedMomentSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Evaluating checked formal-series identities at convergent complex series

The coefficient series is summed in the unconditional sense. In the
finite-dimensional complex plane it is absolutely summable, so the
checked Cauchy product justifies multiplication. No convergence is
assumed for a formal series unless its coefficient sum is supplied.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def PowerSeriesSumsAt (p : PowerSeries ℂ) (q a : ℂ) : Prop :=
  HasSum (fun k : ℕ => q ^ k * PowerSeries.coeff k p) a

theorem power_series_sums_add {p s : PowerSeries ℂ} {q a b : ℂ}
    (hp : PowerSeriesSumsAt p q a) (hs : PowerSeriesSumsAt s q b) :
    PowerSeriesSumsAt (p + s) q (a + b) := by
  simpa only [PowerSeriesSumsAt, map_add, mul_add] using hp.add hs

theorem power_series_sums_sub {p s : PowerSeries ℂ} {q a b : ℂ}
    (hp : PowerSeriesSumsAt p q a) (hs : PowerSeriesSumsAt s q b) :
    PowerSeriesSumsAt (p - s) q (a - b) := by
  simpa only [PowerSeriesSumsAt, map_sub, mul_sub] using hp.sub hs

theorem power_series_sums_C (q c : ℂ) : PowerSeriesSumsAt (PowerSeries.C c) q c := by
  have hFun : (fun k : ℕ => q ^ k * PowerSeries.coeff k (PowerSeries.C c)) =
      (fun k : ℕ => if k = 0 then c else 0) := by
    funext k
    by_cases h : k = 0 <;> simp [PowerSeries.coeff_C, h]
  unfold PowerSeriesSumsAt
  rw [hFun]
  exact hasSum_ite_eq 0 c

theorem power_series_sums_one (q : ℂ) : PowerSeriesSumsAt 1 q 1 := by
  simpa only [map_one] using power_series_sums_C q 1

theorem power_series_sums_two (q : ℂ) : PowerSeriesSumsAt 2 q 2 := by
  simpa only [map_ofNat] using power_series_sums_C q 2

theorem power_series_sums_X (q : ℂ) : PowerSeriesSumsAt PowerSeries.X q q := by
  have hFun : (fun k : ℕ => q ^ k * PowerSeries.coeff k PowerSeries.X) =
      (fun k : ℕ => if k = 1 then q else 0) := by
    funext k
    by_cases h : k = 1 <;> simp [PowerSeries.coeff_X, h]
  unfold PowerSeriesSumsAt
  rw [hFun]
  exact hasSum_ite_eq 1 q

theorem power_series_sums_mul {p s : PowerSeries ℂ} {q a b : ℂ}
    (hp : PowerSeriesSumsAt p q a) (hs : PowerSeriesSumsAt s q b) :
    PowerSeriesSumsAt (p * s) q (a * b) := by
  have hCoeff (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1),
        (q ^ j * PowerSeries.coeff j p) * (q ^ (n - j) * PowerSeries.coeff (n - j) s)) =
      q ^ n * PowerSeries.coeff n (p * s) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i p * PowerSeries.coeff j s) n,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hPow : q ^ j * q ^ (n - j) = q ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hjn]
    calc
      _ = (q ^ j * q ^ (n - j)) * (PowerSeries.coeff j p * PowerSeries.coeff (n - j) s) := by ring
      _ = _ := by rw [hPow]
  have h := hasSum_sum_range_mul_of_summable_norm hp.summable.norm hs.summable.norm
  simpa only [hCoeff, hp.tsum_eq, hs.tsum_eq] using h

theorem power_series_sums_pow {p : PowerSeries ℂ} {q a : ℂ}
    (hp : PowerSeriesSumsAt p q a) (k : ℕ) : PowerSeriesSumsAt (p ^ k) q (a ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using power_series_sums_one q
  | succ k ih => simpa only [pow_succ] using power_series_sums_mul ih hp

theorem power_series_sums_zero_unique {p : PowerSeries ℂ} {q a : ℂ}
    (hp : PowerSeriesSumsAt p q a) (hZero : p = 0) : a = 0 := by
  unfold PowerSeriesSumsAt at hp
  simp only [hZero, map_zero, mul_zero] at hp
  exact hp.unique hasSum_zero

end CircularLaw
