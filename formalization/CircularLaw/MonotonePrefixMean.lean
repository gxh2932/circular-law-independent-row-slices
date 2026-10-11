import CircularLaw.FiniteMean
import Mathlib.Algebra.BigOperators.Fin

/-!
# The integer-rounded lower comparison in the logarithmic squeeze

For a monotone list of length `n`, its full arithmetic mean dominates
the mean of its first `ell` entries. A finite double-sum comparison proves
this for arbitrary real entries, so no sign restriction on logarithms
or unrounded-index convention is needed.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem monotone_prefix_mean_le {n ell : ℕ} (hEll : 0 < ell) (hElln : ell ≤ n)
    (f : ℕ → ℝ) (hf : MonotoneOn f (Set.Iio n)) :
    (∑ i ∈ Finset.range ell, f i) / ell ≤ (∑ i ∈ Finset.range n, f i) / n := by
  let L := ∑ i ∈ Finset.range ell, f i
  let R := ∑ j ∈ Finset.range (n - ell), f (ell + j)
  have hL (j : ℕ) (hj : j ∈ Finset.range (n - ell)) : L ≤ (ell : ℝ) * f (ell + j) := by
    have hjn : ell + j < n := by
      have := Finset.mem_range.mp hj
      omega
    calc
      L ≤ ∑ i ∈ Finset.range ell, f (ell + j) := by
        apply Finset.sum_le_sum
        intro i hi
        have hil := Finset.mem_range.mp hi
        exact hf (by change i < n; omega) hjn (by omega)
      _ = _ := by simp
  have hTail : ((n - ell : ℕ) : ℝ) * L ≤ (ell : ℝ) * R := by
    have h := Finset.sum_le_sum (s := Finset.range (n - ell)) hL
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum] using h
  have hSplit : (∑ i ∈ Finset.range n, f i) = L + R := by
    simpa only [Nat.add_sub_of_le hElln] using Finset.sum_range_add f ell (n - ell)
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hEll hElln)
  have hEllR : (0 : ℝ) < ell := by exact_mod_cast hEll
  rw [hSplit, div_le_div_iff₀ hEllR hn]
  rw [Nat.cast_sub hElln] at hTail
  nlinarith

end CircularLaw
