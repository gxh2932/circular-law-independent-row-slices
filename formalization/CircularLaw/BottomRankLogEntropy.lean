import CircularLaw.BottomLogGeometry
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The entropy bound for a bottom rank interval

Distinct bottom ranks are exactly 1,...,R. Stirling's checked factorial
bound controls the sum of log(A/r) by R*(log(A/R)+1). The conventions
also cover an empty bottom interval.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem sum_successor_logs_eq_factorial (R : ℕ) :
    (∑ k : Fin R, Real.log ((k.val : ℝ) + 1)) = Real.log (R.factorial : ℝ) := by
  change (∑ k : Fin R, (fun k : ℕ => Real.log ((k : ℝ) + 1)) k.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => Real.log ((k : ℝ) + 1)) R]
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih]
    push_cast
    ring

theorem log_factorial_lower_entropy {R : ℕ} (hR : 0 < R) :
    (R : ℝ) * Real.log R - R ≤ Real.log (R.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling hR.ne'
  have hLogR : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hR)
  have hLogPi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    have hPi := Real.pi_gt_three
    linarith)
  linarith

theorem successor_log_ratio_sum_bound {A : ℝ} (hA : 0 < A) (R : ℕ) :
    (∑ k : Fin R, Real.log (A / ((k.val : ℝ) + 1))) ≤
      (R : ℝ) * (Real.log (A / R) + 1) := by
  by_cases hR : R = 0
  · subst R
    simp
  · have hRPos : 0 < R := Nat.pos_of_ne_zero hR
    have hSum : (∑ k : Fin R, Real.log (A / ((k.val : ℝ) + 1))) =
        (R : ℝ) * Real.log A - Real.log (R.factorial : ℝ) := by
      have hFormula (k : Fin R) : Real.log (A / ((k.val : ℝ) + 1)) =
          Real.log A - Real.log ((k.val : ℝ) + 1) :=
        Real.log_div hA.ne' (by positivity)
      simp_rw [hFormula]
      rw [Finset.sum_sub_distrib, sum_successor_logs_eq_factorial]
      simp
    rw [hSum, Real.log_div hA.ne' (by exact_mod_cast hR)]
    nlinarith [log_factorial_lower_entropy hRPos]

theorem bottom_rank_sum_eq {n R : ℕ} (hRn : R ≤ n) (f : ℕ → ℝ) :
    (∑ j ∈ bottomLogIndices n R, f (n - j.val)) = ∑ k : Fin R, f (k.val + 1) := by
  classical
  let rank : (j : Fin n) → j ∈ bottomLogIndices n R → Fin R := fun j hj =>
    ⟨n - j.val - 1, by
      have hjn := j.isLt
      have hjR : n - R ≤ j.val := (Finset.mem_filter.mp hj).2
      omega⟩
  apply Finset.sum_bij rank
  · intro j hj
    exact Finset.mem_univ _
  · intro i hi j hj hEq
    apply Fin.ext
    have hVal := congrArg Fin.val hEq
    have hiN := i.isLt
    have hjN := j.isLt
    dsimp only [rank] at hVal
    omega
  · intro k _
    let j : Fin n := ⟨n - (k.val + 1), by have hk := k.isLt; omega⟩
    have hj : j ∈ bottomLogIndices n R := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [j]
      have hk := k.isLt
      omega
    refine ⟨j, hj, ?_⟩
    apply Fin.ext
    dsimp only [rank, j]
    have hk := k.isLt
    omega
  · intro j hj
    congr 1
    dsimp only [rank]
    have hjn := j.isLt
    omega

theorem bottom_rank_log_ratio_sum_bound {n R : ℕ} (hRn : R ≤ n)
    {A : ℝ} (hA : 0 < A) :
    (∑ j ∈ bottomLogIndices n R, Real.log (A / ((n - j.val : ℕ) : ℝ))) ≤
      (R : ℝ) * (Real.log (A / R) + 1) := by
  rw [bottom_rank_sum_eq hRn (fun r => Real.log (A / r))]
  simpa only [Nat.cast_add, Nat.cast_one] using successor_log_ratio_sum_bound hA R

end CircularLaw
