import CircularLaw.SquareSliceSingularValues
import CircularLaw.LogarithmicNetCost

/-!
# Absorbing the polynomial factor in the intermediate scale

The literal lower band makes the source deletion indices valid and gives
`log(d) <= d^(1/96)` uniformly. Thus division of the surviving radius by
`d` is absorbed by increasing its exponential constant by one.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem intermediate_radius_div_degree {d : ℕ} (hd : 0 < d) (R : ℝ)
    (hLog : Real.log (d : ℝ) ≤ Real.rpow (d : ℝ) (1 / 96)) :
    Real.exp (-(R + 1) * Real.rpow (d : ℝ) (1 / 96)) ≤
      Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    _ ≤ Real.exp (-R * Real.rpow (d : ℝ) (1 / 96) - Real.log d) :=
      Real.exp_le_exp.mpr (by nlinarith only [hLog])
    _ = _ := by rw [Real.exp_sub, Real.exp_log hdR]

theorem eventually_intermediate_singular_parameters {C σ : ℝ} (hC : 0 < C) (hσ : σ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      4 ≤ d ∧ 4 * d ^ 3 ≤ n ∧ Real.log (d : ℝ) ≤ Real.rpow (d : ℝ) (1 / 96) := by
  have hBudget : ∀ᶠ d : ℕ in atTop, Real.log (d : ℝ) ≤ Real.rpow (d : ℝ) (1 / 96) := by
    simpa only [zero_add, one_mul] using
      eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 96)
        (by norm_num : (0 : ℝ) < 1) 0 1 (by norm_num)
  filter_upwards [eventually_fresh_row_gaussian_parameters hC hσ,
    eventually_degree_property_uniform hC (eventually_ge_atTop 4),
    eventually_degree_property_uniform hC hBudget] with n hParameters hDegree hLog
  intro d hBand
  exact ⟨hDegree d hBand.1, (hParameters d hBand).2.2.2.1, hLog d hBand.1⟩

end CircularLaw
