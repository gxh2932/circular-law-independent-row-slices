import CircularLaw.GaussianTwoTraceCycleBound
import CircularLaw.DimensionPowerLimit

/-!
# Connected two-trace pairing contributions vanish

Every pairing that crosses the trace blocks has exponent strictly below
the product normalization. Its contribution is at most `1/n`, so the
whole mixed sum is at most `factorial(2*order)/n` and tends to zero.
`GaussianMomentVariance.lean` identifies this sum with the actual
normalized singular-moment variance through the two-trace expansion.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def gaussianTwoTraceMixedContribution (n k : ℕ) : ℝ :=
  ∑ σ : Equiv.Perm (Bool × Fin (k + 1)),
    if ∃ a, (σ a).1 ≠ a.1 then
      (n : ℝ) ^ gaussianTwoTraceCycleExponent k σ / (n : ℝ) ^ (2 * (k + 1) + 2)
    else 0

theorem gaussian_two_trace_mixed_contribution_nonneg (n k : ℕ) :
    0 ≤ gaussianTwoTraceMixedContribution n k := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs <;> positivity

theorem gaussian_two_trace_mixed_contribution_bound {n : ℕ} (hn : 0 < n) (k : ℕ) :
    gaussianTwoTraceMixedContribution n k ≤ ((2 * (k + 1)).factorial : ℝ) / n := by
  unfold gaussianTwoTraceMixedContribution
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Bool × Fin (k + 1)), 1 / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hCross : ∃ a, (σ a).1 ≠ a.1
      · rw [if_pos hCross]
        apply dimension_power_ratio_le_inverse hn
        have h := gaussian_two_trace_mixed_cycle_exponent_bound k σ hCross
        omega
      · rw [if_neg hCross]
        positivity
    _ = _ := by
      simp [Fintype.card_perm, Fintype.card_prod, nsmul_eq_mul, div_eq_mul_inv]

theorem gaussian_two_trace_mixed_contribution_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => gaussianTwoTraceMixedContribution n k) atTop (𝓝 0) := by
  have hLimit : Tendsto (fun n : ℕ => ((2 * (k + 1)).factorial : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((2 * (k + 1)).factorial : ℝ)
    simpa only [mul_zero, mul_one_div] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun n => gaussian_two_trace_mixed_contribution_nonneg n k))
    ((eventually_gt_atTop 0).mono (fun _ hn => gaussian_two_trace_mixed_contribution_bound hn k))

end CircularLaw
