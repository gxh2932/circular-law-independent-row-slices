import CircularLaw.FixedShiftIntermediateTheorem

/-!
# The intermediate deletion count's logarithmic-tail budget

The exact rounded count `q0` obeys `q0*d*log(d)/n <= 5*log(d)/d`.
The right side tends to zero along every lower-band degree sequence.
This is the scalar budget used when only the bottom `q0` singular values
pay the smallest-singular-value cost in Section 9.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def intermediateDeletionLogBudget (n d : ℕ) : ℝ :=
  (intermediateDeletionCount n d : ℝ) * d * Real.log d / n

theorem intermediateDeletionLogBudget_nonneg {n d : ℕ} (hd : 1 ≤ d) :
    0 ≤ intermediateDeletionLogBudget n d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hdR)) (Nat.cast_nonneg n)

theorem intermediateDeletionCount_relative_scale (n d : ℕ) :
    (intermediateDeletionCount n d : ℝ) / ((n : ℝ) / ((d : ℝ) * Real.log d)) =
      intermediateDeletionLogBudget n d := by
  rw [div_div_eq_mul_div]
  simp only [intermediateDeletionLogBudget, mul_assoc]

theorem intermediateDeletionLogBudget_bound {n d : ℕ} (hd : 4 ≤ d)
    (hn : 4 * d ^ 3 ≤ n) :
    intermediateDeletionLogBudget n d ≤ 5 * Real.log d / d := by
  have hdPos : 0 < d := by omega
  have hnPos : 0 < n := (mul_pos (by decide) (pow_pos hdPos 3)).trans_le hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hScale : (intermediateDeletionCount n d : ℝ) * (d : ℝ) ^ 2 ≤ 5 * n := by
    apply (le_div_iff₀ (pow_pos hdR 2)).mp
    simpa only [mul_div_assoc] using intermediateDeletionCount_scale_bound hdPos hn
  have hLog := mul_le_mul_of_nonneg_right hScale (Real.log_nonneg hdOne)
  apply (div_le_div_iff₀ hnR hdR).mpr
  change ((intermediateDeletionCount n d : ℝ) * d * Real.log d) * d ≤ (5 * Real.log d) * n
  nlinarith only [hLog]

theorem intermediate_deletion_log_budget_tendsto_zero {C σ : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) (d : ℕ → ℕ)
    (hBand : ∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) :
    Tendsto (fun n : ℕ => intermediateDeletionLogBudget n (d n)) atTop (𝓝 0) := by
  have hD := degree_tendsto_atTop_of_log_lower_bound hC d (hBand.mono (fun _ h => h.1))
  have hRatio : Tendsto (fun n : ℕ => Real.log (d n : ℝ) / (d n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hD
  have hUpper : Tendsto (fun n : ℕ => 5 * Real.log (d n : ℝ) / (d n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using (tendsto_const_nhds (x := (5 : ℝ))).mul hRatio
  have hBounds : ∀ᶠ n : ℕ in atTop, 0 ≤ intermediateDeletionLogBudget n (d n) ∧
      intermediateDeletionLogBudget n (d n) ≤ 5 * Real.log (d n : ℝ) / (d n : ℝ) := by
    filter_upwards [eventually_intermediate_singular_parameters hC hσ, hBand] with n hParameters hDegree
    obtain ⟨hd, hn, _⟩ := hParameters (d n) hDegree
    exact ⟨intermediateDeletionLogBudget_nonneg (by omega), intermediateDeletionLogBudget_bound hd hn⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2))

theorem intermediate_deletion_relative_scale_tendsto_zero {C σ : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) (d : ℕ → ℕ)
    (hBand : ∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) :
    Tendsto (fun n : ℕ => (intermediateDeletionCount n (d n) : ℝ) /
      ((n : ℝ) / ((d n : ℝ) * Real.log (d n : ℝ)))) atTop (𝓝 0) := by
  simpa only [intermediateDeletionCount_relative_scale] using
    intermediate_deletion_log_budget_tendsto_zero hC hσ d hBand

end CircularLaw
