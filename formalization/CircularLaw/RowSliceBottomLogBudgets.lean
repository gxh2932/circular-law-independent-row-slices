import CircularLaw.HermitizationBottomScalarRates
import CircularLaw.HermitizationPrefixComparison

/-!
# The vanishing row-slice bottom logarithmic budgets

The lower regime uses its exact intermediate deletion count and the
rounded n/sqrt(d) cutoff. The superlogarithmic regime uses the literal
balanced exponent and source degree hypothesis. The deterministic bounds
apply on the minimum/intermediate events, whose probabilities are separate.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lower_intermediate_minimum_cost_tendsto_zero {C σ CL : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) (hCL : 0 ≤ CL) (d : ℕ → ℕ)
    (hBand : ∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) :
    Tendsto (fun n => (intermediateDeletionCount n (d n) : ℝ) *
      max (-Real.log (lowerHermitizationCutoff n CL)) 0 / n) atTop (𝓝 0) := by
  have hCast := degree_tendsto_atTop_of_log_lower_bound hC d (hBand.mono (fun _ h => h.1))
  have hInv := hCast.inv_tendsto_atTop
  have hLogRatio : Tendsto (fun n => Real.log (d n : ℝ) / (d n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hCast
  have hRatio : Tendsto (fun n => (|Real.log C⁻¹| + Real.log (d n : ℝ)) / d n) atTop (𝓝 0) := by
    have h := (hInv.const_mul |Real.log C⁻¹|).add hLogRatio
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    exact Eventually.of_forall (fun n => by dsimp; ring)
  have hUpper := hRatio.const_mul (5 * CL * C⁻¹)
  simp only [mul_zero] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => by positivity))
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [eventually_intermediate_singular_parameters hC hσ, hBand, hLog] with n hP hB hL
  obtain ⟨hd, hn, _⟩ := hP (d n) hB
  have hLogN : Real.log n ≤ C⁻¹ * d n := by
    have h : Real.log n ≤ (d n : ℝ) / C := (le_div_iff₀ hC).mpr (by nlinarith only [hB.1])
    simpa only [div_eq_mul_inv, mul_comm] using h
  have h := lower_intermediate_minimum_cost_bound hd hn (inv_pos.mpr hC) hCL hL hLogN
  simpa only [mul_div_assoc] using h

def lowerRowBottomLogBudget (n d : ℕ) (CL R : ℝ) : ℝ :=
  (intermediateDeletionCount n d : ℝ) * max (-Real.log (lowerHermitizationCutoff n CL)) 0 / n +
    (hermitizationDeletionCount n d (1 / 2) : ℝ) * R * Real.rpow (d : ℝ) (1 / 96) / n

theorem lower_row_bottom_log_budget_tendsto_zero {C σ CL R : ℝ}
    (hC : 0 < C) (hσ : σ ≤ 1) (hCL : 0 ≤ CL) (hR : 0 ≤ R) (d : ℕ → ℕ)
    (hBand : ∀ᶠ n : ℕ in atTop, InLowerBand C σ n (d n)) (hSparse : SparseDegrees d) :
    Tendsto (fun n => lowerRowBottomLogBudget n (d n) CL R) atTop (𝓝 0) := by
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound hC d (hBand.mono (fun _ h => h.1)))
  have hLow := lower_intermediate_minimum_cost_tendsto_zero hC hσ hCL d hBand
  have hRest := hermitization_deletion_power_cost_tendsto_zero d hDegree hSparse
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : (1 / 96 : ℝ) < 1 / 2) hR
  simpa only [lowerRowBottomLogBudget, add_zero] using hLow.add hRest

theorem row_slice_lower_bottom_bound_on_good_events {n d : ℕ} (hn : 0 < n)
    (rows : RowSliceMatrix n d) (ζ : ℂ) {CL R : ℝ} (hR : 0 ≤ R)
    (hMinimum : ∀ j, lowerHermitizationCutoff n CL ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) j)
    (hIntermediate : IntermediateSingularValueEvent ζ R rows) :
    empiricalBottomNegativeLog (squareSingularValuesNNReal (fullShiftedSliceMatrix ζ rows))
      (hermitizationDeletionCount n d (1 / 2)) ≤ lowerRowBottomLogBudget n d CL R := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ : 0 < lowerHermitizationCutoff n CL := Real.rpow_pos_of_pos hnR _
  have h := row_slice_bottom_log_bound_on_intermediate_event rows ζ
    (hermitizationDeletionCount n d (1 / 2)) hτ hR hMinimum hIntermediate
  simpa only [lowerRowBottomLogBudget, add_div, mul_assoc] using h

def superlogRowBottomLogBudget (n d : ℕ) (B ε : ℝ) : ℝ :=
  (hermitizationDeletionCount n d (superlogHermitizationExponent ε) : ℝ) *
    max (-Real.log (polynomialHermitizationCutoff n B)) 0 / n

theorem superlog_row_bottom_log_budget_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ≤ n) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hLog : 1 ≤ Real.log n) (hLower : Real.rpow (Real.log n) (1 + ε) ≤ (d : ℝ)) :
    superlogRowBottomLogBudget n d B ε ≤ 2 * B / Real.rpow (Real.log n) (ε / 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLogPos : 0 < Real.log n := by linarith
  obtain ⟨ha, haOne⟩ := superlog_hermitization_exponent_range hε
  have hIdentity : (1 + ε) * superlogHermitizationExponent ε = 1 + ε / 2 := by
    have h := (superlog_hermitization_exponent_identities hε).2
    nlinarith only [h]
  have hPower := Real.rpow_le_rpow (Real.rpow_nonneg hLogPos.le (1 + ε)) hLower ha.le
  rw [← Real.rpow_mul hLogPos.le, hIdentity] at hPower
  have hRatio : Real.log n / Real.rpow (d : ℝ) (superlogHermitizationExponent ε) ≤
      1 / Real.rpow (Real.log n) (ε / 2) := by
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hdR _) (Real.rpow_pos_of_pos hLogPos _)).mpr
    simpa only [one_mul, Real.rpow_eq_pow, Real.rpow_add hLogPos, Real.rpow_one] using hPower
  unfold superlogRowBottomLogBudget
  rw [polynomial_cutoff_negative_log_eq hn hB]
  calc
    _ = ((hermitizationDeletionCount n d (superlogHermitizationExponent ε) : ℝ) / n) *
        (B * Real.log n) := by ring
    _ ≤ (2 / Real.rpow (d : ℝ) (superlogHermitizationExponent ε)) * (B * Real.log n) :=
      mul_le_mul_of_nonneg_right (hermitization_deletion_fraction_bound hn hd hdn haOne.le)
        (mul_nonneg hB hLogPos.le)
    _ = 2 * B * (Real.log n / Real.rpow (d : ℝ) (superlogHermitizationExponent ε)) := by ring
    _ ≤ 2 * B * (1 / Real.rpow (Real.log n) (ε / 2)) :=
      mul_le_mul_of_nonneg_left hRatio (by positivity)
    _ = _ := by ring

theorem superlog_row_bottom_log_budget_tendsto_zero (d : ℕ → ℕ) (hSparse : SparseDegrees d)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hLower : ∀ᶠ n : ℕ in atTop, Real.rpow (Real.log n) (1 + ε) ≤ (d n : ℝ)) :
    Tendsto (fun n => superlogRowBottomLogBudget n (d n) B ε) atTop (𝓝 0) := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hInv := ((tendsto_rpow_atTop (show 0 < ε / 2 by linarith)).comp hLog).inv_tendsto_atTop
  have hUpper : Tendsto (fun n : ℕ => 2 * B / Real.rpow (Real.log n) (ε / 2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hInv.const_mul (2 * B)
  have hLogLower := log_lower_bound_of_superlog_degree d hε.le hLower
  have hDegree : Tendsto d atTop atTop := tendsto_natCast_atTop_iff.mp
    (degree_tendsto_atTop_of_log_lower_bound zero_lt_one d hLogLower)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => by unfold superlogRowBottomLogBudget; positivity))
  filter_upwards [hLower, hLog.eventually_ge_atTop 1, eventually_valid_bernoulli_degrees hDegree hSparse]
    with n hL hLn hd
  exact superlog_row_bottom_log_budget_bound (lt_of_lt_of_le hd.1 hd.2) hd.1 hd.2 hB hε hLn hL

end CircularLaw
