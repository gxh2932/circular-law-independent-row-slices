import CircularLaw.LLYGradualRadiusBudgets
import CircularLaw.LLYFirstSteepAdjoint

/-!
# The gradual radius fits the first steep adjoint threshold

The comparison is needed only when the terminal rank differs from one.
At rank one the first class is empty, so its failure probability is zero.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_gradual_norm_constant_ge_first {n d r k : ℕ} (hd : 0 < d) (hk : k ≠ 1) :
    4 * llyFirstSteepNormConstant n d r ≤ llyGradualNormConstant n d r k := by
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hBase : (1 : ℝ) ≤ 6 * d := by linarith
  have hPower : (6 * (d : ℝ)) ^ r ≤ (6 * (d : ℝ)) ^ (r + 1) :=
    pow_le_pow_right₀ hBase (by omega)
  have hDegree := Real.one_le_rpow hdOne (by norm_num : (0 : ℝ) ≤ 3 / 4)
  unfold llyFirstSteepNormConstant llyGradualNormConstant
  rw [if_neg hk]
  calc
    _ = 4 * Real.sqrt n * (6 * (d : ℝ)) ^ r * 1 := by ring
    _ ≤ 4 * Real.sqrt n * (6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) := by
      gcongr

theorem lly_gradual_radius_first_threshold {n d r k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hk : k ≠ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k)) :
    (ρ / Real.sqrt n) * ρ / Real.sqrt n <
      Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) := by
  have hB := lly_gradual_norm_constant_pos hn hd (r := r) (k₁ := k)
  have hBGe := lly_gradual_norm_constant_ge_four hn hd (r := r) (k₁ := k)
  have hBFirst := lly_gradual_norm_constant_ge_first (n := n) (r := r) hd hk
  have hFirst := lly_first_steep_norm_constant_pos (r := r) hn hd
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hDegreeRoot : 1 ≤ Real.sqrt d := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hdOne
  have hQuotient : ρ / Real.sqrt n ≤ 1 / (5 * llyGradualNormConstant n d r k) := by
    apply (div_le_iff₀ hRoot).mpr
    convert hRadius using 1
    ring
  have hSquare := pow_le_pow_left₀ (div_nonneg hρ hRoot.le) hQuotient 2
  have hStrict : (1 / (5 * llyGradualNormConstant n d r k)) ^ 2 <
      1 / llyGradualNormConstant n d r k := by
    apply (lt_div_iff₀ hB).mpr
    have hCancel : (1 / (5 * llyGradualNormConstant n d r k)) ^ 2 *
        llyGradualNormConstant n d r k = 1 / (25 * llyGradualNormConstant n d r k) := by
      field_simp
      ring
    rw [hCancel]
    have hInv : 1 / (25 * llyGradualNormConstant n d r k) ≤ 1 / 100 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  calc
    _ ≤ (1 / (5 * llyGradualNormConstant n d r k)) ^ 2 := by
      convert hSquare using 1
      ring
    _ < 1 / llyGradualNormConstant n d r k := hStrict
    _ ≤ 1 / (4 * llyFirstSteepNormConstant n d r) :=
      one_div_le_one_div_of_le (by positivity) hBFirst
    _ ≤ _ := div_le_div_of_nonneg_right hDegreeRoot (by positivity)

theorem lly_first_steep_adjoint_rank_one_failure_probability {n d ℓ r : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (ζ : ℂ) (τ : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepAdjointFailure ζ rows ℓ r 1 τ) = 0 := by
  have hEmpty := lly_first_steep_rank_one_empty (n := n) (r := r) hd hℓ
  have hFalse : ∀ rows : RowSliceMatrix n d, ¬llyFirstSteepAdjointFailure ζ rows ℓ r 1 τ := by
    intro rows h
    obtain ⟨x, _, hFirst, _⟩ := h
    rw [hEmpty] at hFirst
    exact hFirst
  simp [uniformProbability, hFalse]

theorem lly_first_steep_adjoint_failure_probability_of_gradual_radius {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    {ε ρ : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k ≤ ε * n)
    (hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4)
    (hρ : 0 ≤ ρ) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k))
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyFirstSteepAdjointFailure ζ rows ℓ r k ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      (r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) +
        (n : ℝ) * Real.exp (-2 * sliceTailRate * d) := by
  by_cases hOne : k = 1
  · subst k
    rw [lly_first_steep_adjoint_rank_one_failure_probability hd hℓ]
    positivity
  · exact lly_first_steep_adjoint_failure_probability hn hd hdn hℓ hk hkn hε hSize hBudget
      hError hStride ζ hSpectral (lly_gradual_radius_first_threshold hn hd hOne hρ hRadius)

end CircularLaw
