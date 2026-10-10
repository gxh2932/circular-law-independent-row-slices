import CircularLaw.LLYThirdGridBudgets

/-!
# Entropy absorption for the constructed LLY third-class net

Both literal net cardinalities are bounded before simplifying their
logarithms. The large grid pays only the first prefix; the fine scalar
grid contributes one additional logarithmic degree cost.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyThirdNetCountBound (n d r k₁ k₂ k₃ : ℕ) (δ : ℝ) : ℕ :=
  (smallCoordinateSets n (k₁ - 1)).card * (smallCoordinateSets n (k₂ - 1)).card *
    (smallCoordinateSets n (k₃ - 1)).card *
      (llyGridCount (llyThirdNetResolution d)
          ((6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3) ^ (k₁ - 1) *
        llyGridCount (llyThirdNetResolution d) ((d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3) ^ (k₂ - 1) *
          llyGridCount (llyThirdNetResolution d) (4 / 3) ^ (k₃ - 1)) *
        llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ)

def llyThirdNetCountEntropy (n d r k₁ k₂ k₃ : ℕ) (a δ : ℝ) : ℝ :=
  3 * (n : ℝ) * smallSetEntropy a +
    (k₁ - 1 : ℕ) * Real.log (llyGridCount (llyThirdNetResolution d)
      ((6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)) +
    (k₂ - 1 : ℕ) * Real.log (llyGridCount (llyThirdNetResolution d) ((d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)) +
    (k₃ - 1 : ℕ) * Real.log (llyGridCount (llyThirdNetResolution d) (4 / 3)) +
    Real.log (llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ))

theorem lly_third_net_card_product_le_count (n d r k₁ k₂ k₃ : ℕ) (δ : ℝ) :
    (llyThirdNonconstantNet n d r k₁ k₂ k₃ (llyThirdNetResolution d)).card *
      (meanCorrectedScalarNet (llyThirdNetResolution d) d (1 / 3) δ).card ≤
        llyThirdNetCountBound n d r k₁ k₂ k₃ δ := by
  have hNet := lly_third_net_card_le n d r k₁ k₂ k₃ (llyThirdNetResolution d)
  have hScalar := meanCorrectedScalarNet_card_le (llyThirdNetResolution d) d (1 / 3) δ
  simpa only [llyThirdNetCountBound, llyGridCount, pow_mul] using Nat.mul_le_mul hNet hScalar

theorem lly_third_net_count_entropy_bound {n d r k₁ k₂ k₃ : ℕ} {a δ : ℝ}
    (ha : 0 < a) (haOne : a ≤ 1)
    (hFirst : ((k₁ - 1 : ℕ) : ℝ) ≤ a * n)
    (hSecond : ((k₂ - 1 : ℕ) : ℝ) ≤ a * n)
    (hThird : ((k₃ - 1 : ℕ) : ℝ) ≤ a * n) :
    (llyThirdNetCountBound n d r k₁ k₂ k₃ δ : ℝ) ≤
      Real.exp (llyThirdNetCountEntropy n d r k₁ k₂ k₃ a δ) := by
  have hCH := smallCoordinateSets_card_density ha haOne hFirst
  have hCM := smallCoordinateSets_card_density ha haOne hSecond
  have hCS := smallCoordinateSets_card_density ha haOne hThird
  have hCounts :
      ((smallCoordinateSets n (k₁ - 1)).card * (smallCoordinateSets n (k₂ - 1)).card *
        (smallCoordinateSets n (k₃ - 1)).card : ℕ) ≤
          Real.exp ((n : ℝ) * smallSetEntropy a) * Real.exp ((n : ℝ) * smallSetEntropy a) *
            Real.exp ((n : ℝ) * smallSetEntropy a) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul hCH hCM (Nat.cast_nonneg _) (Real.exp_pos _).le)
      hCS (Nat.cast_nonneg _) (by positivity)
  unfold llyThirdNetCountBound
  rw [Nat.cast_mul, Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCounts (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans_eq
  rw [Nat.cast_mul, Nat.cast_mul,
    natural_power_eq_exp_log (llyGridCount_pos _ _) (k₁ - 1),
    natural_power_eq_exp_log (llyGridCount_pos _ _) (k₂ - 1),
    natural_power_eq_exp_log (llyGridCount_pos _ _) (k₃ - 1),
    ← Real.exp_log (by exact_mod_cast llyGridCount_pos (llyThirdNetResolution d * d) (1 / 3 + δ) :
      (0 : ℝ) < llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ))]
  simp only [← Real.exp_add]
  congr 1
  unfold llyThirdNetCountEntropy
  ring

theorem lly_third_net_count_entropy_simplified {n d r k₁ k₂ k₃ : ℕ} {a δ : ℝ}
    (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ)) (hδSmall : δ ≤ 1 / 100) :
    llyThirdNetCountEntropy n d r k₁ k₂ k₃ a δ ≤
      3 * (n : ℝ) * smallSetEntropy a +
        (4 * ((r : ℝ) + 2) * (k₁ - 1 : ℕ) + 4 * (k₂ - 1 : ℕ) +
          3 * (k₃ - 1 : ℕ) + 5) * Real.log (d : ℝ) := by
  have hHigh := mul_le_mul_of_nonneg_left (lly_third_high_grid_log (r := r) hd hLog)
    (Nat.cast_nonneg (k₁ - 1) : (0 : ℝ) ≤ (k₁ - 1 : ℕ))
  have hMiddle := mul_le_mul_of_nonneg_left (lly_third_middle_grid_log hd hLog)
    (Nat.cast_nonneg (k₂ - 1) : (0 : ℝ) ≤ (k₂ - 1 : ℕ))
  have hBase := mul_le_mul_of_nonneg_left (lly_third_base_grid_log hd hLog)
    (Nat.cast_nonneg (k₃ - 1) : (0 : ℝ) ≤ (k₃ - 1 : ℕ))
  have hScalar := lly_third_scalar_grid_log hd hLog hδSmall
  unfold llyThirdNetCountEntropy
  nlinarith

theorem lly_third_net_count_absorbed {n d r k₁ k₂ k₃ : ℕ} {a δ : ℝ}
    (hn : 20480 ≤ n) (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ))
    (ha : 0 < a) (haOne : a ≤ 1)
    (hFirst : ((k₁ - 1 : ℕ) : ℝ) ≤ a * n)
    (hSecond : ((k₂ - 1 : ℕ) : ℝ) ≤ a * n)
    (hThird : ((k₃ - 1 : ℕ) : ℝ) ≤ a * n)
    (hFirstCost : ((r : ℝ) + 2) * (k₁ - 1 : ℕ) ≤ (n : ℝ) / 4096)
    (hSecondCost : ((k₂ - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4096)
    (hThirdCost : ((k₃ - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4096)
    (hEntropy : smallSetEntropy a ≤ Real.log (d : ℝ) / 384) (hδSmall : δ ≤ 1 / 100) :
    (llyThirdNetCountBound n d r k₁ k₂ k₃ δ : ℝ) ≤
      Real.exp ((n : ℝ) * Real.log (d : ℝ) / 64) := by
  apply (lly_third_net_count_entropy_bound ha haOne hFirst hSecond hThird).trans
  apply Real.exp_le_exp.mpr
  apply (lly_third_net_count_entropy_simplified hd hLog hδSmall).trans
  have hLogNonneg := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hN : (20480 : ℝ) ≤ n := by exact_mod_cast hn
  have hCost : 4 * ((r : ℝ) + 2) * (k₁ - 1 : ℕ) + 4 * (k₂ - 1 : ℕ) +
      3 * (k₃ - 1 : ℕ) + 5 ≤ (n : ℝ) / 128 := by nlinarith
  have hGrid := mul_le_mul_of_nonneg_right hCost hLogNonneg
  have hSets := mul_le_mul_of_nonneg_left hEntropy (by positivity : 0 ≤ 3 * (n : ℝ))
  nlinarith

end CircularLaw
