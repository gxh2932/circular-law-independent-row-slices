import CircularLaw.NormHeavyEntropy

/-!
# The large edge-ratio heavy case

The fourth-power comparison bounds the entropy/log-ratio quotient.
Summing the remaining scale ratios geometrically gives the third
heavy-case budget with the complete coordinate-level mass bound.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normHeavyLargeRatioPair {m n : ℕ} (C N cap : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : Prop :=
  normHeavyOrientedPair n N x y k l ∧ cap < normHeavyScaledRatio C N M x y k l ∧
    (2 : ℝ) ^ l / Real.sqrt N < (2 : ℝ) ^ k ∧
      normHeavyEntropyArgument n x k < (normHeavyEdgeRatio C N M x y k l) ^ 4

theorem normHeavy_large_ratio_cost_bound {m n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y)
    (hPair : normHeavyLargeRatioPair C N cap M x y k l) :
    normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l ≤
      (4 * kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) := by
  have hOriented := hPair.1
  have hScaled := hPair.2.1
  have hFourth := hPair.2.2.2
  have hRatio := normHeavy_scaled_ratio_le_edge_ratio hn hC hN M hM x y hk hl hOriented.1
  have hLarge := hScaled.trans_le hRatio
  have hRatioOne : 1 < normHeavyEdgeRatio C N M x y k l := hCap.trans hLarge
  have hLogPos := Real.log_pos hRatioOne
  have hEntropy := normHeavy_discrepancy_log_bound hn hC hN hKappa M hDP x y hk hl hOriented.2 hLarge
  have hLog := real_log_fourth_power_comparison (normHeavyEntropyArgument_pos hn x hk) hFourth.le
  have hCoeff : 0 ≤ (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) := by positivity
  apply (mul_le_mul_iff_left₀ hLogPos).mp
  calc
    _ ≤ (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) *
        Real.log (normHeavyEntropyArgument n x k) := hEntropy
    _ ≤ (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) *
        (4 * Real.log (normHeavyEdgeRatio C N M x y k l)) := mul_le_mul_of_nonneg_left hLog hCoeff
    _ = ((4 * kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k))) *
        Real.log (normHeavyEdgeRatio C N M x y k l) := by ring

theorem normHeavy_large_ratio_fixed_left_sum {m n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (P : ℕ → ℕ → Prop) {k : ℕ}
    (hk : k ∈ normCoordinateLevels n x) :
    (∑ l ∈ normCoordinateLevels n y,
      if P k l ∧ normHeavyLargeRatioPair C N cap M x y k l then normHeavyLevelWeight C N M x y k l else 0) ≤
        (8 * kappa₂ / C) * normCoordinateMass n x k := by
  let T := (normCoordinateLevels n y).filter (fun l => P k l ∧ normHeavyLargeRatioPair C N cap M x y k l)
  have hMass := normCoordinateMass_nonneg n x k
  have hRoot := Real.sqrt_pos.mpr hN
  have hThreshold : 0 < Real.sqrt N * (2 : ℝ) ^ k := by positivity
  have hGeom := finite_dyadic_power_ratio_sum_bound T hThreshold (by
    intro l hl
    have hLevel := (Finset.mem_filter.mp hl).2.2.2.2.1
    have h := (div_lt_iff₀ hRoot).mp hLevel
    simpa only [mul_comm] using h.le)
  calc
    _ = ∑ l ∈ T, normHeavyLevelWeight C N M x y k l := (Finset.sum_filter _ _).symm
    _ ≤ ∑ l ∈ T, (normCoordinateMass n x k * (4 * kappa₂ / C)) *
        ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hPoint := normHeavy_large_ratio_cost_bound hn hC hN hCap hKappa M hM hDP x y hk
        (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hl).2.2
      have h := mul_le_mul_of_nonneg_left hPoint (normCoordinateMass_nonneg n x k)
      simpa only [normHeavyLevelWeight, mul_assoc] using h
    _ = (normCoordinateMass n x k * (4 * kappa₂ / C)) *
        ∑ l ∈ T, (2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k) := (Finset.mul_sum _ _ _).symm
    _ ≤ (normCoordinateMass n x k * (4 * kappa₂ / C)) * 2 :=
      mul_le_mul_of_nonneg_left hGeom (by positivity)
    _ = _ := by ring

theorem normHeavy_large_ratio_sum {m n : ℕ} (hn : 0 < n) (hm : m ≤ n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (P : ℕ → ℕ → Prop) :
    normHeavySelectedSum C N M x y (fun k l => P k l ∧ normHeavyLargeRatioPair C N cap M x y k l) ≤
      40 * kappa₂ / C := by
  have hA := normCoordinateMass_sum_unit hn (by simpa only [Fintype.card_fin] using hm) x hx
  unfold normHeavySelectedSum
  calc
    _ ≤ ∑ k ∈ normCoordinateLevels n x, (8 * kappa₂ / C) * normCoordinateMass n x k := by
      apply Finset.sum_le_sum
      intro k hk
      convert normHeavy_large_ratio_fixed_left_sum hn hC hN hCap hKappa M hM hDP x y P hk using 1
      apply Finset.sum_congr rfl
      intro l _
      by_cases h : P k l ∧ normHeavyLargeRatioPair C N cap M x y k l
      · simp only [if_pos h]
      · simp only [if_neg h]
    _ = (8 * kappa₂ / C) * ∑ k ∈ normCoordinateLevels n x, normCoordinateMass n x k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 40 * kappa₂ / C := by
      have h := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 8 * kappa₂ / C)
      convert h using 1
      ring

end CircularLaw
