import CircularLaw.NormHeavyDegreeSums

/-!
# The literal discrepancy bound on normalized heavy costs

The larger coordinate fiber gives the entropy term. The logarithm's
argument is expressed in the actual dyadic mass, with the factor four
absorbing `exp(1)`. A fourth-power condition then bounds its ratio to
the edge-ratio logarithm without a fractional-power assumption.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normHeavyEntropyArgument {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (k : ℕ) : ℝ :=
  4 * ((2 : ℝ) ^ k) ^ 2 / normCoordinateMass n x k

def normHeavyOrientedPair {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ) (N : ℝ)
    (x : ι → ℝ) (y : κ → ℝ) (k l : ℕ) : Prop :=
  Real.sqrt N ≤ (2 : ℝ) ^ (k + l) ∧ (normCoordinatePart n y l).card ≤ (normCoordinatePart n x k).card

theorem normHeavyEntropyArgument_pos {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (x : ι → ℝ) {k : ℕ} (hk : k ∈ normCoordinateLevels n x) :
    0 < normHeavyEntropyArgument n x k :=
  div_pos (by positivity) (normCoordinateMass_pos hn x hk)

theorem normHeavyEntropyArgument_eq_card {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (x : ι → ℝ) {k : ℕ} (hk : k ∈ normCoordinateLevels n x) :
    normHeavyEntropyArgument n x k = 4 * (n : ℝ) / (normCoordinatePart n x k).card := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < (normCoordinatePart n x k).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n x k).mpr hk).card_pos
  unfold normHeavyEntropyArgument normCoordinateMass
  field_simp [hnReal.ne', hS.ne']

theorem normHeavy_scaled_cost_edge_identity {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l =
      ((2 : ℝ) ^ l / (C * Real.sqrt N * (2 : ℝ) ^ k * (normCoordinatePart n x k).card)) *
        matrixEdgeCount M (normCoordinatePart n x k) (normCoordinatePart n y l) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < (normCoordinatePart n x k).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n x k).mpr hk).card_pos
  have hT : (0 : ℝ) < (normCoordinatePart n y l).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n y l).mpr hl).card_pos
  have hRoot := Real.sqrt_pos.mpr hN
  unfold normHeavyScaledRatio normHeavyEdgeRatio normCoordinateMass
  rw [pow_add]
  field_simp [hnReal.ne', hC.ne', hN.ne', hS.ne', hT.ne', hRoot.ne']
  ring_nf
  rw [Real.sq_sqrt hN.le]
  ring

theorem normHeavy_scaled_ratio_le_edge_ratio {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y)
    (hHeavy : Real.sqrt N ≤ (2 : ℝ) ^ (k + l)) :
    normHeavyScaledRatio C N M x y k l ≤ normHeavyEdgeRatio C N M x y k l := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + l))).mpr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hHeavy
    (normHeavyEdgeRatio_nonneg hn hC hN M hM x y hk hl)

theorem normHeavy_discrepancy_log_bound {m n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hKappa : 0 ≤ kappa₂) (M : Matrix (Fin m) (Fin n) ℝ)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y)
    (hSizes : (normCoordinatePart n y l).card ≤ (normCoordinatePart n x k).card)
    (hLarge : cap < normHeavyEdgeRatio C N M x y k l) :
    (normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l) *
        Real.log (normHeavyEdgeRatio C N M x y k l) ≤
      (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) *
        Real.log (normHeavyEntropyArgument n x k) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < (normCoordinatePart n x k).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n x k).mpr hk).card_pos
  have hRoot := Real.sqrt_pos.mpr hN
  have hD := hDP (normCoordinatePart n x k) (normCoordinatePart n y l)
    ((normCoordinatePart_nonempty_iff n x k).mpr hk) ((normCoordinatePart_nonempty_iff n y l).mpr hl)
  have hSecond := hD.resolve_left (not_le.mpr hLarge)
  rw [max_eq_left hSizes] at hSecond
  change matrixEdgeCount M (normCoordinatePart n x k) (normCoordinatePart n y l) *
      Real.log (normHeavyEdgeRatio C N M x y k l) ≤
    kappa₂ * ((normCoordinatePart n x k).card *
      Real.log (Real.exp 1 * (n : ℝ) / (normCoordinatePart n x k).card)) at hSecond
  have hCoeff : 0 ≤ (2 : ℝ) ^ l /
      (C * Real.sqrt N * (2 : ℝ) ^ k * (normCoordinatePart n x k).card) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hSecond hCoeff
  have hRightIdentity : ((2 : ℝ) ^ l /
      (C * Real.sqrt N * (2 : ℝ) ^ k * (normCoordinatePart n x k).card)) *
      (kappa₂ * ((normCoordinatePart n x k).card *
        Real.log (Real.exp 1 * (n : ℝ) / (normCoordinatePart n x k).card))) =
      (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) *
        Real.log (Real.exp 1 * (n : ℝ) / (normCoordinatePart n x k).card) := by
    field_simp [hC.ne', hRoot.ne', hS.ne']
  have hLog : Real.log (Real.exp 1 * (n : ℝ) / (normCoordinatePart n x k).card) ≤
      Real.log (normHeavyEntropyArgument n x k) := by
    rw [normHeavyEntropyArgument_eq_card hn x hk]
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_one_lt_three.le.trans (by norm_num)) hnReal.le) hS.le
  calc
    _ = ((2 : ℝ) ^ l / (C * Real.sqrt N * (2 : ℝ) ^ k * (normCoordinatePart n x k).card)) *
        (matrixEdgeCount M (normCoordinatePart n x k) (normCoordinatePart n y l) *
          Real.log (normHeavyEdgeRatio C N M x y k l)) := by
      rw [normHeavy_scaled_cost_edge_identity hn hC hN M x y hk hl]
      ring
    _ ≤ _ := hScaled
    _ = _ := hRightIdentity
    _ ≤ _ := mul_le_mul_of_nonneg_left hLog (by positivity)

theorem real_log_fourth_power_comparison {q r : ℝ} (hq : 0 < q) (hFourth : q ≤ r ^ 4) :
    Real.log q ≤ 4 * Real.log r := by
  have h := Real.log_le_log hq hFourth
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

end CircularLaw
