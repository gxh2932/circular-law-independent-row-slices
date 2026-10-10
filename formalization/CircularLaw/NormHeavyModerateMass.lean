import CircularLaw.NormHeavySmallMass

/-!
# The moderate-mass heavy case

The inverse-mass condition bounds the entropy logarithm by four times
the coordinate scale. The edge-ratio fourth-power condition restricts
the other scale to a geometric window. The actual discrepancy bound
then supplies the fourth-case budget.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem fourth_power_inverse_mass_bound {a r p : ℝ} (hp : 0 ≤ p)
    (hInv : 1 / a ≤ 4 * p ^ 2) (hFourth : r ^ 4 ≤ 4 * p ^ 2 / a) : r ≤ 2 * p := by
  apply real_le_of_fourth_power_le (by positivity)
  calc
    _ ≤ 4 * p ^ 2 / a := hFourth
    _ = 4 * p ^ 2 * (1 / a) := by ring
    _ ≤ 4 * p ^ 2 * (4 * p ^ 2) := mul_le_mul_of_nonneg_left hInv (by positivity)
    _ = _ := by ring

theorem normHeavyEntropyArgument_log_scale_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 0 < n) (x : ι → ℝ) {k : ℕ} (hk : k ∈ normCoordinateLevels n x)
    (hInv : 1 / normCoordinateMass n x k ≤ 4 * ((2 : ℝ) ^ k) ^ 2) :
    Real.log (normHeavyEntropyArgument n x k) ≤ 4 * (2 : ℝ) ^ k := by
  have hArgument : normHeavyEntropyArgument n x k ≤ ((2 : ℝ) ^ (k + 1)) ^ 4 := by
    calc
      _ = 4 * ((2 : ℝ) ^ k) ^ 2 * (1 / normCoordinateMass n x k) := by
        unfold normHeavyEntropyArgument
        ring
      _ ≤ 4 * ((2 : ℝ) ^ k) ^ 2 * (4 * ((2 : ℝ) ^ k) ^ 2) :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hLog := Real.log_le_log (normHeavyEntropyArgument_pos hn x hk) hArgument
  rw [Real.log_pow, Real.log_pow] at hLog
  have hLogTwo : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hCount : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k)))
  have hProduct := mul_le_mul_of_nonneg_left hLogTwo (by positivity : (0 : ℝ) ≤ 4 * ((k + 1 : ℕ) : ℝ))
  norm_num at hLog
  norm_num at hCount hProduct
  nlinarith [hProduct]

def normHeavyModerateMassPair {m n : ℕ} (C N cap : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : Prop :=
  normHeavyOrientedPair n N x y k l ∧ cap < normHeavyScaledRatio C N M x y k l ∧
    (normHeavyEdgeRatio C N M x y k l) ^ 4 ≤ normHeavyEntropyArgument n x k ∧
      1 / normCoordinateMass n x k ≤ 4 * ((2 : ℝ) ^ k) ^ 2

theorem normHeavy_moderate_mass_level_bound {m n : ℕ} {N cap : ℝ} (hN : 0 < N) (hCap : 1 < cap)
    (C : ℝ) (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hPair : normHeavyModerateMassPair C N cap M x y k l) :
    (2 : ℝ) ^ l / Real.sqrt N ≤ 2 / cap := by
  have hRoot := Real.sqrt_pos.mpr hN
  have hCapPos : 0 < cap := lt_trans (by norm_num) hCap
  have hRatioBound := fourth_power_inverse_mass_bound (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
    hPair.2.2.2 hPair.2.2.1
  have hScaledBound : normHeavyScaledRatio C N M x y k l ≤ 2 * Real.sqrt N / (2 : ℝ) ^ l := by
    calc
      _ ≤ Real.sqrt N * (2 * (2 : ℝ) ^ k) / (2 : ℝ) ^ (k + l) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRatioBound (Real.sqrt_nonneg _)) (by positivity)
      _ = _ := by rw [pow_add]; field_simp
  have hLarge := hPair.2.1.trans_le hScaledBound
  have hProduct := (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ l)).mp hLarge
  apply (div_le_div_iff₀ hRoot hCapPos).mpr
  simpa only [mul_comm] using hProduct.le

theorem normHeavy_moderate_mass_cost_bound {m n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y)
    (hPair : normHeavyModerateMassPair C N cap M x y k l) :
    normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l ≤
      (4 * kappa₂ / (C * Real.log cap)) * ((2 : ℝ) ^ l / Real.sqrt N) := by
  have hRatio := normHeavy_scaled_ratio_le_edge_ratio hn hC hN M hM x y hk hl hPair.1.1
  have hLarge := hPair.2.1.trans_le hRatio
  have hCapPos : 0 < cap := lt_trans (by norm_num) hCap
  have hLogCap := Real.log_pos hCap
  have hLogRatio := Real.log_le_log hCapPos hLarge.le
  have hWeight : 0 ≤ normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l :=
    mul_nonneg (normCoordinateMass_nonneg n y l) (normHeavyScaledRatio_nonneg hn hC hN M hM x y hk hl)
  have hEntropy := normHeavy_discrepancy_log_bound hn hC hN hKappa M hDP x y hk hl hPair.1.2 hLarge
  have hLogScale := normHeavyEntropyArgument_log_scale_bound hn x hk hPair.2.2.2
  apply (mul_le_mul_iff_left₀ hLogCap).mp
  calc
    _ ≤ (normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l) *
        Real.log (normHeavyEdgeRatio C N M x y k l) := mul_le_mul_of_nonneg_left hLogRatio hWeight
    _ ≤ (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) *
        Real.log (normHeavyEntropyArgument n x k) := hEntropy
    _ ≤ (kappa₂ / C) * ((2 : ℝ) ^ l / (Real.sqrt N * (2 : ℝ) ^ k)) * (4 * (2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hLogScale (by positivity)
    _ = ((4 * kappa₂ / (C * Real.log cap)) * ((2 : ℝ) ^ l / Real.sqrt N)) * Real.log cap := by
      field_simp [hLogCap.ne']

theorem normHeavy_moderate_mass_fixed_left_sum {m n : ℕ} (hn : 0 < n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (P : ℕ → ℕ → Prop) {k : ℕ}
    (hk : k ∈ normCoordinateLevels n x) :
    (∑ l ∈ normCoordinateLevels n y,
      if P k l ∧ normHeavyModerateMassPair C N cap M x y k l then normHeavyLevelWeight C N M x y k l else 0) ≤
        (16 * kappa₂ / (C * cap * Real.log cap)) * normCoordinateMass n x k := by
  let T := (normCoordinateLevels n y).filter (fun l => P k l ∧ normHeavyModerateMassPair C N cap M x y k l)
  have hRoot := Real.sqrt_pos.mpr hN
  have hCapPos : 0 < cap := lt_trans (by norm_num) hCap
  have hLogCap := Real.log_pos hCap
  have hMass := normCoordinateMass_nonneg n x k
  have hGeom := finite_dyadic_power_sum_bound T ((2 / cap) * Real.sqrt N) (by positivity) (by
    intro l hl
    have h := normHeavy_moderate_mass_level_bound hN hCap C M x y (Finset.mem_filter.mp hl).2.2
    exact (div_le_iff₀ hRoot).mp h)
  have hGeomRatio : (∑ l ∈ T, (2 : ℝ) ^ l / Real.sqrt N) ≤ 4 / cap := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hRoot).mpr
    calc
      _ ≤ 2 * ((2 / cap) * Real.sqrt N) := hGeom
      _ = _ := by ring
  calc
    _ = ∑ l ∈ T, normHeavyLevelWeight C N M x y k l := (Finset.sum_filter _ _).symm
    _ ≤ ∑ l ∈ T, (normCoordinateMass n x k * (4 * kappa₂ / (C * Real.log cap))) *
        ((2 : ℝ) ^ l / Real.sqrt N) := by
      apply Finset.sum_le_sum
      intro l hl
      have hPoint := normHeavy_moderate_mass_cost_bound hn hC hN hCap hKappa M hM hDP x y hk
        (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hl).2.2
      have h := mul_le_mul_of_nonneg_left hPoint hMass
      simpa only [normHeavyLevelWeight, mul_assoc] using h
    _ = (normCoordinateMass n x k * (4 * kappa₂ / (C * Real.log cap))) *
        ∑ l ∈ T, (2 : ℝ) ^ l / Real.sqrt N := (Finset.mul_sum _ _ _).symm
    _ ≤ (normCoordinateMass n x k * (4 * kappa₂ / (C * Real.log cap))) * (4 / cap) :=
      mul_le_mul_of_nonneg_left hGeomRatio (by positivity)
    _ = _ := by ring

theorem normHeavy_moderate_mass_sum {m n : ℕ} (hn : 0 < n) (hm : m ≤ n) {C N cap kappa₂ : ℝ}
    (hC : 0 < C) (hN : 0 < N) (hCap : 1 < cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy (C * N / n) cap kappa₂ M)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : (∑ i, (x i) ^ 2) ≤ 1) (P : ℕ → ℕ → Prop) :
    normHeavySelectedSum C N M x y (fun k l => P k l ∧ normHeavyModerateMassPair C N cap M x y k l) ≤
      80 * kappa₂ / (C * cap * Real.log cap) := by
  have hA := normCoordinateMass_sum_unit hn (by simpa only [Fintype.card_fin] using hm) x hx
  have hCapPos : 0 < cap := lt_trans (by norm_num) hCap
  have hLogCap := Real.log_pos hCap
  unfold normHeavySelectedSum
  calc
    _ ≤ ∑ k ∈ normCoordinateLevels n x, (16 * kappa₂ / (C * cap * Real.log cap)) * normCoordinateMass n x k := by
      apply Finset.sum_le_sum
      intro k hk
      convert normHeavy_moderate_mass_fixed_left_sum hn hC hN hCap hKappa M hM hDP x y P hk using 1
      apply Finset.sum_congr rfl
      intro l _
      by_cases h : P k l ∧ normHeavyModerateMassPair C N cap M x y k l
      · simp only [if_pos h]
      · simp only [if_neg h]
    _ = (16 * kappa₂ / (C * cap * Real.log cap)) * ∑ k ∈ normCoordinateLevels n x, normCoordinateMass n x k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 80 * kappa₂ / (C * cap * Real.log cap) := by
      have h := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 16 * kappa₂ / (C * cap * Real.log cap))
      convert h using 1
      ring

end CircularLaw
