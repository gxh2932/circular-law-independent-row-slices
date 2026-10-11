import CircularLaw.NormHeavyLargeRatio

/-!
# The small-mass heavy case

The fourth-power constraint and the small level mass bound the mass
times the edge ratio by one. The remaining reciprocal scale ratios
sum geometrically. This uses the complete base-zero partition and
its right-vector mass budget, with no discrepancy estimate assumed.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem real_le_of_fourth_power_le {r t : ℝ} (ht : 0 ≤ t) (hFourth : r ^ 4 ≤ t ^ 4) : r ≤ t := by
  by_contra h
  have hPower := pow_lt_pow_left₀ (lt_of_not_ge h) ht (by decide : (4 : ℕ) ≠ 0)
  exact not_lt_of_ge hFourth hPower

theorem small_mass_fourth_power_product_bound {a r p : ℝ} (ha : 0 < a) (hp : 1 ≤ p)
    (hSmall : 4 * a * p ^ 2 ≤ 1) (hFourth : r ^ 4 ≤ 4 * p ^ 2 / a) : a * r ≤ 1 := by
  have hPSquare : 1 ≤ p ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hp 2
  have hScale : 1 ≤ 4 * p ^ 2 := by linarith
  have hMass : a ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hScale ha.le
    nlinarith [hSmall]
  have hMassSquare : a ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ ha.le hMass 2
  have hScaled := (le_div_iff₀ ha).mp hFourth
  have hProductFourth : (a * r) ^ 4 ≤ (1 : ℝ) ^ 4 := by
    calc
      _ = a ^ 3 * (r ^ 4 * a) := by ring
      _ ≤ a ^ 3 * (4 * p ^ 2) := mul_le_mul_of_nonneg_left hScaled (by positivity)
      _ = a ^ 2 * (4 * a * p ^ 2) := by ring
      _ ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left hSmall (sq_nonneg _)
      _ = a ^ 2 := mul_one _
      _ ≤ 1 := hMassSquare
      _ = _ := by norm_num
  exact real_le_of_fourth_power_le (by norm_num) hProductFourth

def normHeavySmallMassPair {m n : ℕ} (C N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : Prop :=
  normHeavyOrientedPair n N x y k l ∧
    (normHeavyEdgeRatio C N M x y k l) ^ 4 ≤ normHeavyEntropyArgument n x k ∧
      4 * normCoordinateMass n x k * ((2 : ℝ) ^ k) ^ 2 ≤ 1

theorem normHeavy_small_mass_cost_bound {m n : ℕ} (hn : 0 < n) (C N : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hPair : normHeavySmallMassPair C N M x y k l) :
    normCoordinateMass n x k * normHeavyScaledRatio C N M x y k l ≤
      Real.sqrt N / (2 : ℝ) ^ (k + l) := by
  have hMass := normCoordinateMass_pos hn x hk
  have hPow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hFourth := hPair.2.1
  change (normHeavyEdgeRatio C N M x y k l) ^ 4 ≤
    4 * ((2 : ℝ) ^ k) ^ 2 / normCoordinateMass n x k at hFourth
  have hProduct := small_mass_fourth_power_product_bound hMass hPow hPair.2.2 hFourth
  calc
    _ = (normCoordinateMass n x k * normHeavyEdgeRatio C N M x y k l) *
        Real.sqrt N / (2 : ℝ) ^ (k + l) := by
      unfold normHeavyScaledRatio
      ring
    _ ≤ 1 * Real.sqrt N / (2 : ℝ) ^ (k + l) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hProduct (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by rw [one_mul]

theorem normHeavy_small_mass_fixed_right_sum {m n : ℕ} (hn : 0 < n) (C N : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (P : ℕ → ℕ → Prop) (l : ℕ) :
    (∑ k ∈ normCoordinateLevels n x,
      if P k l ∧ normHeavySmallMassPair C N M x y k l then normHeavyLevelWeight C N M x y k l else 0) ≤
        2 * normCoordinateMass n y l := by
  let S := (normCoordinateLevels n x).filter (fun k => P k l ∧ normHeavySmallMassPair C N M x y k l)
  have hMass := normCoordinateMass_nonneg n y l
  have hThreshold : 0 ≤ Real.sqrt N / (2 : ℝ) ^ l := by positivity
  have hGeom := finite_dyadic_lower_ratio_sum_bound S (Real.sqrt N / (2 : ℝ) ^ l) hThreshold (by
    intro k hk
    have hHeavy := (Finset.mem_filter.mp hk).2.2.1.1
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ l)).mpr
    simpa only [pow_add] using hHeavy)
  calc
    _ = ∑ k ∈ S, normHeavyLevelWeight C N M x y k l := (Finset.sum_filter _ _).symm
    _ ≤ ∑ k ∈ S, normCoordinateMass n y l * ((Real.sqrt N / (2 : ℝ) ^ l) / (2 : ℝ) ^ k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hPoint := normHeavy_small_mass_cost_bound hn C N M x y (Finset.mem_filter.mp hk).1
        (Finset.mem_filter.mp hk).2.2
      have h := mul_le_mul_of_nonneg_left hPoint hMass
      convert h using 1
      · unfold normHeavyLevelWeight
        ring
      · rw [pow_add]
        ring
    _ = normCoordinateMass n y l * ∑ k ∈ S, (Real.sqrt N / (2 : ℝ) ^ l) / (2 : ℝ) ^ k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hGeom hMass

theorem normHeavy_small_mass_sum {m n : ℕ} (hn : 0 < n) (C N : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hy : (∑ j, (y j) ^ 2) ≤ 1) (P : ℕ → ℕ → Prop) :
    normHeavySelectedSum C N M x y (fun k l => P k l ∧ normHeavySmallMassPair C N M x y k l) ≤ 10 := by
  have hB := normCoordinateMass_sum_unit hn (by simp only [Fintype.card_fin, le_refl]) y hy
  unfold normHeavySelectedSum
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ l ∈ normCoordinateLevels n y, 2 * normCoordinateMass n y l := by
      apply Finset.sum_le_sum
      intro l _
      convert normHeavy_small_mass_fixed_right_sum hn C N M x y P l using 1
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : P k l ∧ normHeavySmallMassPair C N M x y k l
      · simp only [if_pos h]
      · simp only [if_neg h]
    _ = 2 * ∑ l ∈ normCoordinateLevels n y, normCoordinateMass n y l := (Finset.mul_sum _ _ _).symm
    _ ≤ 10 := by linarith

end CircularLaw
