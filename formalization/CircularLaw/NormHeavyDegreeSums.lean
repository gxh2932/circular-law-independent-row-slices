import CircularLaw.NormHeavyLevelRatios

/-!
# The small-ratio and degree-bound heavy cases

The selected costs are the literal normalized matrix level costs.
Their bounds use the checked mass budget and geometric sums; no
unproved heavy-term estimate is supplied as an input.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normHeavySelectedSum {m n : ℕ} (C N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (P : ℕ → ℕ → Prop) : ℝ :=
  ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
    if P k l then normHeavyLevelWeight C N M x y k l else 0

theorem finite_mass_product_sum_bound {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (hb : ∀ j ∈ T, 0 ≤ b j)
    (hA : (∑ i ∈ S, a i) ≤ 5) (hB : (∑ j ∈ T, b j) ≤ 5)
    {cap : ℝ} (hCap : 0 ≤ cap) : (∑ i ∈ S, ∑ j ∈ T, cap * a i * b j) ≤ 25 * cap := by
  have hSumB : 0 ≤ ∑ j ∈ T, b j := Finset.sum_nonneg hb
  have hProduct : (∑ i ∈ S, a i) * (∑ j ∈ T, b j) ≤ 25 := by
    have h := mul_le_mul hA hB hSumB (by norm_num : (0 : ℝ) ≤ 5)
    norm_num at h
    exact h
  calc
    _ = cap * ((∑ i ∈ S, a i) * ∑ j ∈ T, b j) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hProduct hCap

theorem normHeavy_small_scaled_sum {m n : ℕ} (hn : 0 < n) (hm : m ≤ n)
    (C N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : (∑ i, (x i) ^ 2) ≤ 1) (hy : (∑ j, (y j) ^ 2) ≤ 1)
    {cap : ℝ} (hCap : 0 ≤ cap) (P : ℕ → ℕ → Prop) :
    normHeavySelectedSum C N M x y (fun k l => P k l ∧ normHeavyScaledRatio C N M x y k l ≤ cap) ≤
      25 * cap := by
  have hA := normCoordinateMass_sum_unit hn (by simpa only [Fintype.card_fin] using hm) x hx
  have hB := normCoordinateMass_sum_unit hn (by simp only [Fintype.card_fin, le_refl]) y hy
  apply le_trans (b := ∑ k ∈ normCoordinateLevels n x, ∑ l ∈ normCoordinateLevels n y,
    cap * normCoordinateMass n x k * normCoordinateMass n y l)
  · apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro l _
    by_cases h : P k l ∧ normHeavyScaledRatio C N M x y k l ≤ cap
    · rw [if_pos h]
      unfold normHeavyLevelWeight
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left h.2
          (mul_nonneg (normCoordinateMass_nonneg n x k) (normCoordinateMass_nonneg n y l))
    · rw [if_neg h]
      exact mul_nonneg (mul_nonneg hCap (normCoordinateMass_nonneg n x k)) (normCoordinateMass_nonneg n y l)
  · exact finite_mass_product_sum_bound _ _ _ _
      (fun l _ => normCoordinateMass_nonneg n y l) hA hB hCap

theorem normHeavyLevelWeight_degree_bound {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hColumn : ∀ j, (∑ i, M i j) ≤ N)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    normHeavyLevelWeight C N M x y k l ≤
      (normCoordinateMass n y l / C) * ((2 : ℝ) ^ k / ((2 : ℝ) ^ l / Real.sqrt N)) := by
  have hA := normCoordinateMass_pos hn x hk
  have hB := normCoordinateMass_nonneg n y l
  have hRoot := Real.sqrt_pos.mpr hN
  have hDegree := normHeavyEdgeRatio_column_bound hn hC hN M hM hColumn x y hk hl
  have hMultiplier : 0 ≤ normCoordinateMass n x k * normCoordinateMass n y l * Real.sqrt N /
      (2 : ℝ) ^ (k + l) := by positivity
  calc
    _ = (normCoordinateMass n x k * normCoordinateMass n y l * Real.sqrt N /
        (2 : ℝ) ^ (k + l)) * normHeavyEdgeRatio C N M x y k l := by
      unfold normHeavyLevelWeight normHeavyScaledRatio
      ring
    _ ≤ (normCoordinateMass n x k * normCoordinateMass n y l * Real.sqrt N /
        (2 : ℝ) ^ (k + l)) * (((2 : ℝ) ^ k) ^ 2 / (C * normCoordinateMass n x k)) :=
      mul_le_mul_of_nonneg_left hDegree hMultiplier
    _ = _ := by
      rw [pow_add]
      field_simp [hC.ne', hA.ne', hRoot.ne']

theorem normHeavy_degree_fixed_right_sum {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hColumn : ∀ j, (∑ i, M i j) ≤ N)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (P : ℕ → ℕ → Prop) {l : ℕ}
    (hl : l ∈ normCoordinateLevels n y) :
    (∑ k ∈ normCoordinateLevels n x,
      if P k l ∧ (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N then normHeavyLevelWeight C N M x y k l else 0) ≤
        2 * (normCoordinateMass n y l / C) := by
  let S := (normCoordinateLevels n x).filter (fun k => P k l ∧ (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N)
  have hThreshold : 0 < (2 : ℝ) ^ l / Real.sqrt N := div_pos (by positivity) (Real.sqrt_pos.mpr hN)
  have hGeom := finite_dyadic_power_ratio_sum_bound S hThreshold
    (fun k hk => (Finset.mem_filter.mp hk).2.2)
  calc
    _ = ∑ k ∈ S, normHeavyLevelWeight C N M x y k l := (Finset.sum_filter _ _).symm
    _ ≤ ∑ k ∈ S, (normCoordinateMass n y l / C) * ((2 : ℝ) ^ k / ((2 : ℝ) ^ l / Real.sqrt N)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact normHeavyLevelWeight_degree_bound hn hC hN M hM hColumn x y (Finset.mem_filter.mp hk).1 hl
    _ = (normCoordinateMass n y l / C) * ∑ k ∈ S, (2 : ℝ) ^ k / ((2 : ℝ) ^ l / Real.sqrt N) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hGeom
        (div_nonneg (normCoordinateMass_nonneg n y l) hC.le)

theorem normHeavy_degree_sum {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hColumn : ∀ j, (∑ i, M i j) ≤ N)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hy : (∑ j, (y j) ^ 2) ≤ 1) (P : ℕ → ℕ → Prop) :
    normHeavySelectedSum C N M x y (fun k l => P k l ∧ (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N) ≤
      10 / C := by
  classical
  have hB := normCoordinateMass_sum_unit hn (by simp only [Fintype.card_fin, le_refl]) y hy
  unfold normHeavySelectedSum
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ l ∈ normCoordinateLevels n y, 2 * (normCoordinateMass n y l / C) := by
      apply Finset.sum_le_sum
      intro l hl
      convert normHeavy_degree_fixed_right_sum hn hC hN M hM hColumn x y P hl using 1
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : P k l ∧ (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l / Real.sqrt N
      · simp only [if_pos h]
      · simp only [if_neg h]
    _ = (2 / C) * ∑ l ∈ normCoordinateLevels n y, normCoordinateMass n y l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ 10 / C := by
      have h := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 / C)
      convert h using 1
      ring

end CircularLaw
