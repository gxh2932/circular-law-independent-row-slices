import CircularLaw.NormDyadicSums

/-!
# Actual heavy edge ratios and normalized level costs

These quantities use the real matrix edge counts and the complete
coordinate fibers. The normalization identity and degree estimate
are checked at every pair of nonempty levels, with positive density.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normHeavyEdgeRatio {m n : ℕ} (C N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : ℝ :=
  matrixEdgeCount M (normCoordinatePart n x k) (normCoordinatePart n y l) /
    ((C * N / n) * ((normCoordinatePart n x k).card * (normCoordinatePart n y l).card))

def normHeavyScaledRatio {m n : ℕ} (C N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : ℝ :=
  Real.sqrt N * normHeavyEdgeRatio C N M x y k l / (2 : ℝ) ^ (k + l)

def normHeavyLevelWeight {m n : ℕ} (C N : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (k l : ℕ) : ℝ :=
  normCoordinateMass n x k * normCoordinateMass n y l * normHeavyScaledRatio C N M x y k l

theorem normHeavyEdgeRatio_denominator_pos {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    0 < (C * N / n) * ((normCoordinatePart n x k).card * (normCoordinatePart n y l).card : ℝ) := by
  have hS : (0 : ℝ) < (normCoordinatePart n x k).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n x k).mpr hk).card_pos
  have hT : (0 : ℝ) < (normCoordinatePart n y l).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n y l).mpr hl).card_pos
  exact mul_pos (div_pos (mul_pos hC hN) (by exact_mod_cast hn)) (mul_pos hS hT)

theorem normHeavyEdgeRatio_nonneg {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    0 ≤ normHeavyEdgeRatio C N M x y k l :=
  div_nonneg (matrixEdgeCount_nonneg M hM _ _) (normHeavyEdgeRatio_denominator_pos hn hC hN x y hk hl).le

theorem normHeavyScaledRatio_nonneg {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    0 ≤ normHeavyScaledRatio C N M x y k l :=
  div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (normHeavyEdgeRatio_nonneg hn hC hN M hM x y hk hl))
    (by positivity)

theorem normHeavyLevelWeight_nonneg {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    0 ≤ normHeavyLevelWeight C N M x y k l :=
  mul_nonneg (mul_nonneg (normCoordinateMass_nonneg n x k) (normCoordinateMass_nonneg n y l))
    (normHeavyScaledRatio_nonneg hn hC hN M hM x y hk hl)

theorem normHeavy_level_normalization {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    ((2 : ℝ) ^ (k + l) / n) * matrixEdgeCount M (normCoordinatePart n x k) (normCoordinatePart n y l) =
      C * Real.sqrt N * normHeavyLevelWeight C N M x y k l := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < (normCoordinatePart n x k).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n x k).mpr hk).card_pos
  have hT : (0 : ℝ) < (normCoordinatePart n y l).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n y l).mpr hl).card_pos
  have hPow : (2 : ℝ) ^ (k + l) ≠ 0 := by positivity
  unfold normHeavyLevelWeight normHeavyScaledRatio normHeavyEdgeRatio normCoordinateMass
  rw [pow_add]
  field_simp [hnReal.ne', hC.ne', hN.ne', hS.ne', hT.ne']
  ring_nf
  rw [Real.sq_sqrt hN.le]

theorem normHeavyEdgeRatio_column_bound {m n : ℕ} (hn : 0 < n) {C N : ℝ}
    (hC : 0 < C) (hN : 0 < N) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hColumn : ∀ j, (∑ i, M i j) ≤ N)
    (x : Fin m → ℝ) (y : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ normCoordinateLevels n x) (hl : l ∈ normCoordinateLevels n y) :
    normHeavyEdgeRatio C N M x y k l ≤ ((2 : ℝ) ^ k) ^ 2 / (C * normCoordinateMass n x k) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < (normCoordinatePart n x k).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n x k).mpr hk).card_pos
  have hT : (0 : ℝ) < (normCoordinatePart n y l).card := by
    exact_mod_cast ((normCoordinatePart_nonempty_iff n y l).mpr hl).card_pos
  have hDen := normHeavyEdgeRatio_denominator_pos hn hC hN x y hk hl
  have hEdge := matrixEdgeCount_le_columns M hM hColumn (normCoordinatePart n x k) (normCoordinatePart n y l)
  apply (div_le_iff₀ hDen).mpr
  have hProduct : (((2 : ℝ) ^ k) ^ 2 / (C * normCoordinateMass n x k)) *
      ((C * N / n) * ((normCoordinatePart n x k).card * (normCoordinatePart n y l).card : ℝ)) =
        (normCoordinatePart n y l).card * N := by
    unfold normCoordinateMass
    field_simp [hnReal.ne', hC.ne', hS.ne']
  rw [hProduct]
  exact hEdge

end CircularLaw
