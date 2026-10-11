import CircularLaw.NormDyadicLevels

/-!
# Squared mass of the complete coordinate levels

The actual level fibers regroup every coordinate exactly once. The
base level contributes at most one when the ambient dimension bounds
the number of coordinates, and all other levels cost at most four times
the squared Euclidean mass. In particular, a unit vector has total
dyadic mass at most five, including its small and zero coordinates.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem normCoordinatePart_sum {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ)
    (f : ι → ℝ) :
    (∑ k ∈ normCoordinateLevels n x, ∑ i ∈ normCoordinatePart n x k, f i) = ∑ i, f i := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun i _ => normCoordinateLevel_mem n x i) f

theorem normCoordinateMass_nonneg {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (k : ℕ) :
    0 ≤ normCoordinateMass n x k := by
  exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)) (Nat.cast_nonneg _)

theorem normCoordinateMass_pos {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (x : ι → ℝ) {k : ℕ} (hk : k ∈ normCoordinateLevels n x) :
    0 < normCoordinateMass n x k := by
  have hPart := (normCoordinatePart_nonempty_iff n x k).mpr hk
  exact mul_pos (div_pos (sq_pos_of_pos (pow_pos (by norm_num) _))
    (by exact_mod_cast hn)) (by exact_mod_cast hPart.card_pos)

theorem normCoordinateMass_sum {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) :
    (∑ k ∈ normCoordinateLevels n x, normCoordinateMass n x k) =
      ∑ i, ((2 : ℝ) ^ normCoordinateLevel n x i) ^ 2 / n := by
  calc
    _ = ∑ k ∈ normCoordinateLevels n x,
        ∑ _i ∈ normCoordinatePart n x k, ((2 : ℝ) ^ k) ^ 2 / n := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [normCoordinateMass, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = _ := Finset.sum_fiberwise_of_maps_to'
      (fun i _ => normCoordinateLevel_mem n x i) (fun k => ((2 : ℝ) ^ k) ^ 2 / n)

theorem normCoordinate_scaled_square_bound {ι : Type*} {n : ℕ} (hn : 0 < n)
    (x : ι → ℝ) (i : ι) :
    ((2 : ℝ) ^ normCoordinateLevel n x i) ^ 2 / n ≤ 1 / n + 4 * (x i) ^ 2 := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hZero : normCoordinateLevel n x i = 0
  · simp only [hZero, pow_zero, one_pow]
    nlinarith [sq_nonneg (x i)]
  · have hIndex : 0 < dyadicCeilIndex (Real.sqrt n * |x i|) := by
      change 0 < normCoordinateLevel n x i
      omega
    have hScale := dyadicCeilIndex_scale_le_twice hIndex
    have hScaleNonneg : 0 ≤ (2 : ℝ) ^ normCoordinateLevel n x i := by positivity
    have hUpperNonneg : 0 ≤ 2 * (Real.sqrt n * |x i|) := by positivity
    have hSquare := (sq_le_sq₀ hScaleNonneg hUpperNonneg).mpr hScale
    have hUpperSquare : (2 * (Real.sqrt n * |x i|)) ^ 2 = 4 * (n : ℝ) * (x i) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hnReal.le, sq_abs]
      ring
    rw [hUpperSquare] at hSquare
    have hBound : ((2 : ℝ) ^ normCoordinateLevel n x i) ^ 2 / n ≤ 4 * (x i) ^ 2 :=
      (div_le_iff₀ hnReal).mpr (by nlinarith [hSquare])
    exact hBound.trans (le_add_of_nonneg_left (by positivity))

theorem normCoordinateMass_sum_bound {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (hCard : Fintype.card ι ≤ n) (x : ι → ℝ) :
    (∑ k ∈ normCoordinateLevels n x, normCoordinateMass n x k) ≤ 1 + 4 * ∑ i, (x i) ^ 2 := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hCardReal : (Fintype.card ι : ℝ) ≤ n := by exact_mod_cast hCard
  rw [normCoordinateMass_sum]
  calc
    _ ≤ ∑ i, (1 / (n : ℝ) + 4 * (x i) ^ 2) :=
      Finset.sum_le_sum (fun i _ => normCoordinate_scaled_square_bound hn x i)
    _ = (Fintype.card ι : ℝ) / n + 4 * ∑ i, (x i) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := add_le_add ((div_le_one hnReal).mpr hCardReal) le_rfl

theorem normCoordinateMass_sum_unit {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (hCard : Fintype.card ι ≤ n) (x : ι → ℝ) (hUnit : (∑ i, (x i) ^ 2) ≤ 1) :
    (∑ k ∈ normCoordinateLevels n x, normCoordinateMass n x k) ≤ 5 := by
  have hBound := normCoordinateMass_sum_bound hn hCard x
  linarith

end CircularLaw
