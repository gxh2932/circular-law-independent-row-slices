import CircularLaw.NormLatticeCardinality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean coordinate rounding for the finite norm net

Round `8*sqrt(n)*x_i` down to an integer. The error vector has norm at
most `sqrt(n)`, so the rounded integer vector has squared mass at most
`81*n`. Dividing it by `9*sqrt(n)` gives a point in the unit ball within
distance `1/4` of the original unit-ball vector.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normRoundInteger {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : ℤ :=
  ⌊8 * Real.sqrt n * x i⌋

def normRoundReal {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (normRoundInteger x i : ℝ))

def normRoundError {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (normRoundInteger x i : ℝ) - 8 * Real.sqrt n * x i)

def normRoundPoint {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 / (9 * Real.sqrt n)) • normRoundReal x

theorem real_euclidean_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x

theorem normRoundError_coordinate_bound {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |normRoundError x i| ≤ 1 := by
  have hFloor := Int.floor_le (8 * Real.sqrt n * x i)
  have hNext := Int.lt_floor_add_one (8 * Real.sqrt n * x i)
  change |(normRoundInteger x i : ℝ) - 8 * Real.sqrt n * x i| ≤ 1
  unfold normRoundInteger
  apply abs_le.mpr
  constructor <;> linarith

theorem normRoundError_norm_bound {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖normRoundError x‖ ≤ Real.sqrt n := by
  have hMass : (∑ i, (normRoundError x i) ^ 2) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (normRoundError_coordinate_bound x i) 2
      _ = _ := by simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hNorm := real_euclidean_norm_sq (normRoundError x)
  have hRoot := Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith [norm_nonneg (normRoundError x), Real.sqrt_nonneg (n : ℝ)]

theorem normRoundReal_decomposition {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    normRoundReal x = (8 * Real.sqrt n) • x + normRoundError x := by
  apply WithLp.ofLp_injective
  funext i
  change (normRoundInteger x i : ℝ) = 8 * Real.sqrt n * x i +
    ((normRoundInteger x i : ℝ) - 8 * Real.sqrt n * x i)
  ring

theorem normRoundReal_norm_bound {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ‖normRoundReal x‖ ≤ 9 * Real.sqrt n := by
  rw [normRoundReal_decomposition]
  calc
    _ ≤ ‖(8 * Real.sqrt n) • x‖ + ‖normRoundError x‖ := norm_add_le _ _
    _ = (8 * Real.sqrt n) * ‖x‖ + ‖normRoundError x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (8 * Real.sqrt n) * 1 + Real.sqrt n :=
      add_le_add (mul_le_mul_of_nonneg_left hx (by positivity)) (normRoundError_norm_bound x)
    _ = _ := by ring

theorem normRoundInteger_squared_mass {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    (∑ i, (normRoundInteger x i : ℝ) ^ 2) ≤ 81 * (n : ℝ) := by
  have hSquare := pow_le_pow_left₀ (norm_nonneg (normRoundReal x)) (normRoundReal_norm_bound x hx) 2
  rw [real_euclidean_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hSquare
  norm_num at hSquare
  exact hSquare

theorem normRoundPoint_norm_bound {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ‖normRoundPoint x‖ ≤ 1 := by
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold normRoundPoint
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 / (9 * Real.sqrt n)) * (9 * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (normRoundReal_norm_bound x hx) (by positivity)
    _ = _ := by field_simp

theorem normRoundPoint_difference {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    x - normRoundPoint x = (1 / 9 : ℝ) • x - (1 / (9 * Real.sqrt n)) • normRoundError x := by
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  apply WithLp.ofLp_injective
  funext i
  change x i - (1 / (9 * Real.sqrt n)) * (normRoundInteger x i : ℝ) =
    (1 / 9 : ℝ) * x i - (1 / (9 * Real.sqrt n)) * ((normRoundInteger x i : ℝ) - 8 * Real.sqrt n * x i)
  field_simp [hRoot.ne']
  ring

theorem normRoundPoint_distance_bound {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ‖x - normRoundPoint x‖ ≤ 1 / 4 := by
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hFirst : ‖(1 / 9 : ℝ) • x‖ ≤ 1 / 9 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 9)]
    have h := mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 1 / 9)
    simpa only [mul_one] using h
  have hSecond : ‖(1 / (9 * Real.sqrt n)) • normRoundError x‖ ≤ 1 / 9 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (1 / (9 * Real.sqrt n)) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left (normRoundError_norm_bound x) (by positivity)
      _ = _ := by field_simp
  rw [normRoundPoint_difference hn x]
  have hTriangle := norm_sub_le ((1 / 9 : ℝ) • x) ((1 / (9 * Real.sqrt n)) • normRoundError x)
  linarith

end CircularLaw
