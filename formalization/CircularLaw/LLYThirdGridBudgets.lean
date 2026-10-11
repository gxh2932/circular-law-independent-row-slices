import CircularLaw.LLYThirdSteepNet
import CircularLaw.MeanCorrectedScalarNet
import CircularLaw.SteepNetEntropy

/-!
# Polynomial mesh and grid costs for the actual LLY third-class net

The mesh has resolution of order `d^(3/4)`. The logarithmic costs
are charged to the actual first/second/support prefix lengths, with
the separate fine scalar grid counted explicitly.
-/

noncomputable section
open Classical

namespace CircularLaw

def llyThirdNetResolution (d : ℕ) : ℕ := ⌈2 * (d : ℝ) ^ (3 / 4 : ℝ)⌉₊

def llyThirdNetError (d : ℕ) : ℝ := 1 / (d : ℝ) ^ (3 / 4 : ℝ)

def llyGridCount (k : ℕ) (R : ℝ) : ℕ := (2 * gridBoxRadius k R + 1) ^ 2

theorem llyThirdNetResolution_pos {d : ℕ} (hd : 0 < d) : 0 < llyThirdNetResolution d := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

theorem llyThirdNetResolution_upper {d : ℕ} (hd : 0 < d) :
    (llyThirdNetResolution d : ℝ) ≤ 3 * (d : ℝ) ^ (3 / 4 : ℝ) := by
  have hOne : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hCeil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ) ^ (3 / 4 : ℝ))
  change (⌈2 * (d : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ≤ _
  linarith

theorem llyThirdNetResolution_error {d : ℕ} (hd : 0 < d) :
    Real.sqrt 2 / (llyThirdNetResolution d : ℝ) ≤ llyThirdNetError d := by
  have hD : 0 < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hk : (0 : ℝ) < llyThirdNetResolution d := by exact_mod_cast llyThirdNetResolution_pos hd
  have hRoot : Real.sqrt 2 ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    norm_num [Real.sq_sqrt]
  have hCeil : 2 * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (llyThirdNetResolution d : ℝ) := Nat.le_ceil _
  unfold llyThirdNetError
  apply (le_div_iff₀ hD).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk).mpr
  convert (mul_le_mul_of_nonneg_right hRoot hD.le).trans hCeil using 1
  ring

theorem llyGridCount_pos (k : ℕ) (R : ℝ) : 0 < llyGridCount k R := by
  unfold llyGridCount
  positivity

theorem lly_grid_count_log_bound {d k : ℕ} (hd : 0 < d) {p R : ℝ}
    (hp : 0 ≤ p) (hK : (k : ℝ) ≤ 3 * (d : ℝ) ^ p) (hR : 1 ≤ R) :
    Real.log (llyGridCount k R) ≤ Real.log 121 + 2 * p * Real.log (d : ℝ) + 2 * Real.log R := by
  have hD : 1 ≤ (d : ℝ) ^ p := Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) hp
  have hRadius := gridBoxRadius_upper (k := k) (by linarith : 0 ≤ R)
  have hScaled := mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ R)
  have hSide : 2 * (gridBoxRadius k R : ℝ) + 1 ≤ 11 * (d : ℝ) ^ p * R := by nlinarith
  have hLog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (gridBoxRadius k R : ℝ) + 1) hSide
  have hDPos : 0 < (d : ℝ) ^ p := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hRPos : 0 < R := by linarith
  rw [Real.log_mul (by positivity : (11 : ℝ) * (d : ℝ) ^ p ≠ 0) hRPos.ne',
    Real.log_mul (by norm_num : (11 : ℝ) ≠ 0) hDPos.ne', Real.log_rpow (by exact_mod_cast hd : (0 : ℝ) < d)] at hLog
  have h121 : Real.log 121 = 2 * Real.log 11 := by
    rw [show (121 : ℝ) = 11 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simp only [llyGridCount, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Real.log_pow]
  rw [h121]
  nlinarith

theorem lly_third_high_grid_log {d r : ℕ} (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ)) :
    Real.log (llyGridCount (llyThirdNetResolution d)
      ((6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)) ≤
        4 * ((r : ℝ) + 2) * Real.log (d : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hdR (by norm_num)
  have hPow : 1 ≤ (6 * (d : ℝ)) ^ (r + 1) := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 6 * d)
  let R := (6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ)
  have hR : 1 ≤ R := by dsimp only [R]; nlinarith
  have hCap : R + 1 / 3 ≤ 2 * R := by linarith
  have hLogCap := Real.log_le_log (by linarith : 0 < R + 1 / 3) hCap
  have hRPos : 0 < R := by linarith
  have hDPos : 0 < (d : ℝ) ^ (3 / 4 : ℝ) := by linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRPos.ne'] at hLogCap
  have hLogR : Real.log R = ((r : ℝ) + 1) * (Real.log 6 + Real.log (d : ℝ)) +
      (3 / 4 : ℝ) * Real.log (d : ℝ) := by
    dsimp only [R]
    rw [Real.log_mul (by positivity : (6 * (d : ℝ)) ^ (r + 1) ≠ 0) hDPos.ne', Real.log_pow,
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0),
      Real.log_rpow (by exact_mod_cast hd : (0 : ℝ) < d)]
    push_cast
    ring
  rw [hLogR] at hLogCap
  have hCount := lly_grid_count_log_bound hd (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (llyThirdNetResolution_upper hd) (by linarith : 1 ≤ R + 1 / 3)
  have h484 : Real.log 121 + 2 * Real.log 2 = Real.log 484 := by
    rw [show (484 : ℝ) = 121 * 2 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hSix : Real.log 6 ≤ Real.log (d : ℝ) :=
    (Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 484)).trans hLog
  have hScaled := mul_le_mul_of_nonneg_left hSix (by positivity : 0 ≤ 2 * ((r : ℝ) + 1))
  change Real.log (llyGridCount (llyThirdNetResolution d) (R + 1 / 3)) ≤ _
  nlinarith

theorem lly_third_middle_grid_log {d : ℕ} (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ)) :
    Real.log (llyGridCount (llyThirdNetResolution d) ((d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)) ≤
      4 * Real.log (d : ℝ) := by
  have hD : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hCap : (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3 ≤ 2 * (d : ℝ) ^ (3 / 4 : ℝ) := by linarith
  have hLogCap := Real.log_le_log (by linarith : 0 < (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3) hCap
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (d : ℝ) ^ (3 / 4 : ℝ) ≠ 0),
    Real.log_rpow (by exact_mod_cast hd : (0 : ℝ) < d)] at hLogCap
  have hCount := lly_grid_count_log_bound hd (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (llyThirdNetResolution_upper hd) (by linarith : 1 ≤ (d : ℝ) ^ (3 / 4 : ℝ) + 1 / 3)
  have h484 : Real.log 121 + 2 * Real.log 2 = Real.log 484 := by
    rw [show (484 : ℝ) = 121 * 2 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  nlinarith

theorem lly_third_base_grid_log {d : ℕ} (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ)) :
    Real.log (llyGridCount (llyThirdNetResolution d) (4 / 3)) ≤ 3 * Real.log (d : ℝ) := by
  have hCount := lly_grid_count_log_bound hd (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (llyThirdNetResolution_upper hd) (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have hCap := Real.log_le_log (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (4 / 3 : ℝ) ≤ 2)
  have h484 : Real.log 121 + 2 * Real.log 2 = Real.log 484 := by
    rw [show (484 : ℝ) = 121 * 2 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hLogNonneg := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  nlinarith

theorem lly_third_scalar_grid_log {d : ℕ} (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ))
    {δ : ℝ} (hδSmall : δ ≤ 1 / 100) :
    Real.log (llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ)) ≤ 5 * Real.log (d : ℝ) := by
  have hK : ((llyThirdNetResolution d * d : ℕ) : ℝ) ≤ 3 * (d : ℝ) ^ (7 / 4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (llyThirdNetResolution_upper hd) (Nat.cast_nonneg (α := ℝ) d)
    have hPower : (d : ℝ) ^ (3 / 4 : ℝ) * d = (d : ℝ) ^ (7 / 4 : ℝ) := by
      calc
        _ = (d : ℝ) ^ (3 / 4 : ℝ) * (d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add (by exact_mod_cast hd : (0 : ℝ) < d)]; norm_num
    push_cast
    convert h using 1
    rw [mul_assoc, hPower]
  have hRadius : gridBoxRadius (llyThirdNetResolution d * d) (1 / 3 + δ) ≤
      gridBoxRadius (llyThirdNetResolution d * d) 1 := by
    unfold gridBoxRadius
    apply Nat.add_le_add_right
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left (by linarith : 1 / 3 + δ ≤ (1 : ℝ)) (Nat.cast_nonneg _)
  have hCountLe : llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ) ≤
      llyGridCount (llyThirdNetResolution d * d) 1 := by
    apply Nat.pow_le_pow_left
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hRadius) 1
  have hLogLe := Real.log_le_log (by exact_mod_cast llyGridCount_pos _ _ :
      (0 : ℝ) < llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ))
    (by exact_mod_cast hCountLe : (llyGridCount (llyThirdNetResolution d * d) (1 / 3 + δ) : ℝ) ≤
      llyGridCount (llyThirdNetResolution d * d) 1)
  have hCount := lly_grid_count_log_bound hd (by norm_num : (0 : ℝ) ≤ 7 / 4) hK (le_refl (1 : ℝ))
  have h121 : Real.log 121 ≤ Real.log (d : ℝ) :=
    (Real.log_le_log (by norm_num : (0 : ℝ) < 121) (by norm_num : (121 : ℝ) ≤ 484)).trans hLog
  have hLogNonneg := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  simp only [Real.log_one, mul_zero, add_zero] at hCount
  linarith

end CircularLaw
