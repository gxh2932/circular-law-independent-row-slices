import CircularLaw.GradualClassBlocks

/-!
# Explicit alphabets in the gradual-class block count

The finite grid boxes are counted with their actual ceiling radius.
For the source discretization budget `k^2*d^3 <= n`, the bulk alphabet
has at most `25*n/d^3` values and the radius-`d^(3/2)` alphabet has at
most `49*n` values. These are the small-alphabet inputs needed for
exponential class-count absorption.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem gridBoxRadius_card_bound {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 1 ≤ R) :
    ((gridBox k (gridBoxRadius k R)).card : ℝ) ≤ 49 * (k : ℝ) ^ 2 * R ^ 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hRadius := gridBoxRadius_upper (by linarith : 0 ≤ R) (k := k)
  have hProduct : (1 : ℝ) ≤ (k : ℝ) * R := by nlinarith
  have hLinear : (2 : ℝ) * gridBoxRadius k R + 1 ≤ 7 * (k : ℝ) * R := by
    linarith
  have hSquare := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ 2 * gridBoxRadius k R + 1) hLinear 2
  have hCount : ((gridBox k (gridBoxRadius k R)).card : ℝ) ≤
      (2 * (gridBoxRadius k R : ℝ) + 1) ^ 2 := by
    exact_mod_cast gridBox_card_le k (gridBoxRadius k R)
  apply hCount.trans (hSquare.trans_eq _)
  ring

theorem gridBoxRadius_one_card_bound {k : ℕ} (hk : 0 < k) :
    (gridBox k (gridBoxRadius k 1)).card ≤ 25 * k ^ 2 := by
  have hRadius : gridBoxRadius k 1 = k + 1 := by
    simp only [gridBoxRadius, mul_one, Nat.ceil_natCast]
  apply (gridBox_card_le k (gridBoxRadius k 1)).trans
  rw [hRadius]
  calc
    _ ≤ (5 * k) ^ 2 := Nat.pow_le_pow_left (by omega : 2 * (k + 1) + 1 ≤ 5 * k) 2
    _ = _ := by ring

theorem degree_three_halves_one_le {d : ℕ} (hd : 0 < d) :
    1 ≤ Real.rpow (d : ℝ) (3 / 2) :=
  Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)

theorem gradualClassBlock_alphabets {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) :
    ((gradualClassBlockValues n d k 0).card : ℝ) ≤ 25 * (k : ℝ) ^ 2 ∧
    ((gradualClassBlockValues n d k 1).card : ℝ) ≤ 49 * (k : ℝ) ^ 2 * (d : ℝ) ^ 3 ∧
    ((gradualClassBlockValues n d k 2).card : ℝ) ≤ 49 * (k : ℝ) ^ 2 * (d : ℝ) ^ 6 ∧
    ((gradualClassBlockValues n d k 3).card : ℝ) ≤ 49 * (k : ℝ) ^ 2 * (n : ℝ) ^ 12 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · simp only [gradualClassBlockValues, gradualClassBlockRadius, ↓reduceIte]
    exact_mod_cast gridBoxRadius_one_card_bound hk
  constructor
  · simp only [gradualClassBlockValues, gradualClassBlockRadius, ↓reduceIte]
    exact (gridBoxRadius_card_bound hk (degree_three_halves_one_le hd)).trans_eq
      (by rw [degree_three_halves_sq hd])
  constructor
  · simp only [gradualClassBlockValues, gradualClassBlockRadius, ↓reduceIte]
    exact (gridBoxRadius_card_bound hk (one_le_pow₀ hdR)).trans_eq (by ring)
  · simp only [gradualClassBlockValues, gradualClassBlockRadius]
    exact (gridBoxRadius_card_bound hk (one_le_pow₀ hnR)).trans_eq (by ring)

theorem gradualClassBlock_alphabets_budget {n d k : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hk : 0 < k) (hBudget : (k : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤ n) :
    ((gradualClassBlockValues n d k 0).card : ℝ) ≤ 25 * n / (d : ℝ) ^ 3 ∧
    ((gradualClassBlockValues n d k 1).card : ℝ) ≤ 49 * n ∧
    ((gradualClassBlockValues n d k 2).card : ℝ) ≤ 49 * n * (d : ℝ) ^ 3 ∧
    ((gradualClassBlockValues n d k 3).card : ℝ) ≤ 49 * (n : ℝ) ^ 13 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hBounds := gradualClassBlock_alphabets hn hd hk
  have hK : (k : ℝ) ^ 2 ≤ (n : ℝ) / (d : ℝ) ^ 3 :=
    (le_div_iff₀ (pow_pos hdR 3)).mpr hBudget
  have hK' : (k : ℝ) ^ 2 ≤ n := by
    have hD : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hd)
    have h := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
    nlinarith
  constructor
  · apply hBounds.1.trans
    have h := mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ) ≤ 25)
    convert h using 1; ring
  constructor
  · apply hBounds.2.1.trans
    have h := mul_le_mul_of_nonneg_left hBudget (by norm_num : (0 : ℝ) ≤ 49)
    convert h using 1; ring
  constructor
  · apply hBounds.2.2.1.trans
    have h := mul_le_mul_of_nonneg_right hBudget (by positivity : (0 : ℝ) ≤ 49 * (d : ℝ) ^ 3)
    convert h using 1 <;> ring
  · apply hBounds.2.2.2.trans
    have h := mul_le_mul_of_nonneg_right hK' (by positivity : (0 : ℝ) ≤ 49 * (n : ℝ) ^ 12)
    convert h using 1 <;> ring

theorem class_scale_budget_of_range {n d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2)) :
    (k : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤ n := by
  have hDen : 0 < Real.rpow (d : ℝ) (3 / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have h := (le_div_iff₀ hDen).mp hk
  have hSq := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (k : ℝ) * Real.rpow (d : ℝ) (3 / 2)) h 2
  simpa only [mul_pow, degree_three_halves_sq hd, Real.sq_sqrt (Nat.cast_nonneg n)] using hSq

end CircularLaw
