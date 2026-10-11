import CircularLaw.SteepNetCardinality

/-!
# Entropy of the actual finite steep-net count

The three small-set families and the integer grid powers are bounded
before any asymptotic simplification. The constant grid combines with
the strict support cutoff to give exactly `next` base-grid factors.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem natural_power_eq_exp_log {A : ℕ} (hA : 0 < A) (k : ℕ) :
    ((A ^ k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log A) := by
  rw [Nat.cast_pow, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hA : (0 : ℝ) < A)]

theorem steepNetGridCount_pos (d : ℕ) (R : ℝ) : 0 < steepNetGridCount d R := by
  unfold steepNetGridCount
  positivity

def steepNetCountEntropy (n d next : ℕ) (cap t : ℝ) : ℝ :=
  2 * (n : ℝ) * smallSetEntropy (1 / Real.rpow (d : ℝ) (3 / 2)) +
    (n : ℝ) * smallSetEntropy t +
      (terminalSteepSize (steepStride d) (firstSteepScale n d) - 1 : ℕ) *
        Real.log (steepNetGridCount d ((n : ℝ) ^ 6 * cap)) +
          (firstSteepScale n d - 1 : ℕ) * Real.log (steepNetGridCount d (4 * (d : ℝ) * cap)) +
            (next : ℝ) * Real.log (steepNetGridCount d cap)

theorem firstSteepScale_prev_upper (n d : ℕ) :
    (firstSteepScale n d - 1 : ℕ) ≤ (n : ℝ) / Real.rpow (d : ℝ) (3 / 2) := by
  have hRatio : 0 ≤ (n : ℝ) / Real.rpow (d : ℝ) (3 / 2) :=
    div_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  by_cases hn1 : firstSteepScale n d = 0
  · simp only [hn1, Nat.zero_sub, Nat.cast_zero]
    exact hRatio
  · have hCeil := Nat.ceil_lt_add_one hRatio
    rw [Nat.cast_sub (by omega : 1 ≤ firstSteepScale n d), Nat.cast_one]
    change (⌈(n : ℝ) / Real.rpow (d : ℝ) (3 / 2)⌉₊ : ℝ) - 1 ≤ _
    linarith

theorem steep_net_count_entropy_bound {n d next : ℕ} {cap t : ℝ}
    (hd : 0 < d) (hp : 1 ≤ steepStride d) (hn1 : 0 < firstSteepScale n d)
    (hNext : 0 < next) (ht : 0 < t) (htOne : t ≤ 1) (hSize : (next - 1 : ℕ) ≤ t * n) :
    ((steepNetCountBound n d next cap * steepNetGridCount d cap : ℕ) : ℝ) ≤
      Real.exp (steepNetCountEntropy n d next cap t) := by
  let h := terminalSteepSize (steepStride d) (firstSteepScale n d) - 1
  let m := firstSteepScale n d - 1
  let s := next - 1
  let A := steepNetGridCount d ((n : ℝ) ^ 6 * cap)
  let B := steepNetGridCount d (4 * (d : ℝ) * cap)
  let D := steepNetGridCount d cap
  let q := 1 / Real.rpow (d : ℝ) (3 / 2)
  have hQ : 0 < q := div_pos zero_lt_one (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  have hQOne : q ≤ 1 := by
    apply (div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)).mpr
    exact Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hM : (m : ℝ) ≤ q * n := by
    convert firstSteepScale_prev_upper n d using 1
    dsimp only [q, m]
    ring
  have hHM : h ≤ m := Nat.sub_le_sub_right (terminalSteepSize_bounds hp hn1).2.1 1
  have hH : (h : ℝ) ≤ q * n := (by exact_mod_cast hHM : (h : ℝ) ≤ m).trans hM
  have hCH := smallCoordinateSets_card_density hQ hQOne hH
  have hCM := smallCoordinateSets_card_density hQ hQOne hM
  have hCS := smallCoordinateSets_card_density ht htOne hSize
  have hPower : (A ^ h * B ^ m * D ^ s * D : ℕ) = A ^ h * B ^ m * D ^ next := by
    rw [mul_assoc, ← pow_succ, show s + 1 = next by dsimp only [s]; omega]
  have hCounts :
      ((smallCoordinateSets n h).card * (smallCoordinateSets n m).card *
        (smallCoordinateSets n s).card : ℕ) ≤
          Real.exp ((n : ℝ) * smallSetEntropy q) *
            Real.exp ((n : ℝ) * smallSetEntropy q) * Real.exp ((n : ℝ) * smallSetEntropy t) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul hCH hCM (Nat.cast_nonneg _) (Real.exp_pos _).le)
      hCS (Nat.cast_nonneg _) (by positivity)
  change (((smallCoordinateSets n h).card * (smallCoordinateSets n m).card *
    (smallCoordinateSets n s).card * (A ^ h * B ^ m * D ^ s) * D : ℕ) : ℝ) ≤ _
  rw [mul_assoc, hPower, Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_right hCounts (Nat.cast_nonneg _)).trans_eq
  rw [Nat.cast_mul, Nat.cast_mul,
    natural_power_eq_exp_log (steepNetGridCount_pos _ _) h,
    natural_power_eq_exp_log (steepNetGridCount_pos _ _) m,
    natural_power_eq_exp_log (steepNetGridCount_pos _ _) next]
  simp only [← Real.exp_add]
  congr 1
  dsimp only [steepNetCountEntropy, q, h, m, A, B, D]
  ring

end CircularLaw
