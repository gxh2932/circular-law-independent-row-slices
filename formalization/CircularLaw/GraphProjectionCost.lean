import CircularLaw.GraphProjectionThreshold

/-!
# Polynomial logarithmic cost of graph projection thresholds

The exact scalar cost is bounded by a fifth power of the seed logarithm
and degree logarithm. In the exposure range, the global remaining size
is at most nine times the local kernel dimension. The source eighth
powers dominate the cost with a fixed constant depending on beta and
the graph-growth constant.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceGraphProjectionConstant (C β : ℝ) : ℝ :=
  64 * (C + 1) * (22 - Real.log β) ^ 5

def sourceGraphProjectionExponent (C β n d g : ℝ) : ℝ :=
  sourceGraphProjectionConstant C β * Real.log d ^ 8 * Real.log (n / g) ^ 8

theorem subspace_spread_coordinate_count_le_dimension {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) :
    subspaceSpreadCoordinateCount V ≤ Module.finrank ℂ V := by
  unfold subspaceSpreadCoordinateCount
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ V)]

theorem subspace_spread_coordinate_count_lower {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) :
    (Module.finrank ℂ V : ℝ) / 4096 ≤ (subspaceSpreadCoordinateCount V : ℝ) :=
  Nat.le_ceil _

theorem graph_subspace_seed_log_pos {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {n : ℝ} (hn : 4 ≤ n) (hAmbient : (m : ℝ) ≤ n) :
    0 < Real.log (n / subspaceSpreadCoordinateCount V) := by
  have hk : 0 < (subspaceSpreadCoordinateCount V : ℝ) := by
    exact_mod_cast subspace_spread_coordinate_count_pos V hV
  have hDim : (Module.finrank ℂ V : ℝ) ≤ n := by
    have hLe : Module.finrank ℂ V ≤ m := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using V.finrank_le
    exact (by exact_mod_cast hLe : (Module.finrank ℂ V : ℝ) ≤ m).trans hAmbient
  have hCeil : (subspaceSpreadCoordinateCount V : ℝ) <
      (Module.finrank ℂ V : ℝ) / 4096 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hHalf : 2 * (subspaceSpreadCoordinateCount V : ℝ) ≤ n := by linarith
  apply Real.log_pos
  apply (lt_div_iff₀ hk).mpr
  linarith

set_option maxHeartbeats 1500000 in
theorem graph_projection_log_cost_le_envelope {C β n d h m : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 0 < d)
    (hk : 0 < k) (hh : 0 < h) (hm : 0 < m) (hKH : (k : ℝ) ≤ h) (hMN : m ≤ n)
    (hD : 0 ≤ Real.log d) (hL : 0 ≤ Real.log (n / k)) :
    graphProjectionLogCost C β n d k h m ≤
      64 * (C + 1) * (1 + Real.log d - Real.log β + Real.log (n / k)) ^ 5 := by
  let L := Real.log (n / k)
  let D := Real.log d
  let B := -Real.log β
  let W := 1 + D + B + L
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hB : 0 ≤ B := neg_nonneg.mpr (Real.log_nonpos hβ.le hβOne)
  have hW : 1 ≤ W := by dsimp [W, D, L]; linarith
  have hLW : L ≤ W := by dsimp [W, D]; linarith
  have hBW : B ≤ W := by dsimp [W, D, L]; linarith
  have hLogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLog8192 : Real.log 8192 ≤ 13 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hRatio : m / h ≤ n / k := by
    apply (div_le_div_iff₀ hh hkReal).mpr
    exact (mul_le_mul_of_nonneg_right hMN hkReal.le).trans
      (mul_le_mul_of_nonneg_left hKH hn.le)
  have hLogMH : Real.log (m / h) ≤ L := Real.log_le_log (div_pos hm hh) hRatio
  have hLogHead : Real.log (8192 * m / h) ≤ 13 + L := by
    rw [show 8192 * m / h = 8192 * (m / h) by ring,
      Real.log_mul (by norm_num) (div_pos hm hh).ne']
    linarith
  have hLogOne : Real.log (1 + L) ≤ L := by
    have h := Real.log_le_sub_one_of_pos (by dsimp [L]; linarith : 0 < 1 + L)
    linarith
  have hBase : Real.log (8192 * m / h) + Real.log (1 + L) - Real.log β ≤ 16 * W := by
    have h13 : 13 ≤ 13 * W := by linarith
    dsimp [B] at hBW
    linarith
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW
  have hLPow : L ^ 4 ≤ W ^ 4 := pow_le_pow_left₀ hL hLW 4
  have hSteps : (sourceGraphIterationSteps C n k : ℝ) ≤ (4 * C + 2) * W ^ 4 := by
    have hCeil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * C * L ^ 4)
    have hSeed : (sourceGraphIterationSteps C n k : ℝ) ≤ 4 * C * L ^ 4 + 2 := by
      unfold sourceGraphIterationSteps
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp [L] at hCeil
      linarith
    calc
      _ ≤ 4 * C * L ^ 4 + 2 := hSeed
      _ ≤ 4 * C * W ^ 4 + 2 * W ^ 4 := add_le_add
        (mul_le_mul_of_nonneg_left hLPow (by positivity)) (by linarith)
      _ = _ := by ring
  have hLogRatio : Real.log (d * n / (β * k)) = D + B + L := by
    dsimp [D, B, L]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hd.ne' hn.ne',
      Real.log_mul hβ.ne' hkReal.ne', Real.log_div hn.ne' hkReal.ne']
    ring
  have hPart : 7 * (sourceGraphIterationSteps C n k : ℝ) * (D + B + L) ≤
      (28 * C + 14) * W ^ 5 := by
    have h0 : 0 ≤ D + B + L := by dsimp [D, L]; linarith
    have hLe : D + B + L ≤ W := by dsimp [W]; linarith
    have h := mul_le_mul hSteps hLe h0 (by positivity : 0 ≤ (4 * C + 2) * W ^ 4)
    have hSeven := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 7)
    convert hSeven using 1 <;> ring
  have hW5 : W ≤ W ^ 5 := le_self_pow₀ hW (by decide : (5 : ℕ) ≠ 0)
  have hCost : graphProjectionLogCost C β n d k h m ≤ (28 * C + 30) * W ^ 5 := by
    unfold graphProjectionLogCost
    rw [hLogRatio]
    have hBase5 := hBase.trans (mul_le_mul_of_nonneg_left hW5 (by norm_num : (0 : ℝ) ≤ 16))
    dsimp [L] at hBase5
    linarith
  have hCoeff : 28 * C + 30 ≤ 64 * (C + 1) := by linarith
  have hFinal := hCost.trans (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0 ≤ W ^ 5))
  simpa only [W, D, B, L, sub_eq_add_neg] using hFinal

set_option maxHeartbeats 1500000 in
theorem graph_projection_log_cost_le_source_power {C β n d h m g : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 0 < d)
    (hk : 0 < k) (hh : 0 < h) (hm : 0 < m) (hKH : (k : ℝ) ≤ h) (hHM : h ≤ m) (hMN : m ≤ n)
    (hSeed : h / 4096 ≤ (k : ℝ)) (hg : 0 < g) (hGap : g ≤ 9 * h)
    (hD : 1 ≤ Real.log d) (hG : 1 ≤ Real.log (n / g))
    (hDG : Real.log d ≤ 4 * Real.log (n / g)) :
    graphProjectionLogCost C β n d k h m ≤ sourceGraphProjectionExponent C β n d g := by
  let G := Real.log (n / g)
  let B := -Real.log β
  let W := 1 + Real.log d + B + Real.log (n / k)
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hB : 0 ≤ B := neg_nonneg.mpr (Real.log_nonpos hβ.le hβOne)
  have hKN : (k : ℝ) ≤ n := hKH.trans (hHM.trans hMN)
  have hL : 0 ≤ Real.log (n / k) :=
    Real.log_nonneg ((le_div_iff₀ hkReal).mpr (by simpa using hKN))
  have hGapSeed : g ≤ 36864 * (k : ℝ) := by linarith
  have hRatio : n / k ≤ 36864 * (n / g) := by
    rw [show 36864 * (n / g) = (36864 * n) / g by ring]
    apply (div_le_div_iff₀ hkReal hg).mpr
    have h := mul_le_mul_of_nonneg_left hGapSeed hn.le
    nlinarith
  have hLogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLog36864 : Real.log 36864 ≤ 16 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 36864)
      (by norm_num : (36864 : ℝ) ≤ 2 ^ 16)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hLUpper : Real.log (n / k) ≤ 16 + G := by
    have h := Real.log_le_log (div_pos hn hkReal) hRatio
    rw [Real.log_mul (by norm_num) (div_pos hn hg).ne'] at h
    dsimp [G]
    linarith
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hEnvelope : W ≤ (22 + B) * G := by
    have hConst : 17 + B ≤ (17 + B) * G :=
      le_mul_of_one_le_right (by linarith : 0 ≤ 17 + B) hG
    dsimp [W, G] at *
    nlinarith
  have hPower := pow_le_pow_left₀ hW hEnvelope 5
  rw [mul_pow] at hPower
  have hG58 : G ^ 5 ≤ G ^ 8 := pow_le_pow_right₀ hG (by decide : (5 : ℕ) ≤ 8)
  have hD8 : 1 ≤ Real.log d ^ 8 := one_le_pow₀ hD
  have hPowers : G ^ 5 ≤ Real.log d ^ 8 * G ^ 8 := hG58.trans
    (le_mul_of_one_le_left (by positivity : 0 ≤ G ^ 8) hD8)
  have hCost := graph_projection_log_cost_le_envelope hC hβ hβOne hn hd hk hh hm hKH hMN
    (by linarith : 0 ≤ Real.log d) hL
  have hFirst := mul_le_mul_of_nonneg_left hPower (by positivity : 0 ≤ 64 * (C + 1))
  have hSecond := mul_le_mul_of_nonneg_left hPowers
    (by positivity : 0 ≤ 64 * (C + 1) * (22 + B) ^ 5)
  unfold sourceGraphProjectionExponent sourceGraphProjectionConstant
  dsimp [W, B, G] at hFirst hSecond
  nlinarith [hCost]

end CircularLaw
