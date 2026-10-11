import CircularLaw.LLYSourceGradualBudgets

/-!
# A logarithmic budget for the actual checked source radius

The denominator controls both branches of the radius, including the
first-rank-one case. Bounds on the rounded stride's logarithm then give
explicit power thresholds for the actual minimum-value event.
-/

noncomputable section
open Classical

namespace CircularLaw

def llySourceRadiusDenominator (n d : ℕ) (a : ℝ) : ℝ :=
  20 * (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) *
    ((d : ℝ) ^ (3 / 4 : ℝ)) ^ 2

theorem lly_source_radius_denominator_pos {n d : ℕ} (hd : 0 < d) (a : ℝ) :
    0 < llySourceRadiusDenominator n d a := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold llySourceRadiusDenominator
  positivity

theorem lly_source_almost_radius_reciprocal_lower {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (a : ℝ) :
    1 / llySourceRadiusDenominator n d a ≤ llySourceAlmostRadius n d a := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot := Real.sqrt_pos.mpr (by exact_mod_cast hn : (0 : ℝ) < n)
  have hD := lly_source_radius_denominator_pos (n := n) hd a
  have hQ := Real.rpow_pos_of_pos hdR (3 / 4 : ℝ)
  have hQOne := Real.one_le_rpow hdOne (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hP : 0 < (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) := by positivity
  have hPOne : (1 : ℝ) ≤ (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) :=
    one_le_pow₀ (by linarith : (1 : ℝ) ≤ 6 * d)
  have hG : (if llySourceFirstRank n d a = 1 then 1 else
      (6 * (d : ℝ)) ^ (llySourceScale n d a + 1)) ≤
        (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) := by
    split_ifs
    · exact hPOne
    · exact le_rfl
  have hGradual := lly_gradual_norm_constant_pos (r := llySourceScale n d a)
    (k₁ := llySourceFirstRank n d a) hn hd
  have hThird := lly_third_norm_constant_pos (r := llySourceScale n d a) hn hd
  unfold llySourceAlmostRadius
  apply le_min
  · apply (div_le_div_iff₀ hD (mul_pos (by norm_num) hGradual)).mpr
    simp only [one_mul]
    unfold llyGradualNormConstant llySourceRadiusDenominator
    have hQSquare : (d : ℝ) ^ (3 / 4 : ℝ) ≤ ((d : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := by
      nlinarith only [hQOne]
    calc
      _ = 20 * Real.sqrt n * (if llySourceFirstRank n d a = 1 then 1 else
          (6 * (d : ℝ)) ^ (llySourceScale n d a + 1)) * (d : ℝ) ^ (3 / 4 : ℝ) := by ring
      _ ≤ 20 * Real.sqrt n * (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) *
          (d : ℝ) ^ (3 / 4 : ℝ) := by gcongr
      _ ≤ 20 * Real.sqrt n * (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) *
          ((d : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  · apply (div_le_div_iff₀ hD hThird).mpr
    simp only [one_mul]
    have hCancel : (llyThirdNetError d * Real.sqrt n) * llySourceRadiusDenominator n d a =
        20 * llyThirdSteepNormConstant n d (llySourceScale n d a) := by
      unfold llyThirdNetError llySourceRadiusDenominator llyThirdSteepNormConstant
      field_simp
    rw [hCancel]
    nlinarith only [hThird]

theorem lly_source_minimum_threshold_reciprocal_lower {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (a : ℝ) :
    1 / (llySourceRadiusDenominator n d a ^ 2 * n) ≤
      (llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n := by
  have hRadius := lly_source_almost_radius_reciprocal_lower hn hd a
  have hSquare := pow_le_pow_left₀
    (one_div_pos.mpr (lly_source_radius_denominator_pos (n := n) hd a)).le hRadius 2
  have hDiv := div_le_div_of_nonneg_right hSquare (Nat.cast_nonneg (α := ℝ) n)
  calc
    _ = (1 / llySourceRadiusDenominator n d a) ^ 2 / n := by ring
    _ ≤ llySourceAlmostRadius n d a ^ 2 / n := hDiv
    _ = llySourceAlmostRadius n d a ^ 2 / (Real.sqrt n) ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = _ := by ring

theorem lly_source_stride_log_degree_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d) :
    Real.log (d : ℝ) ≤ Real.log 1920000 + Real.log (Real.log (n : ℝ)) +
      2 * Real.log (llySourceStride n d : ℝ) := by
  have hStride := lly_source_stride_ge_two hn hd hC hDegree
  have hStrideR : (2 : ℝ) ≤ llySourceStride n d := by exact_mod_cast hStride
  have hEps := lly_source_epsilon_pos hn hd
  have hFloor := Nat.lt_floor_add_one (1 / (100 * llySourceEpsilon n d))
  change 1 / (100 * llySourceEpsilon n d) < (llySourceStride n d : ℝ) + 1 at hFloor
  have hRatio : 1 / (100 * llySourceEpsilon n d) ≤ 2 * llySourceStride n d := by
    linarith only [hFloor, hStrideR]
  have hProduct := (div_le_iff₀ (by positivity : 0 < 100 * llySourceEpsilon n d)).mp hRatio
  have hSquare : (1 : ℝ) ≤ (2 * llySourceStride n d * (100 * llySourceEpsilon n d)) ^ 2 := by
    nlinarith only [hProduct]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hScaled := mul_le_mul_of_nonneg_right hSquare hdR.le
  have hEpsSquare := lly_source_epsilon_square_degree hn hd
  have hEpsScaled := congrArg (fun t : ℝ => t * (40000 * (llySourceStride n d : ℝ) ^ 2)) hEpsSquare
  have hRaw : (d : ℝ) ≤ 1920000 * Real.log (n : ℝ) * (llySourceStride n d : ℝ) ^ 2 := by
    nlinarith only [hScaled, hEpsScaled]
  have hLog := Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hStridePos : (0 : ℝ) < llySourceStride n d := by linarith only [hStrideR]
  have h := Real.log_le_log hdR hRaw
  rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 1920000) hLog).ne'
      (pow_pos hStridePos 2).ne',
    Real.log_mul (by norm_num : (1920000 : ℝ) ≠ 0) hLog.ne', Real.log_pow] at h
  simpa only [Nat.cast_ofNat] using h

theorem lly_source_scale_log_stride_budget {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C a : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d)
    (ha : 0 < a) (haOne : a ≤ 1) :
    (llySourceScale n d a : ℝ) * Real.log (llySourceStride n d : ℝ) ≤ Real.log (n : ℝ) := by
  have hFirst := lly_source_scale_ranks hn hd hC hDegree ha
  have hStride := lly_source_stride_ge_two hn hd hC hDegree
  rcases hFirst.1 with hOne | hRank
  · have hScale : llySourceScale n d a = 0 := by simp [llySourceScale, hOne]
    rw [hScale, Nat.cast_zero, zero_mul]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  · have hRankN := lly_source_first_rank_le_dimension hn hd ha.le haOne (by linarith only [hC]) hDegree
    have hPow : (llySourceStride n d : ℝ) ^ llySourceScale n d a ≤ n := by
      exact_mod_cast (le_of_lt (lt_of_lt_of_le hRank hRankN))
    have h := Real.log_le_log (pow_pos
      (by exact_mod_cast (show 0 < llySourceStride n d by omega) : (0 : ℝ) < llySourceStride n d) _) hPow
    rwa [Real.log_pow] at h

theorem lly_source_radius_denominator_log (n d : ℕ) (hd : 0 < d) (a : ℝ) :
    Real.log (llySourceRadiusDenominator n d a) = Real.log 20 +
      ((llySourceScale n d a : ℝ) + 1) * Real.log (6 * (d : ℝ)) +
        (3 / 2 : ℝ) * Real.log (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hP : 0 < (6 * (d : ℝ)) ^ (llySourceScale n d a + 1) := by positivity
  have hQ := Real.rpow_pos_of_pos hdR (3 / 4 : ℝ)
  unfold llySourceRadiusDenominator
  rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 20) hP).ne' (pow_pos hQ 2).ne',
    Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) hP.ne']
  simp only [Real.log_pow, Real.log_rpow hdR, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem lly_source_minimum_threshold_of_stride_ratio {n d : ℕ} (hn : 20 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {C a K : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d)
    (ha : 0 < a) (haOne : a ≤ 1) (hK : 0 ≤ K)
    (hRatio : Real.log (6 * (d : ℝ)) ≤ K * Real.log (llySourceStride n d : ℝ)) :
    (n : ℝ) ^ (-(2 * K + 12)) ≤
      (llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n := by
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hD := lly_source_radius_denominator_pos (n := n) hd a
  have hLogN := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)
  have hLogD := Real.log_le_log hdR (by exact_mod_cast hdn : (d : ℝ) ≤ n)
  have hLog20 := Real.log_le_log (by norm_num : (0 : ℝ) < 20) (by exact_mod_cast hn : (20 : ℝ) ≤ n)
  have hLog6 := Real.log_le_log (by norm_num : (0 : ℝ) < 6)
    (by exact_mod_cast (show 6 ≤ n by omega) : (6 : ℝ) ≤ n)
  have hBase : Real.log (6 * (d : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hdR.ne']
    linarith only [hLog6, hLogD]
  have hScale := lly_source_scale_log_stride_budget (by omega : 2 ≤ n) hd hC hDegree ha haOne
  have hScaled := mul_le_mul_of_nonneg_left hRatio (Nat.cast_nonneg (α := ℝ) (llySourceScale n d a))
  have hScaleK := mul_le_mul_of_nonneg_left hScale hK
  have hLogBudget : Real.log (llySourceRadiusDenominator n d a) ≤
      (K + 9 / 2) * Real.log (n : ℝ) := by
    rw [lly_source_radius_denominator_log n d hd a]
    nlinarith only [hLog20, hLogD, hBase, hScaled, hScaleK]
  apply le_trans _ (lly_source_minimum_threshold_reciprocal_lower hnPos hd a)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hnR _)
    (one_div_pos.mpr (mul_pos (pow_pos hD 2) hnR))).mp
  rw [Real.log_rpow hnR, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (mul_pos (pow_pos hD 2) hnR).ne', Real.log_one,
    Real.log_mul (pow_pos hD 2).ne' hnR.ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hLogBudget, hLogN]

end CircularLaw
