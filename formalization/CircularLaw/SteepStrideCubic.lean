import CircularLaw.SteepStrideRates

/-!
# Cubic growth of the literal floor stride

The source no-jump chain uses `4*d <= p^3` for sufficiently large degree.
The floor is retained; the condition follows from the checked limit
`log(d)^3/d -> 0`.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem steepStride_cubic {d : ℕ} (hd : 0 < d) (hLog : 1 ≤ Real.log (d : ℝ))
    (hLogCube : 16000000 * Real.log (d : ℝ) ^ 3 ≤ d) :
    4 * d ≤ steepStride d ^ 3 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLogPos : 0 < Real.log (d : ℝ) := lt_of_lt_of_le zero_lt_one hLog
  have hLogLeCube : Real.log (d : ℝ) ≤ Real.log (d : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log d - 1)
      (by positivity : (0 : ℝ) ≤ Real.log d ^ 2 + Real.log d)]
  have hRatio : Real.log (d : ℝ) / d ≤ 1 / 100 := by
    apply (div_le_iff₀ hdR).mpr
    nlinarith
  have hp := (steepStride_bounds hd hLog hRatio).1
  let R := Real.sqrt ((d : ℝ) / Real.log d)
  have hFloor := Nat.floor_le (by positivity : (0 : ℝ) ≤ (1 / 5 : ℝ) * R)
  have hFloorClose := Nat.lt_floor_add_one ((1 / 5 : ℝ) * R)
  have hpR : (2 : ℝ) ≤ steepStride d := by exact_mod_cast (by omega : 2 ≤ steepStride d)
  change (steepStride d : ℝ) ≤ (1 / 5 : ℝ) * R at hFloor
  change (1 / 5 : ℝ) * R < (steepStride d : ℝ) + 1 at hFloorClose
  have hLower : R / 10 ≤ (steepStride d : ℝ) := by linarith
  have hSquare := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hLower 2
  have hRootSquare : R ^ 2 = (d : ℝ) / Real.log d := Real.sq_sqrt (div_pos hdR hLogPos).le
  have hSquareBound : (d : ℝ) ≤ 100 * Real.log d * (steepStride d : ℝ) ^ 2 := by
    rw [div_pow, hRootSquare] at hSquare
    have hScaled := mul_le_mul_of_nonneg_left hSquare (show (0 : ℝ) ≤ 100 * Real.log d by positivity)
    have hCancel : 100 * Real.log d * ((d : ℝ) / Real.log d / 10 ^ 2) = d := by field_simp; ring
    rw [hCancel] at hScaled
    nlinarith
  have hCube := pow_le_pow_left₀ hdR.le hSquareBound 3
  have hCubeBound : (d : ℝ) ^ 3 ≤ 1000000 * Real.log d ^ 3 * (steepStride d : ℝ) ^ 6 := by
    convert hCube using 1
    ring
  have hScaled := mul_le_mul_of_nonneg_right hLogCube (pow_nonneg (Nat.cast_nonneg (steepStride d)) 6)
  have hCancel : 16 * (d : ℝ) ^ 3 ≤ (d : ℝ) * (steepStride d : ℝ) ^ 6 := by nlinarith
  have hCompare : (4 * (d : ℝ)) ^ 2 ≤ ((steepStride d : ℝ) ^ 3) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hdR).mp
    convert hCancel using 1 <;> ring
  have hFinal := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 4 * d)
    (pow_nonneg (Nat.cast_nonneg (steepStride d)) 3)).mp hCompare
  exact_mod_cast hFinal

theorem eventually_steepStride_cubic : ∀ᶠ d : ℕ in atTop, 4 * d ≤ steepStride d ^ 3 := by
  have hLimit := (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  have hSmall : ∀ᶠ d : ℕ in atTop, Real.log (d : ℝ) ^ 3 / d ≤ 1 / 16000000 :=
    (hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16000000))).mono (fun _ h => h.le)
  have hLog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [hSmall, hLog, eventually_ge_atTop 1] with d hSmall hLog hd
  apply steepStride_cubic hd hLog
  have hScaled := (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp hSmall
  nlinarith

end CircularLaw
