import CircularLaw.SteepWitnessEntropy

/-!
# Eventual bounds for the actual steep stride

The literal floor stride is eventually at least two and at most
`sqrt(d)/5`. Its pair entropy is absorbed by the unique-witness rate.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem steepStride_bounds {d : ℕ} (hd : 0 < d) (hLog : 1 ≤ Real.log (d : ℝ))
    (hRatio : Real.log (d : ℝ) / d ≤ 1 / 100) :
    1 < steepStride d ∧ (steepStride d : ℝ) ≤ Real.sqrt d / 5 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLogPos : 0 < Real.log (d : ℝ) := lt_of_lt_of_le zero_lt_one hLog
  have hRatioLarge : (100 : ℝ) ≤ (d : ℝ) / Real.log d := by
    have h := (div_le_iff₀ hdR).mp hRatio
    apply (le_div_iff₀ hLogPos).mpr
    linarith
  have hRootLarge : (10 : ℝ) ≤ Real.sqrt ((d : ℝ) / Real.log d) := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (div_pos hdR hLogPos).le]
    norm_num
    exact hRatioLarge
  have hFloor : 2 ≤ steepStride d := by
    apply (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (1 / 5 : ℝ) *
      Real.sqrt ((d : ℝ) / Real.log d))).mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hDiv : (d : ℝ) / Real.log d ≤ d := by
    apply (div_le_iff₀ hLogPos).mpr
    nlinarith
  have hRoot := Real.sqrt_le_sqrt hDiv
  have hUpper := Nat.floor_le (by positivity : (0 : ℝ) ≤ (1 / 5 : ℝ) *
    Real.sqrt ((d : ℝ) / Real.log d))
  change (steepStride d : ℝ) ≤ (1 / 5 : ℝ) * Real.sqrt ((d : ℝ) / Real.log d) at hUpper
  exact ⟨by omega, by nlinarith⟩

theorem eventually_steepStride_bounds :
    ∀ᶠ d : ℕ in atTop, 1 < steepStride d ∧ (steepStride d : ℝ) ≤ Real.sqrt d / 5 := by
  have hLimit := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  simp only [Real.rpow_one] at hLimit
  have hSmall : ∀ᶠ d : ℕ in atTop, Real.log (d : ℝ) / d ≤ 1 / 100 :=
    (hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))).mono (fun _ h => h.le)
  have hLog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [hSmall, hLog, eventually_ge_atTop 1] with d hSmall hLog hd
  exact steepStride_bounds hd hLog hSmall

theorem eventually_steep_witness_entropy :
    ∀ᶠ d : ℕ in atTop, Real.sqrt d / 5 * (1 + 4 * Real.log d + Real.log 2) ≤
      (uniqueWitnessRate / 2) * d := by
  have hRate := uniqueWitnessRate_pos
  have hLimit := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  simp only [← Real.sqrt_eq_rpow] at hLimit
  have hSmall : ∀ᶠ d : ℕ in atTop, Real.log d / Real.sqrt d < 5 * uniqueWitnessRate / 16 :=
    hLimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 5 * uniqueWitnessRate / 16))
  have hLarge : ∀ᶠ d : ℕ in atTop,
      4 * (1 + Real.log 2) / (5 * uniqueWitnessRate) ≤ Real.sqrt d :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  filter_upwards [hSmall, hLarge, eventually_ge_atTop 1] with d hSmall hLarge hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hLog := (div_lt_iff₀ hRoot).mp hSmall
  have hConstant := (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * uniqueWitnessRate)).mp hLarge
  have hC : 1 + 4 * Real.log d + Real.log 2 ≤ (5 * uniqueWitnessRate / 2) * Real.sqrt d := by
    linarith
  have hScaled := mul_le_mul_of_nonneg_left hC (div_nonneg hRoot.le (by norm_num : (0 : ℝ) ≤ 5))
  have hSquare := congrArg (fun a : ℝ => (uniqueWitnessRate / 2) * a) (Real.sq_sqrt hdR.le)
  nlinarith

end CircularLaw
