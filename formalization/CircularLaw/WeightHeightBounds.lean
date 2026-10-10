import CircularLaw.ProfileCutoffProduct

/-!
# Height bounds for the actual truncated profile weights

Every truncated weight lies between `height/d` and `height*sqrt(d)`.
The inequalities include all four branches of the source definition.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem truncatedProfileWeight_height_div_degree_le {α ι : Type*}
    [Fintype α] [Nonempty α] (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (q : ι) :
    (P.height q : ℝ) / d ≤ truncatedProfileWeight P d q := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hw := truncatedProfileWeight_pos P hd q
  have hRatio : (P.height q : ℝ) / truncatedProfileWeight P d q ≤ (d : ℝ) := by
    calc
      _ = Real.exp (Real.log ((P.height q : ℝ) / truncatedProfileWeight P d q)) :=
        (Real.exp_log (div_pos hh hw)).symm
      _ ≤ Real.exp (Real.log d) := Real.exp_le_exp.mpr (profile_height_weight_log_le_degree P hd q)
      _ = _ := Real.exp_log hdR
  exact (div_le_iff₀ hdR).mpr (by
    simpa only [mul_comm] using (div_le_iff₀ hw).mp hRatio)

theorem truncatedProfileWeight_le_height_sqrt_degree {α ι : Type*}
    [Fintype α] (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (q : ι) :
    truncatedProfileWeight P d q ≤ (P.height q : ℝ) * Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSqrt : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.mpr hdOne
  have hMass : partMass P.part q ≤ 1 := uniformProbability_le_one _
  have hh : (0 : ℝ) ≤ P.height q := Nat.cast_nonneg _
  have hHeight : (P.height q : ℝ) ≤ (P.height q : ℝ) * Real.sqrt d := by nlinarith
  unfold truncatedProfileWeight
  split_ifs
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) hh
  · exact (mul_le_mul_of_nonneg_left hMass hh).trans (by simpa only [mul_one] using hHeight)
  · exact hHeight
  · exact (div_le_self hh hdOne).trans hHeight

theorem profileLargePart_weight_lower {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (q : ι) (hq : profileLargePart P d q) :
    (P.height q : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ truncatedProfileWeight P d q := by
  change Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q at hq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hh : (0 : ℝ) ≤ P.height q := Nat.cast_nonneg _
  have hPowOne : Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hdOne (by norm_num : (-1 / 3 : ℝ) ≤ 0)
    simpa only [Real.rpow_zero] using h
  have hPowInv : 1 / (d : ℝ) ≤ Real.rpow (d : ℝ) (-1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hdOne (by norm_num : (-1 : ℝ) ≤ -1 / 3)
    simpa only [Real.rpow_neg_one, one_div, Real.rpow_eq_pow] using h
  have hDMass : 1 ≤ (d : ℝ) * partMass P.part q := by
    have h := (div_le_iff₀ hdR).mp (hPowInv.trans hq)
    simpa only [mul_comm] using h
  unfold truncatedProfileWeight
  rw [if_pos hq]
  split_ifs
  · have hSqrt : 1 ≤ Real.sqrt ((d : ℝ) * partMass P.part q) := Real.one_le_sqrt.mpr hDMass
    exact mul_le_mul_of_nonneg_left (hPowOne.trans hSqrt) hh
  · exact mul_le_mul_of_nonneg_left hq hh

end CircularLaw
