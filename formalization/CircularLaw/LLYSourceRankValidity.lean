import CircularLaw.LLYThirdAdjointDecay

/-!
# Validity of the rounded source ranks throughout the degree window

All rank bounds retain the ceiling and floors in the source definitions.
The second rank is positive uniformly even at degree n, and its order
relative to the third rank follows from the actual degree lower bound.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_third_rank_density_lower {n : ℕ} {a : ℝ}
    (hSize : 2 ≤ a * n) : a * n / 2 ≤ llySourceThirdRank n a := by
  have hFloor := Nat.lt_floor_add_one (a * n)
  change _ ≤ (⌊a * n⌋₊ : ℝ)
  linarith

theorem lly_source_third_rank_half {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (haHalf : a ≤ 1 / 2) :
    2 * llySourceThirdRank n a ≤ n := by
  have hUpper := lly_source_third_rank_upper (n := n) ha
  have hScaled := mul_le_mul_of_nonneg_right haHalf (Nat.cast_nonneg (α := ℝ) n)
  have hReal : (2 : ℝ) * llySourceThirdRank n a ≤ n := by linarith
  exact_mod_cast hReal

theorem lly_source_second_rank_le_third {n d : ℕ} (hd : 0 < d) {a₂ a₃ : ℝ}
    (ha₂ : 0 ≤ a₂) (hSize : 2 ≤ a₃ * n)
    (hPower : 2 * a₂ ≤ a₃ * (d : ℝ) ^ (3 / 4 : ℝ)) :
    llySourceSecondRank n d a₂ ≤ llySourceThirdRank n a₃ := by
  have hUpper := lly_source_second_rank_upper (n := n) (d := d) ha₂
  have hLower := lly_source_third_rank_density_lower hSize
  have hScaled := mul_le_mul_of_nonneg_right hPower (Nat.cast_nonneg (α := ℝ) n)
  have hRatio : a₂ * n / (d : ℝ) ^ (3 / 4 : ℝ) ≤ a₃ * n / 2 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hd : (0 : ℝ) < d) _)).mpr
    nlinarith
  exact_mod_cast (hUpper.trans hRatio).trans hLower

theorem eventually_lly_source_rank_validity {C a₁ a₂ a₃ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1)
    (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha₃Half : a₃ ≤ 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      0 < d ∧ 2 ≤ llySourceStride n d ∧
        0 < llySourceFirstRank n d a₁ ∧ llySourceFirstRank n d a₁ ≤ n ∧
          0 < llySourceSecondRank n d a₂ ∧ 0 < llySourceThirdRank n a₃ ∧
            llySourceSecondRank n d a₂ ≤ llySourceThirdRank n a₃ ∧
              2 * llySourceThirdRank n a₃ ≤ n := by
  have hCPos : 0 < C := by linarith
  have hThirdSize : ∀ᶠ n : ℕ in atTop, 2 ≤ a₃ * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (2 / a₃)] with n hn
    have h := (div_le_iff₀ ha₃).mp hn
    nlinarith
  have hCross : ∀ᶠ d : ℕ in atTop, 2 * a₂ ≤ a₃ * (d : ℝ) ^ (3 / 4 : ℝ) := by
    filter_upwards [eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4)
      (2 * a₂ / a₃)] with d hd
    change 2 * a₂ / a₃ ≤ (d : ℝ) ^ (3 / 4 : ℝ) at hd
    have h := (div_le_iff₀ ha₃).mp hd
    nlinarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_degree_property_uniform hCPos hCross,
    eventually_lly_source_second_rank_size_uniform ha₂, hThirdSize]
      with n hn hDegrees hCrosses hSecondSizes hThirdSize
  intro d hLower hdn
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hSecondLower := lly_source_second_rank_density_lower (hSecondSizes d hd hdn)
  have hSecondPos : 0 < llySourceSecondRank n d a₂ := by
    have hReal : (0 : ℝ) < llySourceSecondRank n d a₂ := by
      linarith [hSecondSizes d hd hdn]
    exact_mod_cast hReal
  have hThirdPos : 0 < llySourceThirdRank n a₃ := by
    have hReal : (0 : ℝ) < llySourceThirdRank n a₃ := by
      linarith [lly_source_third_rank_density_lower hThirdSize]
    exact_mod_cast hReal
  exact ⟨hd, lly_source_stride_ge_two hn hd hC hLower,
    lly_source_first_rank_pos hn hd ha₁,
    lly_source_first_rank_le_dimension hn hd ha₁.le ha₁One (by linarith) hLower,
    hSecondPos, hThirdPos,
    lly_source_second_rank_le_third hd ha₂.le hThirdSize (hCrosses d hLower),
    lly_source_third_rank_half ha₃.le ha₃Half⟩

end CircularLaw
