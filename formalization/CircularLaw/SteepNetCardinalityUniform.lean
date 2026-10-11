import CircularLaw.SteepNetCardinalityFinite

/-!
# Uniform source exponential net-size bounds

A single dimension threshold covers every integer degree in the literal
lower band. It bounds the actual Cartesian product of the nonconstant
and constant nets, a stronger count than that of their summed image.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_degree_real_power_lower {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, B ≤ Real.rpow (d : ℝ) a := by
  have hGrowth : Tendsto (fun d : ℕ => Real.rpow (d : ℝ) a) atTop atTop := by
    simpa only [Real.rpow_eq_pow] using (tendsto_rpow_atTop ha).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  exact hGrowth.eventually_ge_atTop B

theorem eventually_steep_net_count_seven_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      (((steepNetCountBound n d (secondSteepScale n d) 1 * steepNetGridCount d 1 : ℕ) : ℝ) ≤
        Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ))) ∧
      (((steepNetCountBound n d (thirdSteepScale n a₃) (Real.rpow (d : ℝ) (3 / 2)) *
        steepNetGridCount d (Real.rpow (d : ℝ) (3 / 2)) : ℕ) : ℝ) ≤
          Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ))) := by
  have hLog : ∀ᶠ d : ℕ in atTop,
      max 3 (max (4 * Real.log 121) (8 * smallSetEntropy a₃ / a₃)) ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  have hDegree : ∀ᶠ d : ℕ in atTop,
      max 3 (max (4 * Real.log 121) (8 * smallSetEntropy a₃ / a₃)) ≤ Real.log (d : ℝ) ∧
      4 * steepNetMiddleConstant ≤ Real.rpow (d : ℝ) (5 / 6) ∧
      8 * steepNetHighConstant / C ≤ Real.rpow (d : ℝ) (1 / 12) ∧
      8 * steepNetMiddleConstant / a₃ ≤ Real.rpow (d : ℝ) (3 / 2) ∧
      16 * steepNetHighConstant / (a₃ * C) ≤ Real.rpow (d : ℝ) (3 / 4) ∧
      4 * d ≤ steepStride d ^ 3 := by
    filter_upwards [hLog, eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 5 / 6) _,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 12) _,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 2) _,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) _,
      eventually_steepStride_cubic] with d hLog hMid₁ hHigh₁ hMid₂ hHigh₂ hCubic
    exact ⟨hLog, hMid₁, hHigh₁, hMid₂, hHigh₂, hCubic⟩
  have hNSize : ∀ᶠ n : ℕ in atTop, 2 / a₃ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_degree_property_uniform hC hDegree, hNSize] with n hConditions hDegree hNSize
  intro d hBand
  have h := hConditions d hBand.1 hBand.2
  obtain ⟨hLog, hMid₁, hHigh₁, hMid₂, hHigh₂, hCubic⟩ := hDegree d hBand.1
  have hLogThree : 3 ≤ Real.log (d : ℝ) := (le_max_left _ _).trans hLog
  have hLogBase : 4 * Real.log 121 ≤ Real.log (d : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hLog)
  have hLogSupport : 8 * smallSetEntropy a₃ / a₃ ≤ Real.log (d : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLog)
  have hLogBaseOne : Real.log 121 ≤ Real.log (d : ℝ) := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 121)
    linarith
  have hSize : 2 ≤ a₃ * (n : ℝ) := by
    have h := (div_le_iff₀ ha).mp hNSize
    nlinarith
  exact ⟨steep_net_T1_count_seven h hCubic hC hBand.1 hLogThree hLogBaseOne hMid₁ hHigh₁,
    steep_net_T2_count_seven ha haOne hSize h hCubic hC hBand.1
      (by linarith : 1 ≤ Real.log (d : ℝ)) hLogBase hLogSupport hMid₂ hHigh₂⟩

theorem eventually_source_steep_net_cardinality_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      (((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card ≤
        Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ))) ∧
      (((sourceT2Net n d a₃).card : ℝ) * (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card ≤
        Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ))) := by
  filter_upwards [eventually_steep_net_count_seven_uniform ha haOne hC σ] with n hCounts
  intro d hBand
  have h := hCounts d hBand
  have h₁ := Nat.mul_le_mul (steepNonconstantNet_card_le n d (firstSteepScale n d) (secondSteepScale n d) 1)
    (steepConstantNet_card_le d 1)
  have h₂ := Nat.mul_le_mul (steepNonconstantNet_card_le n d (secondSteepScale n d) (thirdSteepScale n a₃)
    (Real.rpow (d : ℝ) (3 / 2))) (steepConstantNet_card_le d (Real.rpow (d : ℝ) (3 / 2)))
  constructor
  · apply le_trans _ h.1
    exact_mod_cast h₁
  · apply le_trans _ h.2
    exact_mod_cast h₂

def SourceSteepNetCardinalityLemma : Prop :=
  ∀ a₃ : ℝ, 0 < a₃ → a₃ < 1 / 2 → ∀ C : ℝ, 0 < C →
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ d : ℕ, InLowerBand C σ n d →
        (((sourceT1Net n d).card : ℝ) * (steepConstantNet d 1).card ≤
          Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ))) ∧
        (((sourceT2Net n d a₃).card : ℝ) * (steepConstantNet d (Real.rpow (d : ℝ) (3 / 2))).card ≤
          Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ)))

theorem source_steep_net_cardinality_lemma : SourceSteepNetCardinalityLemma := by
  intro a₃ ha haHalf C hC σ _ _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_source_steep_net_cardinality_uniform ha (by linarith : a₃ ≤ 1) hC σ)
  exact ⟨N, hN⟩

end CircularLaw
