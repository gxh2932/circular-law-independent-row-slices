import CircularLaw.LLYSourceRanks
import CircularLaw.SteepNetCardinalityUniform
import CircularLaw.LowerBandEventually

/-!
# Uniform cardinality bounds at the literal LLY ranks

For every degree above a fixed logarithmic threshold, one dimension
threshold absorbs the constructed third-class vector and scalar nets.
The rounded first rank and its empty-prefix case are retained.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_second_rank_small_density {n d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 ≤ a) (hPower : 4096 * a ≤ (d : ℝ) ^ (3 / 4 : ℝ)) :
    (llySourceSecondRank n d a : ℝ) ≤ (n : ℝ) / 4096 := by
  apply (lly_source_second_rank_upper ha).trans
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hd : (0 : ℝ) < d) _)).mpr
  have hScaled := mul_le_mul_of_nonneg_right hPower (Nat.cast_nonneg (α := ℝ) n)
  nlinarith

theorem lly_third_source_net_count_absorbed {n d r : ℕ} {C a₁ a₂ a₃ : ℝ}
    (hn : 20480 ≤ n) (hd : 0 < d) (hC : 1920000 ≤ C)
    (ha₁ : 0 ≤ a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hDegree : C * Real.log (n : ℝ) ≤ d) (hFirstCost : 12288 * a₁ ≤ C * Real.log 2)
    (hRank : llySourceFirstRank n d a₁ = 1 ∨ (llySourceStride n d) ^ r < llySourceFirstRank n d a₁)
    (hLog : Real.log 484 ≤ Real.log (d : ℝ))
    (hEntropy : 384 * smallSetEntropy (1 / 4096) ≤ Real.log (d : ℝ))
    (hPower : max (4096 * a₂) 100 ≤ (d : ℝ) ^ (3 / 4 : ℝ)) :
    (llyThirdNetCountBound n d r (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
      (llySourceThirdRank n a₃) (llyThirdNetError d) : ℝ) ≤
        Real.exp ((n : ℝ) * Real.log (d : ℝ) / 64) := by
  have hnTwo : 2 ≤ n := by omega
  have hCost := lly_source_first_prefix_cost hnTwo hd (lly_source_stride_ge_two hnTwo hd hC hDegree)
    ha₁ ha₁One (by linarith : 48 ≤ C) hDegree hFirstCost hRank
  have hFirst : ((llySourceFirstRank n d a₁ - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4096 := by
    have hPrev : (0 : ℝ) ≤ (llySourceFirstRank n d a₁ - 1 : ℕ) := Nat.cast_nonneg _
    nlinarith
  have hSecond := lly_source_second_rank_small_density (n := n) hd ha₂ ((le_max_left _ _).trans hPower)
  have hSecondPrev : ((llySourceSecondRank n d a₂ - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4096 :=
    (by exact_mod_cast Nat.sub_le (llySourceSecondRank n d a₂) 1 :
      ((llySourceSecondRank n d a₂ - 1 : ℕ) : ℝ) ≤ llySourceSecondRank n d a₂).trans hSecond
  have hThird : (llySourceThirdRank n a₃ : ℝ) ≤ (n : ℝ) / 4096 :=
    (lly_source_third_rank_upper ha₃).trans (by nlinarith)
  have hThirdPrev : ((llySourceThirdRank n a₃ - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4096 :=
    (by exact_mod_cast Nat.sub_le (llySourceThirdRank n a₃) 1 :
      ((llySourceThirdRank n a₃ - 1 : ℕ) : ℝ) ≤ llySourceThirdRank n a₃).trans hThird
  have hError : llyThirdNetError d ≤ 1 / 100 := by
    unfold llyThirdNetError
    apply (div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 100)
      ((le_max_right _ _).trans hPower)).trans
    norm_num
  exact lly_third_net_count_absorbed hn hd hLog (by norm_num : (0 : ℝ) < 1 / 4096)
    (by norm_num : (1 / 4096 : ℝ) ≤ 1)
    (by simpa only [one_div_mul_eq_div] using hFirst)
    (by simpa only [one_div_mul_eq_div] using hSecondPrev)
    (by simpa only [one_div_mul_eq_div] using hThirdPrev) hCost hSecondPrev hThirdPrev
    (by linarith : smallSetEntropy (1 / 4096) ≤ Real.log (d : ℝ) / 384) hError

theorem eventually_lly_third_source_net_count_uniform {C a₁ a₂ a₃ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 ≤ a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 ≤ a₂)
    (ha₃ : 0 ≤ a₃) (ha₃Small : a₃ ≤ 1 / 4096) (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d r : ℕ, C * Real.log (n : ℝ) ≤ d →
      (llySourceFirstRank n d a₁ = 1 ∨ (llySourceStride n d) ^ r < llySourceFirstRank n d a₁) →
      (llyThirdNetCountBound n d r (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
        (llySourceThirdRank n a₃) (llyThirdNetError d) : ℝ) ≤
          Real.exp ((n : ℝ) * Real.log (d : ℝ) / 64) := by
  have hCPos : 0 < C := by linarith
  have hLog : ∀ᶠ d : ℕ in atTop,
      max (Real.log 484) (384 * smallSetEntropy (1 / 4096)) ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  have hDegree : ∀ᶠ d : ℕ in atTop, 0 < d ∧
      max (Real.log 484) (384 * smallSetEntropy (1 / 4096)) ≤ Real.log (d : ℝ) ∧
        max (4096 * a₂) 100 ≤ (d : ℝ) ^ (3 / 4 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hLog,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) _]
      with d hd hLog hPower
    exact ⟨by omega, hLog, hPower⟩
  filter_upwards [eventually_ge_atTop 20480, eventually_degree_property_uniform hCPos hDegree]
    with n hn hDegrees
  intro d r hLower hRank
  obtain ⟨hd, hLog, hPower⟩ := hDegrees d hLower
  exact lly_third_source_net_count_absorbed hn hd hC ha₁ ha₁One ha₂ ha₃ ha₃Small hLower hFirstCost hRank
    ((le_max_left _ _).trans hLog) ((le_max_right _ _).trans hLog) hPower

theorem eventually_lly_third_source_net_cardinality_uniform {C a₁ a₂ a₃ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 ≤ a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 ≤ a₂)
    (ha₃ : 0 ≤ a₃) (ha₃Small : a₃ ≤ 1 / 4096) (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d r : ℕ, C * Real.log (n : ℝ) ≤ d →
      (llySourceFirstRank n d a₁ = 1 ∨ (llySourceStride n d) ^ r < llySourceFirstRank n d a₁) →
      ((llyThirdNonconstantNet n d r (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
        (llySourceThirdRank n a₃) (llyThirdNetResolution d)).card : ℝ) *
        (meanCorrectedScalarNet (llyThirdNetResolution d) d (1 / 3) (llyThirdNetError d)).card ≤
          Real.exp ((n : ℝ) * Real.log (d : ℝ) / 64) := by
  filter_upwards [eventually_lly_third_source_net_count_uniform hC ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost]
    with n hCounts
  intro d r hLower hRank
  apply le_trans _ (hCounts d r hLower hRank)
  exact_mod_cast lly_third_net_card_product_le_count n d r (llySourceFirstRank n d a₁)
    (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) (llyThirdNetError d)

end CircularLaw
