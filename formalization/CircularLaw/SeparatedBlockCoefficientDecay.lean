import CircularLaw.SeparatedBlockSliceSmallBall
import CircularLaw.LLYThirdAdjointDecay

/-!
# Absorbing direct separated-block probabilities at the source ranks

The exponential pair-count tail is bounded by an inverse density. At
the source second rank the density grows like `d^(1/4)`, so the scalar
coefficient decays fast enough to pay the retained third-class net.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem separated_block_small_ball_coefficient_inverse_sqrt {μ : ℝ} (hμ : 1 ≤ μ) :
    separatedBlockSmallBallCoefficient μ ≤
      (2 * bernoulliScalarSmallBallConstant + 96) / Real.sqrt μ := by
  have hμPos : 0 < μ := by linarith
  have hRoot : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμPos
  have hRootLe : Real.sqrt μ ≤ μ := (Real.sqrt_le_iff).mpr ⟨hμPos.le, by nlinarith⟩
  have hExp : μ / 48 ≤ Real.exp (μ / 48) := by
    have h := Real.add_one_le_exp (μ / 48)
    linarith
  have hTail : Real.exp (-μ / 48) ≤ 48 / μ := by
    rw [show -μ / 48 = -(μ / 48) by ring, Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) hμPos).mpr
    nlinarith
  have hTailRoot : 2 * Real.exp (-μ / 48) ≤ 96 / Real.sqrt μ := by
    calc
      _ ≤ 2 * (48 / μ) := mul_le_mul_of_nonneg_left hTail (by norm_num)
      _ = 96 / μ := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hRoot hRootLe
  unfold separatedBlockSmallBallCoefficient
  calc
    _ ≤ 2 * bernoulliScalarSmallBallConstant / Real.sqrt μ + 96 / Real.sqrt μ :=
      add_le_add le_rfl hTailRoot
    _ = _ := by ring

theorem separated_block_tensorization_base_decay {d : ℕ} (hd : 0 < d)
    {a μ : ℝ} (ha : 0 < a) (hμ : 1 ≤ μ)
    (hDensity : a / 2 * (d : ℝ) ^ (1 / 4 : ℝ) ≤ μ)
    (hConstant : Real.log (8 * Real.exp 1 * (2 * bernoulliScalarSmallBallConstant + 96)) -
      Real.log (a / 2) / 2 ≤ Real.log (d : ℝ) / 16) :
    8 * Real.exp 1 * separatedBlockSmallBallCoefficient μ ≤
      Real.exp (-Real.log (d : ℝ) / 16) := by
  let F := 8 * Real.exp 1 * (2 * bernoulliScalarSmallBallConstant + 96)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hμPos : 0 < μ := by linarith
  have hF : 0 < F := by
    have hC := bernoulli_scalar_small_ball_constant_pos
    dsimp only [F]
    positivity
  have hLower : 0 < a / 2 * (d : ℝ) ^ (1 / 4 : ℝ) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hdR _)
  have hLogDensity : Real.log (a / 2) + (1 / 4 : ℝ) * Real.log (d : ℝ) ≤ Real.log μ := by
    have h := Real.log_le_log hLower hDensity
    rw [Real.log_mul (by positivity : a / 2 ≠ 0)
      (by positivity : (d : ℝ) ^ (1 / 4 : ℝ) ≠ 0), Real.log_rpow hdR] at h
    exact h
  have hLog : Real.log (F / Real.sqrt μ) ≤ -Real.log (d : ℝ) / 16 := by
    rw [Real.log_div hF.ne' (Real.sqrt_pos.mpr hμPos).ne', Real.log_sqrt hμPos.le]
    change Real.log F - Real.log (a / 2) / 2 ≤ _ at hConstant
    linarith
  calc
    _ ≤ F / Real.sqrt μ := by
      have h := mul_le_mul_of_nonneg_left (separated_block_small_ball_coefficient_inverse_sqrt hμ)
        (by positivity : 0 ≤ 8 * Real.exp 1)
      convert h using 1
      dsimp only [F]
      ring
    _ = Real.exp (Real.log (F / Real.sqrt μ)) := (Real.exp_log (div_pos hF
      (Real.sqrt_pos.mpr hμPos))).symm
    _ ≤ _ := Real.exp_le_exp.mpr hLog

theorem separated_block_retained_factor_decay {n d m K : ℕ} (hd : 0 < d)
    (hRows : (n : ℝ) / 2 ≤ K)
    (hBase : 8 * Real.exp 1 * separatedBlockSmallBallCoefficient
      ((m : ℝ) * ((d : ℝ) / n)) ≤ Real.exp (-Real.log (d : ℝ) / 16)) :
    (8 * Real.exp 1 * separatedBlockSmallBallCoefficient ((m : ℝ) * ((d : ℝ) / n))) ^ K ≤
      Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 32) := by
  have hNonneg : 0 ≤ 8 * Real.exp 1 * separatedBlockSmallBallCoefficient
      ((m : ℝ) * ((d : ℝ) / n)) :=
    mul_nonneg (by positivity) (separated_block_small_ball_coefficient_nonneg _)
  apply (pow_le_pow_left₀ hNonneg hBase K).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hLog := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hRowsScaled := mul_le_mul_of_nonneg_right hRows hLog
  nlinarith

theorem eventually_lly_third_source_right_base_decay {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      8 * Real.exp 1 * separatedBlockSmallBallCoefficient
        ((llySourceSecondRank n d a : ℝ) * ((d : ℝ) / n)) ≤
          Real.exp (-Real.log (d : ℝ) / 16) := by
  have hLog : ∀ᶠ d : ℕ in atTop,
      16 * (Real.log (8 * Real.exp 1 * (2 * bernoulliScalarSmallBallConstant + 96)) -
        Real.log (a / 2) / 2) ≤ Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  have hDegree : ∀ᶠ d : ℕ in atTop, 0 < d ∧
      2 / a ≤ (d : ℝ) ^ (1 / 4 : ℝ) ∧
        16 * (Real.log (8 * Real.exp 1 * (2 * bernoulliScalarSmallBallConstant + 96)) -
          Real.log (a / 2) / 2) ≤ Real.log (d : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hLog,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 4) (2 / a)]
        with d hd hLog hPower
    exact ⟨by omega, hPower, hLog⟩
  filter_upwards [eventually_ge_atTop 1, eventually_degree_property_uniform hC hDegree,
    eventually_lly_source_second_rank_size_uniform ha] with n hn hDegrees hSizes
  intro d hLower hdn
  obtain ⟨hd, hPower, hLog⟩ := hDegrees d hLower
  have hDensity := lly_source_second_rank_coefficient_density (by omega : 0 < n) hd (hSizes d hd hdn)
  have hOne : 1 ≤ a / 2 * (d : ℝ) ^ (1 / 4 : ℝ) := by
    have h := (div_le_iff₀ ha).mp hPower
    nlinarith
  exact separated_block_tensorization_base_decay hd ha (hOne.trans hDensity) hDensity (by linarith)

theorem eventually_lly_third_source_retained_net_probability_cost {C a₁ a₂ a₃ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 ≤ a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 ≤ a₃) (ha₃Small : a₃ ≤ 1 / 4096) (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d r : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      (llySourceFirstRank n d a₁ = 1 ∨ (llySourceStride n d) ^ r < llySourceFirstRank n d a₁) →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
        ((llyThirdNonconstantNet n d r (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
          (llySourceThirdRank n a₃) (llyThirdNetResolution d)).card : ℝ) *
          (meanCorrectedScalarNet (llyThirdNetResolution d) d (1 / 3) (llyThirdNetError d)).card *
            (8 * Real.exp 1 * separatedBlockSmallBallCoefficient
              ((llySourceSecondRank n d a₂ : ℝ) * ((d : ℝ) / n))) ^ I.card ≤
                Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_lly_third_source_net_cardinality_uniform hC ha₁ ha₁One ha₂.le ha₃ ha₃Small hFirstCost,
    eventually_lly_third_source_right_base_decay hCPos ha₂] with n hDegrees hCards hBases
  intro d r hLower hdn hRank I hRows
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hCard := hCards d r hLower hRank
  have hFactor := separated_block_retained_factor_decay hd hRows (hBases d hLower hdn)
  have hNonneg : 0 ≤ (8 * Real.exp 1 * separatedBlockSmallBallCoefficient
      ((llySourceSecondRank n d a₂ : ℝ) * ((d : ℝ) / n))) ^ I.card :=
    pow_nonneg (mul_nonneg (by positivity) (separated_block_small_ball_coefficient_nonneg _)) _
  apply (mul_le_mul hCard hFactor hNonneg (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end CircularLaw
