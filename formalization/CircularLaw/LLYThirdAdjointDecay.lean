import CircularLaw.LLYThirdNetCardinalityUniform
import CircularLaw.LLYThirdSteepAdjointProbability

/-!
# Absorbing the selected-row conditioning loss and both third-class nets

At the literal second rank, the coefficient density grows like `d^(1/4)`.
The resulting column probability overcomes both the selected-row cost
and the constructed third-class entropy, uniformly in the degree range.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def llyThirdAdjointFactor (n d m : ℕ) : ℝ :=
  (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ m *
    (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
      Real.sqrt ((m : ℝ) * ((d : ℝ) / n)))) ^ n

theorem lly_third_adjoint_factor_decay {n d m : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (hRank : (m : ℝ) ≤ (n : ℝ) / 4096)
    (hDensity : a / 2 * (d : ℝ) ^ (1 / 4 : ℝ) ≤ (m : ℝ) * ((d : ℝ) / n))
    (hDegree : 2 * (Real.log 4 + 2) ≤ Real.log (d : ℝ))
    (hConstant : Real.log (4 * Real.exp 1 * bernoulliScalarSmallBallConstant) -
      Real.log (a / 2) / 2 ≤ Real.log (d : ℝ) / 32) :
    llyThirdAdjointFactor n d m ≤ Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 16) := by
  let G := 4 * Real.exp 1 ^ 2 * Real.sqrt d
  let F := 4 * Real.exp 1 * bernoulliScalarSmallBallConstant
  let q := (m : ℝ) * ((d : ℝ) / n)
  let Y := 4 * Real.exp 1 * (bernoulliScalarSmallBallConstant / Real.sqrt q)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hG : 0 < G := by dsimp only [G]; positivity
  have hF : 0 < F := mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) bernoulli_scalar_small_ball_constant_pos
  have hLower : 0 < a / 2 * (d : ℝ) ^ (1 / 4 : ℝ) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hdR _)
  have hq : 0 < q := lt_of_lt_of_le hLower hDensity
  have hY : 0 < Y := by
    dsimp only [Y]
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
      (div_pos bernoulli_scalar_small_ball_constant_pos (Real.sqrt_pos.mpr hq))
  have hLogD := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hLogG : Real.log G ≤ Real.log (d : ℝ) := by
    have hLog : Real.log G = Real.log 4 + 2 + Real.log (d : ℝ) / 2 := by
      dsimp only [G]
      rw [Real.log_mul (by positivity : (4 : ℝ) * Real.exp 1 ^ 2 ≠ 0) hRoot.ne',
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : Real.exp 1 ^ 2 ≠ 0),
        Real.log_pow, Real.log_exp, Real.log_sqrt hdR.le]
      norm_num
    rw [hLog]
    linarith
  have hLogQ : Real.log (a / 2) + (1 / 4 : ℝ) * Real.log (d : ℝ) ≤ Real.log q := by
    have h := Real.log_le_log hLower hDensity
    rw [Real.log_mul (by positivity : a / 2 ≠ 0) (by positivity : (d : ℝ) ^ (1 / 4 : ℝ) ≠ 0),
      Real.log_rpow hdR] at h
    exact h
  have hLogY : Real.log Y ≤ -(3 / 32 : ℝ) * Real.log (d : ℝ) := by
    have hEq : Y = F / Real.sqrt q := by dsimp only [Y, F]; ring
    rw [hEq, Real.log_div hF.ne' (Real.sqrt_pos.mpr hq).ne', Real.log_sqrt hq.le]
    change Real.log F - Real.log q / 2 ≤ _
    change Real.log F - Real.log (a / 2) / 2 ≤ _ at hConstant
    linarith
  have hGPow : G ^ m = Real.exp ((m : ℝ) * Real.log G) := by
    rw [Real.exp_nat_mul, Real.exp_log hG]
  have hYPow : Y ^ n = Real.exp ((n : ℝ) * Real.log Y) := by
    rw [Real.exp_nat_mul, Real.exp_log hY]
  change G ^ m * Y ^ n ≤ _
  rw [hGPow, hYPow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hRow := mul_le_mul_of_nonneg_left hLogG (Nat.cast_nonneg (α := ℝ) m)
  have hColumn := mul_le_mul_of_nonneg_left hLogY (Nat.cast_nonneg (α := ℝ) n)
  have hRankScaled := mul_le_mul_of_nonneg_right hRank hLogD
  nlinarith

theorem lly_source_second_rank_coefficient_density {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {a : ℝ}
    (hSize : 2 ≤ a * n / (d : ℝ) ^ (3 / 4 : ℝ)) :
    a / 2 * (d : ℝ) ^ (1 / 4 : ℝ) ≤
      (llySourceSecondRank n d a : ℝ) * ((d : ℝ) / n) := by
  have hFloor := lly_source_second_rank_density_lower hSize
  have hD : 0 < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hNumerator := (div_le_iff₀ hD).mp hFloor
  have hScaled := mul_le_mul_of_nonneg_right hNumerator (Real.rpow_nonneg (Nat.cast_nonneg d) (1 / 4))
  have hPower : (d : ℝ) ^ (3 / 4 : ℝ) * (d : ℝ) ^ (1 / 4 : ℝ) = d := by
    rw [← Real.rpow_add (by exact_mod_cast hd : (0 : ℝ) < d)]
    norm_num
  rw [mul_assoc, mul_assoc, hPower] at hScaled
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  nlinarith

theorem eventually_lly_source_second_rank_size_uniform {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ n →
      2 ≤ a * n / (d : ℝ) ^ (3 / 4 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1, eventually_degree_real_power_lower
    (by norm_num : (0 : ℝ) < 1 / 4) (2 / a)] with n hn hPower
  intro d hd hdn
  have hScaled := (div_le_iff₀ ha).mp hPower
  have hMono : (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast hdn) (by norm_num)
  have hNumerator := mul_le_mul_of_nonneg_right hScaled (Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 4))
  change 2 * (n : ℝ) ^ (3 / 4 : ℝ) ≤
    (n : ℝ) ^ (1 / 4 : ℝ) * a * (n : ℝ) ^ (3 / 4 : ℝ) at hNumerator
  have hIdentity : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = n := by
    rw [← Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
    norm_num
  rw [show (n : ℝ) ^ (1 / 4 : ℝ) * a * (n : ℝ) ^ (3 / 4 : ℝ) =
    a * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) by ring, hIdentity] at hNumerator
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hd : (0 : ℝ) < d) _)).mpr
  linarith

theorem eventually_lly_third_adjoint_factor_decay_uniform {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      llyThirdAdjointFactor n d (llySourceSecondRank n d a) ≤
        Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 16) := by
  have hLog : ∀ᶠ d : ℕ in atTop,
      max (2 * (Real.log 4 + 2))
        (32 * (Real.log (4 * Real.exp 1 * bernoulliScalarSmallBallConstant) - Real.log (a / 2) / 2)) ≤
          Real.log (d : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _
  have hDegree : ∀ᶠ d : ℕ in atTop, 0 < d ∧
      4096 * a ≤ (d : ℝ) ^ (3 / 4 : ℝ) ∧
        max (2 * (Real.log 4 + 2))
          (32 * (Real.log (4 * Real.exp 1 * bernoulliScalarSmallBallConstant) - Real.log (a / 2) / 2)) ≤
            Real.log (d : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hLog,
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) _] with d hd hLog hPower
    exact ⟨by omega, hPower, hLog⟩
  filter_upwards [eventually_ge_atTop 1, eventually_degree_property_uniform hC hDegree,
    eventually_lly_source_second_rank_size_uniform ha] with n hn hDegrees hSizes
  intro d hLower hdn
  obtain ⟨hd, hPower, hLog⟩ := hDegrees d hLower
  exact lly_third_adjoint_factor_decay hd ha
    (lly_source_second_rank_small_density hd ha.le hPower)
    (lly_source_second_rank_coefficient_density (by omega : 0 < n) hd (hSizes d hd hdn))
    ((le_max_left _ _).trans hLog) (by have h := (le_max_right _ _).trans hLog; linarith)

theorem eventually_lly_third_source_net_probability_cost {C a₁ a₂ a₃ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 ≤ a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 ≤ a₃) (ha₃Small : a₃ ≤ 1 / 4096) (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d r : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      (llySourceFirstRank n d a₁ = 1 ∨ (llySourceStride n d) ^ r < llySourceFirstRank n d a₁) →
      ((llyThirdNonconstantNet n d r (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
        (llySourceThirdRank n a₃) (llyThirdNetResolution d)).card : ℝ) *
        (meanCorrectedScalarNet (llyThirdNetResolution d) d (1 / 3) (llyThirdNetError d)).card *
          llyThirdAdjointFactor n d (llySourceSecondRank n d a₂) ≤
            Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 1,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_lly_third_source_net_cardinality_uniform hC ha₁ ha₁One ha₂.le ha₃ ha₃Small hFirstCost,
    eventually_lly_third_adjoint_factor_decay_uniform hCPos ha₂] with n hn hDegrees hCards hFactors
  intro d r hLower hdn hRank
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hCard := hCards d r hLower hRank
  have hFactor := hFactors d hLower hdn
  have hNonneg : 0 ≤ llyThirdAdjointFactor n d (llySourceSecondRank n d a₂) := by
    unfold llyThirdAdjointFactor
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg (mul_nonneg (by positivity) (div_nonneg bernoulli_scalar_small_ball_constant_pos.le
        (Real.sqrt_nonneg _))) _)
  apply (mul_le_mul hCard hFactor hNonneg (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hLog := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hProduct : 0 ≤ (n : ℝ) * Real.log (d : ℝ) := mul_nonneg (Nat.cast_nonneg n) hLog
  nlinarith

end CircularLaw
