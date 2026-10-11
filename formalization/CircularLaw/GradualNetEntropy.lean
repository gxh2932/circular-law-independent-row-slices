import CircularLaw.GradualNetCounting
import CircularLaw.UniformGradualClassCount

/-!
# Absorbing the crude gradual-net entropy

The top-coordinate cost uses `n2 <= n/d^(2/3)` and the standing lower
bound `C*log(n) <= d`. The discretization logarithm has its own explicit
budget. These give the required `exp(C*n*d^(1/3))` bound uniformly over
the degree band, both codimensions and every restricted gradual family.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem secondSteepScale_log_cost {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {C : ℝ} (hC : 0 < C) (hLower : C * Real.log n ≤ (d : ℝ)) :
    (secondSteepScale n d : ℝ) * Real.log n ≤
      ((n : ℝ) / C) * Real.rpow (d : ℝ) (1 / 3) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos hdR _
  have hLogN : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hLogUpper : Real.log n ≤ (d : ℝ) / C :=
    (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using hLower)
  have hProduct : Real.rpow (d : ℝ) (2 / 3) * Real.rpow (d : ℝ) (1 / 3) = d := by
    change (d : ℝ) ^ (2 / 3 : ℝ) * (d : ℝ) ^ (1 / 3 : ℝ) = d
    rw [← Real.rpow_add hdR]
    norm_num
  calc
    _ ≤ ((n : ℝ) / Real.rpow (d : ℝ) (2 / 3)) * ((d : ℝ) / C) :=
      mul_le_mul (secondSteepScale_upper n d) hLogUpper hLogN
        (div_nonneg (Nat.cast_nonneg n) hPower.le)
    _ = _ := by
      rw [show (d : ℝ) / C =
        (Real.rpow (d : ℝ) (2 / 3) * Real.rpow (d : ℝ) (1 / 3)) / C by rw [hProduct]]
      field_simp

theorem gradualNetCountingEntropy_bound {n d k : ℕ} {C B : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) (hC : 0 < C)
    (hLower : C * Real.log n ≤ (d : ℝ))
    (hLogD : Real.log d ≤ Real.rpow (d : ℝ) (1 / 3))
    (hLogK : Real.log k ≤ B * Real.rpow (d : ℝ) (1 / 3)) :
    gradualNetCountingEntropy n d k ≤
      (100 + 4 * B + 12 / C) * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hThird : 1 ≤ Real.rpow (d : ℝ) (1 / 3) := Real.one_le_rpow hdR (by norm_num)
  have hTwoThird : 1 ≤ Real.rpow (d : ℝ) (2 / 3) := Real.one_le_rpow hdR (by norm_num)
  have hRank : (secondSteepScale n d : ℝ) ≤ n :=
    (secondSteepScale_upper n d).trans (div_le_self (Nat.cast_nonneg n) hTwoThird)
  have hLogK0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have hLog49 : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  have hConstRank := mul_le_mul_of_nonneg_right hRank (show 0 ≤ Real.log 49 + 2 * Real.log k by linarith)
  have hRankLog := secondSteepScale_log_cost hn hd hC hLower
  have hLog2Upper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLog49Upper : Real.log 49 ≤ 48 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 49)
    linarith
  have hCoefficient : Real.log 2 + 2 * Real.log 49 + 4 * Real.log k + 3 * Real.log d ≤
      (100 + 4 * B) * Real.rpow (d : ℝ) (1 / 3) := by
    nlinarith only [hLog2Upper, hLog49Upper, hLogD, hLogK, hThird]
  have hMain := mul_le_mul_of_nonneg_left hCoefficient (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  unfold gradualNetCountingEntropy
  rw [div_eq_mul_inv] at hRankLog ⊢
  nlinarith only [hConstRank, hRankLog, hMain]

theorem eventually_degree_log_le_cube_root :
    ∀ᶠ d : ℕ in atTop, Real.log d ≤ Real.rpow (d : ℝ) (1 / 3) := by
  have hLimit : Tendsto (fun d : ℕ => Real.log d / Real.rpow (d : ℝ) (1 / 3))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with d hd hSmall
  have hPos : 0 < Real.rpow (d : ℝ) (1 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  exact (div_lt_one hPos).mp hSmall |>.le

theorem eventually_sourceGradualApprox_family_exp_cube_root_uniform {C : ℝ}
    (hC : 96 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ, ∀ k : ℕ, 0 < k →
      Real.log k ≤ 2 * Real.rpow (d : ℝ) (1 / 96) →
      (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite ∧
      (Nat.card (canonicalApproxFamily k (sourceGradual n d L a₃)) : ℝ) ≤
        Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos eventually_steepStride_cubic,
    eventually_degree_property_uniform hCPos eventually_degree_log_le_cube_root]
    with n hConditions hCubic hLogDegree
  intro d hBand L hL a₃ k hk hLogK
  have hCon := hConditions d hBand.1 hBand.2
  have hFinite := source_kernel_dimension_twice_degree hCon
  obtain ⟨hFamily, hCount⟩ := sourceGradualApprox_family_entropy_bound hCon hL
    (hCubic d hBand.1) hk
  have hPower : Real.rpow (d : ℝ) (1 / 96) ≤ Real.rpow (d : ℝ) (1 / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hFinite.2.1) (by norm_num)
  have hEntropy := gradualNetCountingEntropy_bound hFinite.1 hFinite.2.1 hk hCPos
    hBand.1 (hLogDegree d hBand.1) (hLogK.trans (mul_le_mul_of_nonneg_left hPower (by norm_num)))
  have hRatio : 12 / C ≤ 1 := (div_le_iff₀ hCPos).mpr (by linarith)
  refine ⟨hFamily, hCount.trans (Real.exp_le_exp.mpr (hEntropy.trans ?_))⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : (100 : ℝ) + 4 * 2 + 12 / C ≤ 128)
      (Nat.cast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

theorem eventually_restrictedGradualApprox_family_exp_cube_root_uniform {C : ℝ}
    (hC : 96 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ, ∀ k : ℕ, 0 < k →
      Real.log k ≤ 2 * Real.rpow (d : ℝ) (1 / 96) →
      ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
      (canonicalApproxFamily k X).Finite ∧ (Nat.card (canonicalApproxFamily k X) : ℝ) ≤
        Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)) := by
  filter_upwards [eventually_sourceGradualApprox_family_exp_cube_root_uniform hC σ] with n hCount
  intro d hBand L hL a₃ k hk hLogK X hX
  obtain ⟨hFinite, hBound⟩ := hCount d hBand L hL a₃ k hk hLogK
  have hSubset := canonicalApproxFamily_mono k hX
  letI := hFinite.fintype
  have hCard : Nat.card (canonicalApproxFamily k X) ≤
      Nat.card (canonicalApproxFamily k (sourceGradual n d L a₃)) :=
    Nat.card_le_card_of_injective (fun y => (⟨y.val, hSubset y.property⟩ :
      canonicalApproxFamily k (sourceGradual n d L a₃)))
      (fun _ _ h => Subtype.ext (congrArg
        (@Subtype.val (Fin n → ℂ) (canonicalApproxFamily k (sourceGradual n d L a₃))) h))
  have hReal : (Nat.card (canonicalApproxFamily k X) : ℝ) ≤
      Nat.card (canonicalApproxFamily k (sourceGradual n d L a₃)) := by
    exact_mod_cast hCard
  exact ⟨hFinite.subset hSubset, hReal.trans hBound⟩

end CircularLaw
