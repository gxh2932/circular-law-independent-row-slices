import CircularLaw.GradualClassEntropyFormula
import CircularLaw.SteepNetCardinalityUniform

/-!
# The manuscript's exponential approximation-class count

In the standing logarithmic lower degree band, each of the four actual
block entropy costs is at most `1/4` uniformly for large dimension.
This closes the `exp(n)` class count for every source discretization
scale and both admissible codimensions. The same count applies to every
restricted family, with finiteness proved from the literal encoding.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_gradualClass_degree_budgets (C : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      49 ≤ d ∧ 1 ≤ Real.log d ∧ 200 ≤ (d : ℝ) ^ 3 ∧
      Real.log d / (d : ℝ) ^ 3 ≤ 1 / 600 ∧
      8 ≤ Real.rpow (d : ℝ) (2 / 3) ∧
      Real.log d / Real.rpow (d : ℝ) (2 / 3) ≤ 1 / 48 ∧
      136 / C ≤ Real.sqrt d := by
  have hCast : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLimit₃ : Tendsto (fun d : ℕ => Real.log d / Real.rpow (d : ℝ) (3 : ℕ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℕ))).tendsto_div_nhds_zero.comp hCast
  simp only [Real.rpow_eq_pow, Real.rpow_natCast] at hLimit₃
  have hLimit₂ : Tendsto (fun d : ℕ => Real.log d / Real.rpow (d : ℝ) (2 / 3))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero.comp hCast
  have hLog := (Real.tendsto_log_atTop.comp hCast).eventually_ge_atTop 1
  have hCube : ∀ᶠ d : ℕ in atTop, 200 ≤ (d : ℝ) ^ 3 := by
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < (3 : ℕ)) 200
  have hRoot : ∀ᶠ d : ℕ in atTop, 136 / C ≤ Real.sqrt d := by
    simpa only [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow] using
      eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 1 / 2) (136 / C)
  filter_upwards [eventually_ge_atTop 49, hLog, hCube,
    hLimit₃.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 600)),
    eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 2 / 3) 8,
    hLimit₂.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 48)), hRoot]
    with d hLarge hLog hCube hSmall₃ hPower hSmall₂ hRoot
  exact ⟨hLarge, hLog, hCube, hSmall₃.le, hPower, hSmall₂.le, hRoot⟩

theorem gradualClassCountingEntropy_le_dimension {n d : ℕ} {a₃ C : ℝ}
    (hn : 49 ≤ n) (hd : 49 ≤ d) (hdn : d ≤ n) (ha : 0 < a₃)
    (hSmall : a₃ ≤ 1 / 65536) (hC : 0 < C) (hLogN : 1 ≤ Real.log n)
    (hLower : C * Real.log n ≤ (d : ℝ)) (hLogD : 1 ≤ Real.log d)
    (hCube : 200 ≤ (d : ℝ) ^ 3) (hRatio₃ : Real.log d / (d : ℝ) ^ 3 ≤ 1 / 600)
    (hPower : 8 ≤ Real.rpow (d : ℝ) (2 / 3))
    (hRatio₂ : Real.log d / Real.rpow (d : ℝ) (2 / 3) ≤ 1 / 48)
    (hRoot : 136 / C ≤ Real.sqrt d) :
    gradualClassCountingEntropy n d a₃ ≤ n := by
  have hnPos : 0 < n := by omega
  have hdPos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hCubePos : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos hdR 3
  have hInv₃ : 1 / (d : ℝ) ^ 3 ≤ 1 / 200 :=
    (div_le_iff₀ hCubePos).mpr (by linarith)
  have hBulk : 25 / (d : ℝ) ^ 3 * (1 + Real.log (1 + (d : ℝ) ^ 3 / 25)) ≤ 1 / 4 := by
    apply (gradualClass_bulk_cost_bound (by omega : 2 ≤ d)).trans
    rw [show 25 / (d : ℝ) ^ 3 * (1 + 3 * Real.log d) =
      25 * (1 / (d : ℝ) ^ 3 + 3 * (Real.log d / (d : ℝ) ^ 3)) by ring]
    linarith
  have hRPos : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos hdR _
  have hInv₂ : 1 / Real.rpow (d : ℝ) (2 / 3) ≤ 1 / 8 :=
    (div_le_iff₀ hRPos).mpr (by linarith)
  have hMiddle : 1 / Real.rpow (d : ℝ) (2 / 3) *
      (1 + Real.log (1 + 49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3))) ≤ 1 / 4 := by
    apply (gradualClass_middle_cost_bound hd hLogD).trans
    rw [show 1 / Real.rpow (d : ℝ) (2 / 3) * (1 + 6 * Real.log d) =
      1 / Real.rpow (d : ℝ) (2 / 3) + 6 * (Real.log d / Real.rpow (d : ℝ) (2 / 3)) by ring]
    linarith
  have hRootPos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hInitial : 2 / Real.rpow (d : ℝ) (3 / 2) *
      (1 + Real.log (1 + (49 / 2 : ℝ) * (n : ℝ) ^ 12 * Real.rpow (d : ℝ) (3 / 2))) ≤ 1 / 4 := by
    apply (gradualClass_initial_cost_bound hn hdPos hdn hC hLogN hLower).trans
    apply (div_le_iff₀ (mul_pos hC hRootPos)).mpr
    have h := (div_le_iff₀ hC).mp hRoot
    nlinarith
  rw [gradualClassCountingEntropy_eq hnPos hdPos ha]
  apply (mul_le_mul_of_nonneg_left (show _ ≤ (1 : ℝ) by
    have hTail := gradualClass_tail_cost_small ha hSmall
    linarith) (Nat.cast_nonneg n)).trans_eq
  ring

theorem eventually_sourceGradualApproxClasses_exp_n_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ k : ℕ, 0 < k →
        (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
        (canonicalApproxFamily k (sourceGradual n d L a₃)).Finite ∧
        (coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))).Finite ∧
        (Nat.card {m : Multiset ℂ // m ∈
          coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} : ℝ) ≤
          Real.exp (n : ℝ) := by
  have haHalf : a₃ ≤ 1 / 2 := by linarith
  have hLogN := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [eventually_sourceGradualApproxClasses_entropy_uniform ha haHalf hC σ,
    eventually_degree_property_uniform hC (eventually_gradualClass_degree_budgets C),
    eventually_source_kernel_conditions_uniform hC (1 + σ), eventually_ge_atTop 49, hLogN]
    with n hCount hBudgets hConditions hn hLogN
  intro d hBand L hL k hk hRange
  have hCon := hConditions d hBand.1 hBand.2
  obtain ⟨hd, hLogD, hCube, hRatio₃, hPower, hRatio₂, hRoot⟩ := hBudgets d hBand.1
  have hdPos : 0 < d := by omega
  have hD₄ : d ≤ d ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hdPos (by decide : 1 ≤ 4)
  have hdn : d ≤ n := hD₄.trans (by have h := hCon.dimension_fourth; omega)
  obtain ⟨hFamily, hClasses, hEntropy⟩ := hCount d hBand L hL k hk hRange
  refine ⟨hFamily, hClasses, hEntropy.trans (Real.exp_le_exp.mpr ?_)⟩
  exact gradualClassCountingEntropy_le_dimension hn hd hdn ha hSmall hC hLogN hBand.1
    hLogD hCube hRatio₃ hPower hRatio₂ hRoot

theorem eventually_restrictedGradualApproxClasses_exp_n_uniform {a₃ C : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 0 < C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ k : ℕ, 0 < k →
        (k : ℝ) ≤ Real.sqrt n / Real.rpow (d : ℝ) (3 / 2) →
        ∀ X : Set (Fin n → ℂ), X ⊆ sourceGradual n d L a₃ →
          (canonicalApproxFamily k X).Finite ∧
          (Nat.card {m : Multiset ℂ // m ∈
            coordinateMultisetClasses (canonicalApproxFamily k X)} : ℝ) ≤ Real.exp (n : ℝ) := by
  filter_upwards [eventually_sourceGradualApproxClasses_exp_n_uniform ha hSmall hC σ] with n hn
  intro d hBand L hL k hk hRange X hX
  obtain ⟨hFamily, hClasses, hCount⟩ := hn d hBand L hL k hk hRange
  have hSub := canonicalApproxFamily_mono k hX
  refine ⟨hFamily.subset hSub, ?_⟩
  have hNat := canonicalApproxClasses_card_le k hX hClasses
  have hReal : (Nat.card {m : Multiset ℂ // m ∈
      coordinateMultisetClasses (canonicalApproxFamily k X)} : ℝ) ≤
      Nat.card {m : Multiset ℂ // m ∈
        coordinateMultisetClasses (canonicalApproxFamily k (sourceGradual n d L a₃))} := by
    exact_mod_cast hNat
  exact hReal.trans hCount

end CircularLaw
