import CircularLaw.LLYSecondSteepNet
import CircularLaw.SmallSetPowerBound
import CircularLaw.LLYThirdGridBudgets

/-!
# Entropy of the actual layered second-class net

First-prefix support choices pay the power bound, and each grid retains
its separate coordinate cap. The final support pays the density entropy.
The weighted geometric-scale sum removes the number-of-scales factor.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def llySecondNetCountBound (n d ℓ r k₁ k₂ : ℕ) (δ : ℝ) : ℕ :=
  (∏ i : Fin (r + 1), (n + 1) ^ llySecondLayerSize ℓ r k₁ i *
    llyGridCount (llyThirdNetResolution d) ((6 * (d : ℝ)) ^ (r + 1 - i.val)) ^
      llySecondLayerSize ℓ r k₁ i) *
    ((smallCoordinateSets n (k₂ - 1)).card * llyGridCount (llyThirdNetResolution d) 1 ^ (k₂ - 1)) *
      llyGridCount (llyThirdNetResolution d * d) δ

def llySecondNetCountEntropy (n d ℓ r k₁ k₂ : ℕ) (a δ : ℝ) : ℝ :=
  (∑ i : Fin (r + 1), (llySecondLayerSize ℓ r k₁ i : ℝ) *
    (Real.log (n + 1 : ℕ) +
      Real.log (llyGridCount (llyThirdNetResolution d) ((6 * (d : ℝ)) ^ (r + 1 - i.val))))) +
    (n : ℝ) * smallSetEntropy a +
      (k₂ - 1 : ℕ) * Real.log (llyGridCount (llyThirdNetResolution d) 1) +
        Real.log (llyGridCount (llyThirdNetResolution d * d) δ)

theorem lly_second_layer_weighted_cost (ℓ r k₁ : ℕ) :
    (∑ i : Fin (r + 1), llySecondLayerSize ℓ r k₁ i * (r + 2 - i.val)) =
      llyFirstNetScaleCost ℓ r k₁ :=
  Fin.sum_univ_eq_sum_range (fun i => (llyFirstRank ℓ k₁ (i + 1) - 1) * (r + 2 - i)) (r + 1)

theorem lly_second_layer_support_cost {ℓ r k₁ : ℕ} (hℓ : 2 ≤ ℓ) (hRank : ℓ ^ r ≤ k₁) :
    (∑ i : Fin (r + 1), llySecondLayerSize ℓ r k₁ i) ≤ 5 * k₁ := by
  have hWeighted := lly_first_net_scale_cost_bound hℓ hRank
  rw [← lly_second_layer_weighted_cost] at hWeighted
  have hTwo : 2 * (∑ i : Fin (r + 1), llySecondLayerSize ℓ r k₁ i) ≤
      ∑ i : Fin (r + 1), llySecondLayerSize ℓ r k₁ i * (r + 2 - i.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : 2 ≤ r + 2 - i.val := by omega
    nlinarith [Nat.mul_le_mul_left (llySecondLayerSize ℓ r k₁ i) hi]
  omega

theorem lly_second_layer_support_cost_rank_one {ℓ r : ℕ} (hℓ : 0 < ℓ) :
    (∑ i : Fin (r + 1), llySecondLayerSize ℓ r 1 i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hPower : 1 ≤ ℓ ^ (i.val + 1) := by have h := pow_pos hℓ (i.val + 1); omega
  simp only [llySecondLayerSize, llyFirstRank, min_eq_right hPower, Nat.sub_self]

theorem lly_second_layer_grid_log {d r : ℕ} (hd : 0 < d)
    (hLog : Real.log 484 ≤ Real.log (d : ℝ)) (i : Fin (r + 1)) :
    Real.log (llyGridCount (llyThirdNetResolution d) ((6 * (d : ℝ)) ^ (r + 1 - i.val))) ≤
      4 * (r + 2 - i.val : ℕ) * Real.log (d : ℝ) := by
  have hPow : 1 ≤ (6 * (d : ℝ)) ^ (r + 1 - i.val) :=
    one_le_pow₀ (by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
  have hCount := lly_grid_count_log_bound hd (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (llyThirdNetResolution_upper hd) hPow
  rw [Real.log_pow, Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
    (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)] at hCount
  have h121 : Real.log 121 ≤ Real.log (d : ℝ) :=
    (Real.log_le_log (by norm_num : (0 : ℝ) < 121) (by norm_num : (121 : ℝ) ≤ 484)).trans hLog
  have hSix : Real.log 6 ≤ Real.log (d : ℝ) :=
    (Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 484)).trans hLog
  have hScaled := mul_le_mul_of_nonneg_left hSix
    (Nat.cast_nonneg (r + 1 - i.val) : (0 : ℝ) ≤ (r + 1 - i.val : ℕ))
  have hLogNonneg := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hCast : ((r + 1 - i.val : ℕ) : ℝ) + 1 = (r + 2 - i.val : ℕ) := by
    exact_mod_cast (show (r + 1 - i.val) + 1 = r + 2 - i.val by omega)
  nlinarith

theorem lly_second_net_card_product_le_count (n d ℓ r k₁ k₂ : ℕ) (δ : ℝ) :
    (llySecondNonconstantNet n d ℓ r k₁ k₂ (llyThirdNetResolution d)).card *
      (meanCorrectedScalarNet (llyThirdNetResolution d) d 0 δ).card ≤
        llySecondNetCountBound n d ℓ r k₁ k₂ δ := by
  have hNet := lly_second_net_card_le n d ℓ r k₁ k₂ (llyThirdNetResolution d)
  have hScalar := meanCorrectedScalarNet_card_le (llyThirdNetResolution d) d 0 δ
  apply Nat.mul_le_mul (hNet.trans ?_) (by simpa only [zero_add] using hScalar)
  apply Nat.mul_le_mul
  · apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i _
    apply Nat.mul_le_mul (smallCoordinateSets_card_power _ _)
    exact Nat.pow_le_pow_left (gridBox_card_le _ _) _
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (gridBox_card_le _ _) _)

theorem lly_second_net_count_entropy_bound {n d ℓ r k₁ k₂ : ℕ} {a δ : ℝ}
    (ha : 0 < a) (haOne : a ≤ 1) (hSecond : ((k₂ - 1 : ℕ) : ℝ) ≤ a * n) :
    (llySecondNetCountBound n d ℓ r k₁ k₂ δ : ℝ) ≤
      Real.exp (llySecondNetCountEntropy n d ℓ r k₁ k₂ a δ) := by
  have hLayers : ((∏ i : Fin (r + 1), (n + 1) ^ llySecondLayerSize ℓ r k₁ i *
      llyGridCount (llyThirdNetResolution d) ((6 * (d : ℝ)) ^ (r + 1 - i.val)) ^
        llySecondLayerSize ℓ r k₁ i : ℕ) : ℝ) =
      Real.exp (∑ i : Fin (r + 1), (llySecondLayerSize ℓ r k₁ i : ℝ) *
        (Real.log (n + 1 : ℕ) +
          Real.log (llyGridCount (llyThirdNetResolution d) ((6 * (d : ℝ)) ^ (r + 1 - i.val))))) := by
    rw [Nat.cast_prod, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_mul, natural_power_eq_exp_log (by omega : 0 < n + 1),
      natural_power_eq_exp_log (llyGridCount_pos _ _), ← Real.exp_add]
    congr 1
    ring
  have hSupport := smallCoordinateSets_card_density ha haOne hSecond
  unfold llySecondNetCountBound
  rw [Nat.cast_mul, Nat.cast_mul, hLayers, Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hSupport (Nat.cast_nonneg _)) (Real.exp_pos _).le)
      (Nat.cast_nonneg _)).trans_eq
  rw [natural_power_eq_exp_log (llyGridCount_pos _ _) (k₂ - 1),
    ← Real.exp_log (by exact_mod_cast llyGridCount_pos (llyThirdNetResolution d * d) δ :
      (0 : ℝ) < llyGridCount (llyThirdNetResolution d * d) δ)]
  simp only [← Real.exp_add]
  congr 1
  unfold llySecondNetCountEntropy
  ring

theorem lly_grid_count_log_mono_radius (k : ℕ) {R S : ℝ} (hRS : R ≤ S) :
    Real.log (llyGridCount k R) ≤ Real.log (llyGridCount k S) := by
  have hRadius : gridBoxRadius k R ≤ gridBoxRadius k S := by
    unfold gridBoxRadius
    apply Nat.add_le_add_right
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left hRS (Nat.cast_nonneg k)
  have hCount : llyGridCount k R ≤ llyGridCount k S :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hRadius) 1) 2
  exact Real.log_le_log (by exact_mod_cast llyGridCount_pos k R : (0 : ℝ) < llyGridCount k R)
    (by exact_mod_cast hCount)

theorem lly_second_net_count_entropy_simplified {n d ℓ r k₁ k₂ : ℕ} {a δ : ℝ}
    (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ))
    (hℓ : 2 ≤ ℓ) (hRank : ℓ ^ r ≤ k₁) (hδSmall : δ ≤ 1 / 100) :
    llySecondNetCountEntropy n d ℓ r k₁ k₂ a δ ≤
      5 * (k₁ : ℝ) * Real.log (n + 1 : ℕ) +
        (40 * (k₁ : ℝ) + 3 * (k₂ - 1 : ℕ) + 5) * Real.log (d : ℝ) +
          (n : ℝ) * smallSetEntropy a := by
  have hLogNonneg := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)
  have hLogN := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega) :
    (1 : ℝ) ≤ (n + 1 : ℕ))
  have hSupport : (∑ i : Fin (r + 1), (llySecondLayerSize ℓ r k₁ i : ℝ)) ≤ 5 * (k₁ : ℝ) := by
    exact_mod_cast lly_second_layer_support_cost hℓ hRank
  have hSupportCost := mul_le_mul_of_nonneg_right hSupport hLogN
  rw [Finset.sum_mul] at hSupportCost
  have hWeighted : (llyFirstNetScaleCost ℓ r k₁ : ℝ) ≤ 10 * (k₁ : ℝ) := by
    exact_mod_cast lly_first_net_scale_cost_bound hℓ hRank
  have hGrid : (∑ i : Fin (r + 1), (llySecondLayerSize ℓ r k₁ i : ℝ) *
      Real.log (llyGridCount (llyThirdNetResolution d) ((6 * (d : ℝ)) ^ (r + 1 - i.val)))) ≤
      4 * (llyFirstNetScaleCost ℓ r k₁ : ℝ) * Real.log (d : ℝ) := by
    rw [← lly_second_layer_weighted_cost, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (lly_second_layer_grid_log hd hLog i)
      (Nat.cast_nonneg (llySecondLayerSize ℓ r k₁ i) : (0 : ℝ) ≤ llySecondLayerSize ℓ r k₁ i)
    push_cast
    nlinarith only [h]
  have hGridBudget := mul_le_mul_of_nonneg_right hWeighted hLogNonneg
  have hBase := (lly_grid_count_log_mono_radius (llyThirdNetResolution d)
    (by norm_num : (1 : ℝ) ≤ 4 / 3)).trans (lly_third_base_grid_log hd hLog)
  have hBaseCost := mul_le_mul_of_nonneg_left hBase
    (Nat.cast_nonneg (k₂ - 1) : (0 : ℝ) ≤ (k₂ - 1 : ℕ))
  have hScalar := (lly_grid_count_log_mono_radius (llyThirdNetResolution d * d)
    (by linarith : δ ≤ 1 / 3 + δ)).trans (lly_third_scalar_grid_log hd hLog hδSmall)
  unfold llySecondNetCountEntropy
  simp only [mul_add, Finset.sum_add_distrib]
  nlinarith only [hSupportCost, hGrid, hGridBudget, hBaseCost, hScalar]

theorem lly_second_net_card_product_entropy_bound {n d ℓ r k₁ k₂ : ℕ} {a δ : ℝ}
    (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ))
    (hℓ : 2 ≤ ℓ) (hRank : ℓ ^ r ≤ k₁) (hδSmall : δ ≤ 1 / 100)
    (ha : 0 < a) (haOne : a ≤ 1) (hSecond : ((k₂ - 1 : ℕ) : ℝ) ≤ a * n) :
    ((llySecondNonconstantNet n d ℓ r k₁ k₂ (llyThirdNetResolution d)).card : ℝ) *
      (meanCorrectedScalarNet (llyThirdNetResolution d) d 0 δ).card ≤
        Real.exp (5 * (k₁ : ℝ) * Real.log (n + 1 : ℕ) +
          (40 * (k₁ : ℝ) + 3 * (k₂ - 1 : ℕ) + 5) * Real.log (d : ℝ) +
            (n : ℝ) * smallSetEntropy a) := by
  have hCard : ((llySecondNonconstantNet n d ℓ r k₁ k₂ (llyThirdNetResolution d)).card : ℝ) *
      (meanCorrectedScalarNet (llyThirdNetResolution d) d 0 δ).card ≤
        llySecondNetCountBound n d ℓ r k₁ k₂ δ := by
    exact_mod_cast lly_second_net_card_product_le_count n d ℓ r k₁ k₂ δ
  exact (hCard.trans (lly_second_net_count_entropy_bound ha haOne hSecond)).trans
    (Real.exp_le_exp.mpr (lly_second_net_count_entropy_simplified hd hLog hℓ hRank hδSmall))

theorem lly_second_net_card_product_absorbed {n d ℓ r k₁ k₂ : ℕ} {a δ : ℝ}
    (hd : 0 < d) (hLog : Real.log 484 ≤ Real.log (d : ℝ))
    (hℓ : 2 ≤ ℓ) (hRank : ℓ ^ r ≤ k₁) (hδSmall : δ ≤ 1 / 100)
    (ha : 0 < a) (haOne : a ≤ 1) (hSecond : ((k₂ - 1 : ℕ) : ℝ) ≤ a * n)
    (hBudget : 5 * (k₁ : ℝ) * Real.log (n + 1 : ℕ) +
      (40 * (k₁ : ℝ) + 3 * (k₂ - 1 : ℕ) + 5) * Real.log (d : ℝ) +
        (n : ℝ) * smallSetEntropy a ≤ (k₁ : ℝ) * d / 32) :
    ((llySecondNonconstantNet n d ℓ r k₁ k₂ (llyThirdNetResolution d)).card : ℝ) *
      (meanCorrectedScalarNet (llyThirdNetResolution d) d 0 δ).card ≤
        Real.exp ((k₁ : ℝ) * d / 32) :=
  (lly_second_net_card_product_entropy_bound hd hLog hℓ hRank hδSmall ha haOne hSecond).trans
    (Real.exp_le_exp.mpr hBudget)

end CircularLaw
