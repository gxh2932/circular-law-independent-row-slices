import CircularLaw.RareSteepNetAdjoint
import CircularLaw.LLYThirdNetCardinalityUniform

/-!
# The actual first source rank supplies the rare-coefficient estimate

The ceiling is retained. The first-rank-one case uses d/n <= 1/2;
otherwise the ceiling is controlled by twice its defining positive
ratio. The resulting fixed-vector bound holds at the actual source
first/second ranks throughout the degree window.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_first_rank_degree_lower {n d : ℕ} (hd : 0 < d) (a : ℝ) :
    a * llySourceEpsilon n d * n ≤ (llySourceFirstRank n d a : ℝ) * d := by
  have hCeil : a * llySourceEpsilon n d * n / d ≤ (llySourceFirstRank n d a : ℝ) := Nat.le_ceil _
  exact (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp hCeil

theorem lly_source_first_rank_rare_density {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (hDegree : 2 * d ≤ n) {C a : ℝ} (hC : 1920000 ≤ C)
    (hLower : C * Real.log (n : ℝ) ≤ d) (ha : 0 < a) (haOne : a ≤ 1) :
    (llySourceFirstRank n d a : ℝ) * ((d : ℝ) / n) ≤ 1 / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hFirst := lly_source_first_rank_pos hn hd ha
  by_cases hOne : llySourceFirstRank n d a = 1
  · rw [hOne, Nat.cast_one, one_mul]
    apply (div_le_iff₀ hnR).mpr
    have hReal : 2 * (d : ℝ) ≤ n := by exact_mod_cast hDegree
    linarith
  · have hRatio : 1 < a * llySourceEpsilon n d * n / d := by
      by_contra h
      have hCeil : llySourceFirstRank n d a ≤ 1 := Nat.ceil_le.mpr
        (by simpa only [Nat.cast_one] using le_of_not_gt h)
      omega
    have hCeil := Nat.ceil_lt_add_one (by
      have hEps := (lly_source_epsilon_pos hn hd).le
      positivity : 0 ≤ a * llySourceEpsilon n d * n / d)
    change (llySourceFirstRank n d a : ℝ) < a * llySourceEpsilon n d * n / d + 1 at hCeil
    have hUpper : (llySourceFirstRank n d a : ℝ) ≤ 2 * (a * llySourceEpsilon n d * n / d) := by
      linarith
    have hScaled := mul_le_mul_of_nonneg_right hUpper (div_pos hdR hnR).le
    have hCancel : (2 * (a * llySourceEpsilon n d * n / d)) * ((d : ℝ) / n) =
        2 * a * llySourceEpsilon n d := by field_simp
    rw [hCancel] at hScaled
    have hEps := lly_source_epsilon_upper hn hd (by norm_num : (0 : ℝ) ≤ 1 / 200)
      (by nlinarith : (48 : ℝ) ≤ C * (1 / 200 : ℝ) ^ 2) hLower
    have hCoeff : a * llySourceEpsilon n d ≤ 1 / 200 := by
      have h := mul_le_mul_of_nonneg_right haOne (lly_source_epsilon_pos hn hd).le
      nlinarith
    linarith

theorem eventually_lly_source_second_gap_rare_adjoint_decay {C a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ u : Fin n → ℂ, ∀ w ζ : ℂ,
        (∀ j : Fin n, llySourceSecondRank n d a₂ ≤ j.val →
          (2 / 3 : ℝ) + orderedNorm u j < orderedNormAt u (llySourceFirstRank n d a₁)) →
            uniformProbability (fun rows : RowSliceMatrix n d =>
              ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
                (WithLp.toLp 2 (fun i => u i + w))‖ ≤
                  Real.sqrt ((llySourceFirstRank n d a₁ : ℝ) * d) / 30) ≤
                    Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 16) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_degree_property_uniform hCPos eventually_rare_row_slice_conditioning_cost,
    eventually_degree_property_uniform hCPos
      (eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) (4096 * a₂))]
      with n hn hCosts hPowers
  intro d hLower hDegree u w ζ hGap
  obtain ⟨hd, hCost⟩ := hCosts d hLower
  have hRare := lly_source_first_rank_rare_density hn hd hDegree hC hLower ha₁ ha₁One
  have hk₁ := lly_source_first_rank_pos hn hd ha₁
  have hk₁n := lly_source_first_rank_le_dimension hn hd ha₁.le ha₁One (by linarith) hLower
  have hRankDegree : (llySourceFirstRank n d a₁ : ℝ) * d ≤ (n : ℝ) / 2 := by
    rw [← mul_div_assoc] at hRare
    have h := (div_le_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mp hRare
    linarith
  have hFirstHalf : (llySourceFirstRank n d a₁ : ℝ) ≤ (n : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left (by exact_mod_cast hd : (1 : ℝ) ≤ d)
      (Nat.cast_nonneg (α := ℝ) (llySourceFirstRank n d a₁))
    linarith
  have hSecondHalf := lly_source_second_rank_small_density (n := n) hd ha₂.le (hPowers d hLower)
  have hFit : llySourceSecondRank n d a₂ + llySourceFirstRank n d a₁ ≤ n := by
    have hReal : (llySourceSecondRank n d a₂ : ℝ) + llySourceFirstRank n d a₁ ≤ n := by
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hReal
  have hRanks : llySourceFirstRank n d a₁ ≤ llySourceSecondRank n d a₂ := by
    by_contra h
    have hSelf := hGap ⟨llySourceFirstRank n d a₁ - 1, by omega⟩ (by
      change llySourceSecondRank n d a₂ ≤ llySourceFirstRank n d a₁ - 1
      omega)
    rw [orderedNormAt_eq u hk₁ hk₁n] at hSelf
    linarith
  exact row_slice_ordered_rare_adjoint_norm_decay hd hDegree hk₁ hRanks hFit hRare hCost u w ζ
    (by simpa only [orderedNormAt_eq u hk₁ hk₁n] using hGap)

end CircularLaw
