import CircularLaw.LLYSecondSteepKernelProbability
import CircularLaw.LLYSecondSourcePolynomial
import CircularLaw.LLYLeaveOneOutReduction

/-!
# The second-class right-kernel estimate at the actual source parameters

The literal ceiling rank is either one or has rare density at most
one hundredth. All source grid, entropy, rank-fit and centered norm
budgets are discharged uniformly in the logarithmic degree window.
The conclusion includes arbitrary deterministic retained sets and
every leave-one-out row set.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_first_rank_switching_density {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C a : ℝ} (hC : 1920000 ≤ C) (hLower : C * Real.log (n : ℝ) ≤ d)
    (ha : 0 < a) (haOne : a ≤ 1) :
    llySourceFirstRank n d a = 1 ∨
      (llySourceFirstRank n d a : ℝ) * ((d : ℝ) / n) ≤ 1 / 100 := by
  by_cases hOne : llySourceFirstRank n d a = 1
  · exact Or.inl hOne
  · right
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hFirst := lly_source_first_rank_pos hn hd ha
    have hRatio : 1 < a * llySourceEpsilon n d * n / d := by
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

theorem eventually_lly_second_source_retained_kernel_probability {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            llySecondRetainedKernelFailure I ζ rows (llySourceStride n d) (llySourceScale n d a₁)
              (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)) ≤
                (n : ℝ) ^ (-A) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_second_source_grid_adjoint_error_small hCPos
      (rowSliceComplexNormConstant_nonneg hA) ha₁,
    eventually_lly_second_source_net_count_absorbed hC ha₁ ha₂,
    eventually_degree_property_uniform hCPos
      (eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) (4096 * a₂)),
    eventually_lly_source_second_rank_size_uniform ha₂]
      with n hn hApproximations hCounts hPowers hSizes
  intro d hLower hDegree I hRows ζ hShift
  have hdn : d ≤ n := by omega
  obtain ⟨hd, hδSmall, hErrors⟩ := hApproximations d hLower hdn
  have hk₁ := lly_source_first_rank_pos hn hd ha₁
  have hk₁n := lly_source_first_rank_le_dimension hn hd ha₁.le ha₁One (by linarith) hLower
  have hSecondSize := hSizes d hd hdn
  have hk₂ : 0 < llySourceSecondRank n d a₂ := by
    have hLowerSecond := lly_source_second_rank_density_lower hSecondSize
    have hReal : (0 : ℝ) < llySourceSecondRank n d a₂ := by linarith
    exact_mod_cast hReal
  have hSecondHalf := lly_source_second_rank_small_density (n := n) hd ha₂.le (hPowers d hLower)
  by_cases hRanks : llySourceFirstRank n d a₁ ≤ llySourceSecondRank n d a₂
  · have hDensity := lly_source_first_rank_rare_density hn hd hDegree hC hLower ha₁ ha₁One
    have hFirstDegree : (llySourceFirstRank n d a₁ : ℝ) * d ≤ (n : ℝ) / 2 := by
      rw [← mul_div_assoc] at hDensity
      have h := (div_le_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mp hDensity
      linarith
    have hFirstHalf : (llySourceFirstRank n d a₁ : ℝ) ≤ (n : ℝ) / 2 := by
      have h := mul_le_mul_of_nonneg_left (by exact_mod_cast hd : (1 : ℝ) ≤ d)
        (Nat.cast_nonneg (α := ℝ) (llySourceFirstRank n d a₁))
      linarith
    have hRanksFit : llySourceSecondRank n d a₂ + llySourceFirstRank n d a₁ ≤ n := by
      have hReal : (llySourceSecondRank n d a₂ : ℝ) + llySourceFirstRank n d a₁ ≤ n := by
        linarith [Nat.cast_nonneg (α := ℝ) n]
      exact_mod_cast hReal
    have hSwitching := lly_source_first_rank_switching_density hn hd hC hLower ha₁ ha₁One
    have hRare : llySourceFirstRank n d a₁ = 1 ∨
        (llySourceFirstRank n d a₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 4 := by
      rcases hSwitching with hOne | hRare
      · exact Or.inl hOne
      · exact Or.inr (by linarith)
    have hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
      have hScaled := mul_le_mul_of_nonneg_right hNormCost (Real.log_natCast_nonneg n)
      nlinarith
    exact lly_second_retained_kernel_probability_absorbed hn hd hDegree
      (by have h := lly_source_stride_ge_two hn hd hC hLower; omega)
      (llyThirdNetResolution_pos hd) hk₁ hRanks hRanksFit
      (lly_source_scale_ranks hn hd hC hLower ha₁).2 hRare hA hDegreeLog
      (by unfold llyThirdNetError; positivity) (by linarith : llyThirdNetError d < 1 / 3)
      (llyThirdNetResolution_error hd) le_rfl I hRows ζ
      ((hErrors ζ hShift).trans (by
        have h := Real.sqrt_nonneg ((llySourceFirstRank n d a₁ : ℝ) * d)
        linarith)) (hCounts d hLower)
  · have hEmpty : ∀ rows : RowSliceMatrix n d,
        ¬llySecondRetainedKernelFailure I ζ rows (llySourceStride n d) (llySourceScale n d a₁)
          (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂) := by
      intro rows hFail
      obtain ⟨x, hx, _⟩ := hFail
      exact lly_second_steep_empty_of_reversed_ranks hd hk₂ (by omega) hk₁n _ hx
    letI : IsEmpty {rows : RowSliceMatrix n d //
      llySecondRetainedKernelFailure I ζ rows (llySourceStride n d) (llySourceScale n d a₁)
        (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)} :=
      ⟨fun rows => hEmpty rows.val rows.property⟩
    have hZero : uniformProbability (fun rows : RowSliceMatrix n d =>
        llySecondRetainedKernelFailure I ζ rows (llySourceStride n d) (llySourceScale n d a₁)
          (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)) = 0 := by simp [uniformProbability]
    rw [hZero]
    positivity

theorem eventually_lly_second_source_retained_kernel_probability_polynomial {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            llySecondRetainedKernelFailure I ζ rows (llySourceStride n d) (llySourceScale n d a₁)
              (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)) ≤ (n : ℝ) ^ (-A) := by
  have hAOne : 0 ≤ A + 1 := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_second_source_retained_kernel_probability hC hAOne
      (by linarith : A + 1 + 3 ≤ 9 * C) ha₁ ha₁One ha₂,
    eventually_lly_source_first_rank_exponential_polynomial ha₁ hAOne,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 1)]
      with n hn hProbability hExponents hDegrees
  intro d hLower hDegree I hRows ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hExp := hExponents d hd (by omega : d ≤ n)
  apply (hProbability d hLower hDegree I hRows ζ hShift).trans
  exact (by nlinarith only [hExp] :
    (n : ℝ) ^ (-(A + 1)) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) ≤
      2 * (n : ℝ) ^ (-(A + 1))).trans (two_shifted_polynomial_rates_le hn A)

theorem eventually_lly_second_source_leave_one_out_kernel_probability {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ∃ x : EuclideanSpace ℂ (Fin n),
            (fun j => x j) ∈ llySecondSteep d (llySourceStride n d) (llySourceScale n d a₁)
              (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂) ∧
            ∀ j : Fin n, j ≠ i → (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j = 0) ≤
          (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_second_source_retained_kernel_probability_polynomial hC hA hNormCost
      ha₁ ha₁One ha₂] with n hn hProbability
  intro d hLower hDegree i ζ hShift
  have hCard : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hRows : (n : ℝ) / 2 ≤ (Finset.univ.erase i).card := by
    rw [hCard]
    have hReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply (uniformProbability_mono ?_).trans
    (hProbability d hLower hDegree (Finset.univ.erase i) hRows ζ hShift)
  intro rows hFail
  obtain ⟨x, hx, hKernel⟩ := hFail
  refine ⟨x, hx, ?_⟩
  ext j
  rw [retained_shifted_slice_apply_eq_full]
  exact hKernel j.val (Finset.mem_erase.mp j.property).1

end CircularLaw
