import CircularLaw.LLYThirdSteepKernelProbability
import CircularLaw.SeparatedBlockCoefficientDecay
import CircularLaw.LLYSourceRadius
import CircularLaw.LLYSecondSourcePolynomial
import CircularLaw.LLYLeaveOneOutReduction

/-!
# Third-class almost-constant right kernels at the literal source parameters

The rounded ranks, grid, entropy and approximation budgets are all
discharged uniformly over the degree window. The proved source radius
then supplies a polynomial bound for every retained and leave-one-out
kernel event with the actual almost-constant condition.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_third_rank_quarter {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (haQuarter : a ≤ 1 / 4) :
    4 * llySourceThirdRank n a ≤ n := by
  have hUpper := lly_source_third_rank_upper (n := n) ha
  have hScaled := mul_le_mul_of_nonneg_right haQuarter (Nat.cast_nonneg (α := ℝ) n)
  have hReal : (4 : ℝ) * llySourceThirdRank n a ≤ n := by linarith
  exact_mod_cast hReal

theorem eventually_dimension_log_degree_exponential_polynomial {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 2 ≤ d →
      Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) ≤ (n : ℝ) ^ (-A) := by
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1)
      (div_pos hLogTwo (by norm_num : (0 : ℝ) < 64)) 0 (A + 1) (by linarith)]
      with n hn hBudget
  intro d hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLogN := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have hLogD : Real.log 2 ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hd)
  have hLogScaled := mul_le_mul_of_nonneg_left hLogD (Nat.cast_nonneg (α := ℝ) n)
  simp only [zero_add, Real.rpow_eq_pow, Real.rpow_one] at hBudget
  rw [Real.rpow_def_of_pos hnR]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem eventually_lly_third_source_almost_retained_kernel_probability {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ρ : ℝ, 0 ≤ ρ →
        llyThirdSteepNormConstant n d (llySourceScale n d a₁) * ρ ≤
          llyThirdNetError d * Real.sqrt n →
        ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
          ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
            uniformProbability (fun rows : RowSliceMatrix n d =>
              llyThirdAlmostUnitRetainedKernelFailure I ζ rows (llySourceStride n d)
                (llySourceScale n d a₁) (llySourceFirstRank n d a₁)
                (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) α ρ) ≤
                  (n : ℝ) ^ (-A) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_source_rank_validity hC ha₁ ha₁One ha₂ ha₃ (by linarith : a₃ ≤ 1 / 2),
    eventually_lly_third_source_retained_net_probability_cost hC ha₁.le ha₁One ha₂ ha₃.le ha₃Small hFirstCost,
    eventually_degree_property_uniform hCPos
      (eventually_lly_third_grid_adjoint_error_small (rowSliceComplexNormConstant_nonneg hA)),
    eventually_lly_source_third_rank_density ha₃ hα]
      with n hn hRanks hCosts hBudgets hDensity
  intro d hLower hDegree ρ hρ hRadius I hRows ζ hShift
  have hdn : d ≤ n := by omega
  obtain ⟨hd, _, hk₁, hk₁n, hk₂, hk₃, hRanks, _⟩ := hRanks d hLower hdn
  obtain ⟨hScaleLower, hScaleFit⟩ := lly_source_scale_ranks hn hd hC hLower ha₁
  obtain ⟨_, hδSmall, hErrors⟩ := hBudgets d hLower
  have hδ : 0 ≤ llyThirdNetError d := by unfold llyThirdNetError; positivity
  have hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
    have hScaled := mul_le_mul_of_nonneg_right hNormCost
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))
    nlinarith
  have hTail := lly_source_third_rank_quarter (n := n) ha₃.le (by linarith : a₃ ≤ 1 / 4)
  apply (uniformProbability_mono (fun rows hFail =>
    lly_third_almost_unit_retained_kernel_normalization (by omega : 0 < n) hk₁
      (by omega : llySourceThirdRank n a₃ ≤ n) hScaleFit hρ hDensity hRadius I ζ rows hFail)).trans
  have hProbability := lly_third_almost_retained_right_probability hn hd hDegree
    (llyThirdNetResolution_pos hd) hk₁ hk₂ hk₃ hk₁n hRanks hTail hScaleFit hA hDegreeLog
    hδ hδSmall (llyThirdNetResolution_error hd) I hRows ζ (τ := 0) (by
      have hError := hErrors n ζ hShift
      linarith [Real.sqrt_nonneg n])
  exact hProbability.trans (add_le_add le_rfl
    (hCosts d (llySourceScale n d a₁) hLower hdn hScaleLower I hRows))

theorem eventually_lly_third_source_radius_retained_kernel_probability {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            llyThirdAlmostUnitRetainedKernelFailure I ζ rows (llySourceStride n d)
              (llySourceScale n d a₁) (llySourceFirstRank n d a₁)
              (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)) ≤
                (n : ℝ) ^ (-A) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 1),
    eventually_lly_third_source_almost_retained_kernel_probability hC hA hNormCost
      ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα] with n hn hDegrees hProbability
  intro d hLower hDegree I hRows ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  exact hProbability d hLower hDegree (llySourceAlmostRadius n d a₁)
    (lly_source_almost_radius_pos hn hd a₁).le (lly_source_almost_radius_third hn hd a₁) I hRows ζ hShift

theorem eventually_lly_third_source_radius_retained_kernel_probability_polynomial {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            llyThirdAlmostUnitRetainedKernelFailure I ζ rows (llySourceStride n d)
              (llySourceScale n d a₁) (llySourceFirstRank n d a₁)
              (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)) ≤
                (n : ℝ) ^ (-A) := by
  have hAOne : 0 ≤ A + 1 := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_third_source_radius_retained_kernel_probability hC hAOne
      (by linarith : A + 1 + 3 ≤ 9 * C) ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα,
    eventually_dimension_log_degree_exponential_polynomial hAOne,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 2)]
      with n hn hProbability hExponents hDegrees
  intro d hLower hDegree I hRows ζ hShift
  have hExp := hExponents d (hDegrees d hLower)
  apply (hProbability d hLower hDegree I hRows ζ hShift).trans
  exact (by nlinarith only [hExp] :
    (n : ℝ) ^ (-(A + 1)) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) ≤
      2 * (n : ℝ) ^ (-(A + 1))).trans (two_shifted_polynomial_rates_le hn A)

theorem eventually_lly_third_source_leave_one_out_almost_kernel_probability {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
            (fun j => x j) ∈ llyThirdSteep d (llySourceStride n d) (llySourceScale n d a₁)
              (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) ∧
            ¬sourceNonAlmostConstant α (llySourceAlmostRadius n d a₁) x ∧
              ∀ j : Fin n, j ≠ i → (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j = 0) ≤
          (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_lly_third_source_radius_retained_kernel_probability_polynomial hC hA hNormCost
      ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα] with n hn hProbability
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
  obtain ⟨x, hUnit, hx, hAlmost, hKernel⟩ := hFail
  refine ⟨x, hUnit, hx, hAlmost, ?_⟩
  ext j
  rw [retained_shifted_slice_apply_eq_full]
  exact hKernel j.val (Finset.mem_erase.mp j.property).1

end CircularLaw
