import CircularLaw.BernoulliLaterSourceProbability
import CircularLaw.BernoulliFirstSourceReduction

/-!
# Polynomial Bernoulli later-class probabilities at the actual source radius

The checked exponential remainders and the centered-norm exception each
fit an arbitrary polynomial rate. The resulting estimates cover both the
full shifted adjoint and each actual leave-one-out kernel.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem eventually_bernoulli_second_source_radius_retained_polynomial {C A a₁ a₂ : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ I : Finset (Fin n), (4 / 5 : ℝ) * n ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          (sparseBernoulliMatrixLaw n d).real {sample |
            BernoulliSecondUnitRetainedFailure (d := d) I ζ sample
              (llySourceStride n d) (llySourceScale n d a₁)
              (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
              ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
                Real.sqrt n)} ≤ (n : ℝ) ^ (-A) := by
  have hCPos : 0 < C := by linarith
  have hAOne : 0 ≤ A + 1 := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_bernoulli_second_source_retained_probability hC hAOne
      (by linarith : A + 1 + 3 ≤ 9 * C) ha₁ ha₁One ha₂,
    eventually_lly_source_first_rank_exponential_polynomial ha₁ hAOne]
      with n hn hDegrees hProbability hExponents
  intro d hLower hDegree I hRows ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hExp := hExponents d hd (by omega : d ≤ n)
  apply (hProbability d hLower hDegree (llySourceAlmostRadius n d a₁)
    (lly_source_almost_radius_pos (by omega : 0 < n) hd a₁).le
    (lly_source_almost_radius_third (by omega : 0 < n) hd a₁) I hRows ζ hShift).trans
  exact (by nlinarith only [hExp] :
    (n : ℝ) ^ (-(A + 1)) + Real.exp (-(llySourceFirstRank n d a₁ : ℝ) * d / 32) ≤
      2 * (n : ℝ) ^ (-(A + 1))).trans (two_shifted_polynomial_rates_le hn A)

theorem eventually_bernoulli_third_source_radius_retained_polynomial {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ I : Finset (Fin n), (n : ℝ) / 2 ≤ I.card →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
          (sparseBernoulliMatrixLaw n d).real {sample |
            BernoulliThirdUnitRetainedFailure (d := d) I ζ sample
              (llySourceStride n d) (llySourceScale n d a₁)
              (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
              (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)
              ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
                Real.sqrt n)} ≤ (n : ℝ) ^ (-A) := by
  have hCPos : 0 < C := by linarith
  have hAOne : 0 ≤ A + 1 := by linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 2),
    eventually_bernoulli_third_source_retained_probability hC hAOne
      (by linarith : A + 1 + 3 ≤ 9 * C) ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα,
    eventually_dimension_log_degree_exponential_polynomial hAOne]
      with n hn hDegrees hProbability hExponents
  intro d hLower hDegree I hRows ζ hShift
  have hdTwo := hDegrees d hLower
  have hd : 0 < d := by omega
  have hExp := hExponents d hdTwo
  apply (hProbability d hLower hDegree (llySourceAlmostRadius n d a₁)
    (lly_source_almost_radius_pos (by omega : 0 < n) hd a₁).le
    (lly_source_almost_radius_third (by omega : 0 < n) hd a₁) I hRows ζ hShift).trans
  exact (by nlinarith only [hExp] :
    (n : ℝ) ^ (-(A + 1)) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 64) ≤
      2 * (n : ℝ) ^ (-(A + 1))).trans (two_shifted_polynomial_rates_le hn A)

theorem eventually_bernoulli_later_source_right_polynomial {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYLaterSteepAlmostRightFailure ζ sample d
            (llySourceStride n d) (llySourceScale n d a₁)
            (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
            (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
              Real.sqrt n)} ≤ 2 * (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_bernoulli_second_source_radius_retained_polynomial
    hC hA hNormCost ha₁ ha₁One ha₂,
    eventually_bernoulli_third_source_radius_retained_polynomial
      hC hA hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα] with n hSecond hThird
  intro d hLower hDegree ζ hShift
  have hRows : (4 / 5 : ℝ) * n ≤ (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hRowsHalf : (n : ℝ) / 2 ≤ (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hUnion := (measureReal_union_le _ _).trans
    (add_le_add (hSecond d hLower hDegree Finset.univ hRows ζ hShift)
      (hThird d hLower hDegree Finset.univ hRowsHalf ζ hShift))
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (hUnion.trans_eq (by ring))
  rintro sample ⟨x, hUnit, hAlmost, hClass, hSmall⟩
  have hRetained := (retained_shifted_bernoulli_norm_le_full Finset.univ ζ sample x).trans hSmall
  rcases hClass with hClass | hClass
  · exact Or.inl ⟨x, hUnit, hClass, hRetained⟩
  · exact Or.inr ⟨x, hUnit, hClass, hAlmost, hRetained⟩

theorem eventually_bernoulli_later_source_adjoint_polynomial {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYLaterSteepAlmostAdjointFailure ζ sample d
            (llySourceStride n d) (llySourceScale n d a₁)
            (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
            (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
              Real.sqrt n)} ≤ 2 * (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_bernoulli_later_source_right_polynomial
    hC hA hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα] with n hRight
  intro d hLower hDegree ζ hShift
  rw [bernoulli_lly_later_steep_almost_adjoint_probability_eq_right]
  exact hRight d hLower hDegree (star ζ) (by simpa only [norm_star] using hShift)

theorem eventually_bernoulli_later_source_kernel_polynomial {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 4 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYLaterSteepLeaveOneOutKernelFailure ζ sample i d
            (llySourceStride n d) (llySourceScale n d a₁)
            (llySourceFirstRank n d a₁) (llySourceSecondRank n d a₂)
            (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)} ≤ 2 * (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_ge_atTop 100,
    eventually_degree_property_uniform (by linarith : 0 < C) (eventually_ge_atTop 1),
    eventually_bernoulli_second_source_radius_retained_polynomial
      hC hA hNormCost ha₁ ha₁One ha₂,
    eventually_bernoulli_third_source_radius_retained_polynomial
      hC hA hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small hFirstCost hα] with n hn hDegrees hSecond hThird
  intro d hLower hDegree i ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  have hRows := one_row_deleted_retained_card hn i
  have hRowsFour : (4 / 5 : ℝ) * n ≤ (Finset.univ.erase i).card := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hRowsHalf : (n : ℝ) / 2 ≤ (Finset.univ.erase i).card := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hτ : 0 ≤ (llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
      Real.sqrt n := by
    have hρ := lly_source_almost_radius_pos (by omega : 0 < n) hd a₁
    positivity
  have hUnion := (measureReal_union_le _ _).trans
    (add_le_add (hSecond d hLower hDegree (Finset.univ.erase i) hRowsFour ζ hShift)
      (hThird d hLower hDegree (Finset.univ.erase i) hRowsHalf ζ hShift))
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (hUnion.trans_eq (by ring))
  rintro sample ⟨x, hUnit, hAlmost, hClass, hKernel⟩
  have hZero : (retainedShiftedBernoulliMatrix (Finset.univ.erase i) ζ sample).toEuclideanLin x = 0 := by
    ext j
    rw [retained_shifted_bernoulli_apply_eq_full]
    exact hKernel j.val (Finset.mem_erase.mp j.property).1
  have hSmall : ‖(retainedShiftedBernoulliMatrix (Finset.univ.erase i) ζ sample).toEuclideanLin x‖ ≤
      (llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ / Real.sqrt n := by
    rw [hZero, norm_zero]
    exact hτ
  rcases hClass with hClass | hClass
  · exact Or.inl ⟨x, hUnit, hClass, hSmall⟩
  · exact Or.inr ⟨x, hUnit, hClass, hAlmost, hSmall⟩

end CircularLaw
