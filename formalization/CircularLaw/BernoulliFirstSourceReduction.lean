import CircularLaw.BernoulliFirstSourceProbability

/-!
# Source-parameter Bernoulli reduction to the second and third steep classes

The first-class probability is supplied by the checked source-parameter
bounds. Both the square adjoint and each omitted-row kernel therefore
retain only the two later classes as probability obligations.
-/

noncomputable section
open Classical MeasureTheory Filter

namespace CircularLaw

theorem eventually_bernoulli_lly_source_steep_right_probability_le_later {C A a : ℝ}
    (hC : 1920000 ≤ C) (hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFailureCost : (2 / uniqueWitnessRate) * (A + 1) ≤ C)
    (hUpperCost : (1 / bernoulliDegreeUpperRate) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ k₂ k₃ : ℕ, ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) → ∀ δ ρ : ℝ,
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYSteepAlmostRightFailure ζ sample d (llySourceStride n d)
            (llySourceScale n d a) (llySourceFirstRank n d a) k₂ k₃ δ ρ
            ((llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n)} ≤
              2 * (n : ℝ) ^ (-A) +
              (sparseBernoulliMatrixLaw n d).real {sample |
                BernoulliLLYLaterSteepAlmostRightFailure ζ sample d (llySourceStride n d)
                  (llySourceScale n d a) (llySourceFirstRank n d a) k₂ k₃ δ ρ
                  ((llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n)} := by
  filter_upwards [eventually_bernoulli_lly_first_source_retained_failure_probability
    hC hEntropyCost hFailureCost hUpperCost ha haOne] with n hFirst
  intro d hLower hdn k₂ k₃ ζ hShift δ ρ
  let ℓ := llySourceStride n d
  let r := llySourceScale n d a
  let k₁ := llySourceFirstRank n d a
  let τ := (llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYSteepAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ⊆
      {sample | BernoulliLLYFirstSteepRetainedFailure Finset.univ ζ sample d ℓ r k₁ τ} ∪
        {sample | BernoulliLLYLaterSteepAlmostRightFailure ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} := by
    intro sample hFail
    obtain ⟨x, hUnit, hAlmost, hSteep, hNorm⟩ := hFail
    rcases hSteep with (hFirst | hSecond) | hThird
    · exact Or.inl ⟨x, hUnit, hFirst, (retained_shifted_bernoulli_norm_le_full Finset.univ ζ sample x).trans hNorm⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inl hSecond, hNorm⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inr hThird, hNorm⟩
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (hFirst d hLower hdn Finset.univ
    (by simp only [Finset.card_univ, Fintype.card_fin]; nlinarith [Nat.cast_nonneg (α := ℝ) n])
    ζ hShift) (le_refl _)

theorem eventually_bernoulli_lly_source_steep_adjoint_probability_le_later {C A a : ℝ}
    (hC : 1920000 ≤ C) (hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFailureCost : (2 / uniqueWitnessRate) * (A + 1) ≤ C)
    (hUpperCost : (1 / bernoulliDegreeUpperRate) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ k₂ k₃ : ℕ, ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) → ∀ δ ρ : ℝ,
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYSteepAlmostAdjointFailure ζ sample d (llySourceStride n d)
            (llySourceScale n d a) (llySourceFirstRank n d a) k₂ k₃ δ ρ
            ((llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n)} ≤
              2 * (n : ℝ) ^ (-A) +
              (sparseBernoulliMatrixLaw n d).real {sample |
                BernoulliLLYLaterSteepAlmostAdjointFailure ζ sample d (llySourceStride n d)
                  (llySourceScale n d a) (llySourceFirstRank n d a) k₂ k₃ δ ρ
                  ((llySourceAlmostRadius n d a / Real.sqrt n) * llySourceAlmostRadius n d a / Real.sqrt n)} := by
  filter_upwards [eventually_bernoulli_lly_source_steep_right_probability_le_later
    hC hEntropyCost hFailureCost hUpperCost ha haOne] with n hRight
  intro d hLower hdn k₂ k₃ ζ hShift δ ρ
  rw [bernoulli_lly_steep_almost_adjoint_probability_eq_right,
    bernoulli_lly_later_steep_almost_adjoint_probability_eq_right]
  exact hRight d hLower hdn k₂ k₃ (star ζ) (by simpa only [norm_star] using hShift) δ ρ

theorem eventually_bernoulli_lly_source_steep_kernel_probability_le_later {C A a : ℝ}
    (hC : 1920000 ≤ C) (hEntropyCost : 16 / uniqueWitnessRate ^ 2 ≤ C)
    (hFailureCost : (2 / uniqueWitnessRate) * (A + 1) ≤ C)
    (hUpperCost : (1 / bernoulliDegreeUpperRate) * (A + 1) ≤ C)
    (ha : 0 < a) (haOne : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → d ≤ n →
      ∀ k₂ k₃ : ℕ, ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ (d : ℝ) → ∀ δ ρ : ℝ,
        (sparseBernoulliMatrixLaw n d).real {sample |
          BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d (llySourceStride n d)
            (llySourceScale n d a) (llySourceFirstRank n d a) k₂ k₃ δ ρ} ≤
              2 * (n : ℝ) ^ (-A) +
              (sparseBernoulliMatrixLaw n d).real {sample |
                BernoulliLLYLaterSteepLeaveOneOutKernelFailure ζ sample i d (llySourceStride n d)
                  (llySourceScale n d a) (llySourceFirstRank n d a) k₂ k₃ δ ρ} := by
  filter_upwards [eventually_bernoulli_lly_first_source_leave_one_out_kernel_probability
    hC hEntropyCost hFailureCost hUpperCost ha haOne] with n hFirst
  intro d hLower hdn k₂ k₃ i ζ hShift δ ρ
  let ℓ := llySourceStride n d
  let r := llySourceScale n d a
  let k₁ := llySourceFirstRank n d a
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliLLYSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} ⊆
      {sample | BernoulliLLYFirstSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁} ∪
        {sample | BernoulliLLYLaterSteepLeaveOneOutKernelFailure ζ sample i d ℓ r k₁ k₂ k₃ δ ρ} := by
    intro sample hFail
    obtain ⟨x, hUnit, hAlmost, hSteep, hKernel⟩ := hFail
    rcases hSteep with (hFirst | hSecond) | hThird
    · exact Or.inl ⟨x, hUnit, hFirst, hKernel⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inl hSecond, hKernel⟩
    · exact Or.inr ⟨x, hUnit, hAlmost, Or.inr hThird, hKernel⟩
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (hFirst d hLower hdn i ζ hShift) (le_refl _)

end CircularLaw
