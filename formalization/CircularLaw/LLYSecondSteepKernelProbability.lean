import CircularLaw.RareRowSliceRightAction
import CircularLaw.MeanCorrectedRetainedNet
import CircularLaw.LLYSecondSteepNormalization

/-!
# Retained right-kernel bounds for the actual second steep class

The direct fixed-degree right-action bound charges the same layered
vector net and mean-corrected scalar net as the adjoint argument. The
centered norm failure is proved separately. Normalizing the first
ordered rank covers every second-class kernel vector.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_second_net_retained_right_action_union_probability {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk₁ : 0 < k₁)
    (hRanks : k₁ ≤ k₂) (hFit : k₂ + k₁ ≤ n)
    (hRare : k₁ = 1 ∨ (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∃ w ∈ C,
        ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30) ≤
      ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) * C.card *
        Real.exp (-(k₁ : ℝ) * d / 16) :=
  rare_steep_net_retained_right_action_union_probability hn hd hDegree hk₁ hRanks hFit hRare
    I hRows _ (fun u hu => lly_second_net_ordered_gap hk₁ hRanks hFit u hu) C ζ

def llySecondNormalizedRightFailure {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (ℓ r k₁ k₂ : ℕ) (τ : ℝ) : Prop :=
  ∃ x : Fin n → ℂ, x ∈ llySecondSteep d ℓ r k₁ k₂ ∧ orderedNormAt x k₁ = 1 ∧
    ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin (WithLp.toLp 2 x)‖ ≤ τ

def llySecondRetainedKernelFailure {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (ℓ r k₁ k₂ : ℕ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∧
    (retainedShiftedMatrix I ζ rows).toEuclideanLin x = 0

theorem lly_second_retained_kernel_normalization {n d ℓ r k₁ k₂ : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hFail : llySecondRetainedKernelFailure I ζ rows ℓ r k₁ k₂) :
    llySecondNormalizedRightFailure I ζ rows ℓ r k₁ k₂ 0 := by
  obtain ⟨x, hx, hKernel⟩ := hFail
  let q := orderedNormAt (fun j => x j) k₁
  have hq : 0 < q := lt_of_le_of_lt
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (orderedNormAt_nonneg _ _)) hx.2
  let z : ℂ := (q : ℂ)⁻¹
  have hz : z ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')
  have hNormZ : ‖z‖ = q⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  refine ⟨z • (fun j => x j), (lly_second_steep_smul_iff z hz _).mpr hx, ?_, ?_⟩
  · rw [orderedNormAt_smul, hNormZ]
    exact inv_mul_cancel₀ hq.ne'
  · have hVector : (WithLp.toLp 2 (z • (fun j => x j)) : EuclideanSpace ℂ (Fin n)) = z • x := by
      ext j
      rfl
    rw [hVector, map_smul, hKernel, smul_zero, norm_zero]

theorem lly_second_retained_right_finite_cover {n d ℓ r k₁ k₂ k : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {B δ τ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3)
    (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ) (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hNorm : RetainedCenteredNormBound I rows B)
    (hBudget : τ + ((B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤
        Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hFail : llySecondNormalizedRightFailure I ζ rows ℓ r k₁ k₂ τ) :
    ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k,
      ∃ w ∈ meanCorrectedScalarNet k d 0 δ,
        ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30 := by
  obtain ⟨x, hx, hNormalized, hSmall⟩ := hFail
  obtain ⟨u, hu, hApprox⟩ := lly_second_normalized_net_approximation_degree hd hℓ hk hk₁ hk₂
    hk₁n hk₂n hFit hδSmall hGrid hResolution x hx hNormalized
  obtain ⟨w, hw, hError⟩ := mean_corrected_scalar_net_retained_cover (by omega : 0 < n)
    hk hd I rows ζ hB hδ hNorm x u 0 (by norm_num : ‖(0 : ℂ)‖ ≤ (0 : ℝ)) hApprox
  refine ⟨u, hu, w, hw, ?_⟩
  have hDecomp : (WithLp.toLp 2 (fun i => u i + w) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (fun i => (x i + 0) - (u i + w)) := by
    ext i
    change u i + w = x i - ((x i + 0) - (u i + w))
    ring
  rw [hDecomp, map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add hSmall hError).trans hBudget)

theorem lly_second_retained_right_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : k₁ = 1 ∨ (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (ζ : ℂ)
    (hBudget : τ + ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) *
      (2 * Real.sqrt n * δ) + (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) *
        Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondNormalizedRightFailure I ζ rows ℓ r k₁ k₂ τ) ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  have hCover : ∀ rows : RowSliceMatrix n d,
      llySecondNormalizedRightFailure I ζ rows ℓ r k₁ k₂ τ →
      ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant A) ∨
        ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∃ w ∈ meanCorrectedScalarNet k d 0 δ,
          ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
            (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30 := by
    intro rows hFail
    by_cases hNorm : RetainedCenteredNormBound I rows (rowSliceComplexNormConstant A)
    · exact Or.inr (lly_second_retained_right_finite_cover hd hℓ hk hk₁ (by omega : 0 < k₂)
        (by omega : k₁ ≤ n) (by omega : k₂ ≤ n) hFirstFit (rowSliceComplexNormConstant_nonneg hA)
        hδ hδSmall hGrid hResolution I ζ rows hNorm hBudget hFail)
    · exact Or.inl hNorm
  apply (uniformProbability_mono hCover).trans ((uniformProbability_or_le _ _).trans ?_)
  apply add_le_add (retainedCenteredNormBound_failure_polynomial hn hd (by omega : d ≤ n)
    hA hDegreeLog I)
  apply (lly_second_net_retained_right_action_union_probability hn hd hDegree hk₁ hRanks hRanksFit
    hRare I hRows _ ζ).trans
  apply (mul_le_mul_of_nonneg_right hEntropy (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem lly_second_retained_kernel_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : k₁ = 1 ∨ (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    {A δ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (ζ : ℂ)
    (hBudget : ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
        (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondRetainedKernelFailure I ζ rows ℓ r k₁ k₂) ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  apply (uniformProbability_mono (fun rows hFail =>
    lly_second_retained_kernel_normalization I ζ rows hFail)).trans
  exact lly_second_retained_right_probability_absorbed hn hd hDegree hℓ hk hk₁ hRanks hRanksFit
    hFirstFit hRare hA hDegreeLog hδ hδSmall hGrid hResolution I hRows ζ
      (by simpa only [zero_add] using hBudget) hEntropy

end CircularLaw
