import CircularLaw.LLYSecondSteepNet
import CircularLaw.MeanCorrectedScalarNet
import CircularLaw.RareSteepNetAdjoint

/-!
# Adjoint probability bounds for the actual second LLY steep class

Every normalized vector is covered by the constructed layered net.
Mean correction uses a separate scalar grid. The probability charges
the actual two cardinalities and the centered-operator failure. The
rank, approximation and entropy budgets remain explicit here.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_second_net_ordered_gap {n d ℓ r k₁ k₂ k : ℕ}
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hFit : k₂ + k₁ ≤ n)
    (u : Fin n → ℂ) (hu : u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k) :
    ∀ j : Fin n, k₂ ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm u j < orderedNorm u ⟨k₁ - 1, by omega⟩ := by
  have h := lly_second_net_geometry u hu
  rw [orderedNormAt_eq u hk₁ (by omega : k₁ ≤ n)] at h
  intro j hj
  have hZero : orderedNorm u j = 0 := by
    have hOrder : (⟨k₂ - 1, by omega⟩ : Fin n) ≤ j :=
      Fin.le_iff_val_le_val.mpr (by change k₂ - 1 ≤ j.val; omega)
    have hNorm := orderedNorm_antitone u hOrder
    rw [← orderedNormAt_eq u (by omega : 0 < k₂) (by omega : k₂ ≤ n), h.2] at hNorm
    exact le_antisymm hNorm (orderedNorm_nonneg u j)
  simpa only [hZero, add_zero] using h.1

theorem lly_second_net_adjoint_union_probability {n d ℓ r k₁ k₂ k : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk₁ : 0 < k₁)
    (hRanks : k₁ ≤ k₂) (hFit : k₂ + k₁ ≤ n)
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∃ w ∈ C,
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30) ≤
      ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) * C.card *
        Real.exp (-(k₁ : ℝ) * d / 16) :=
  rare_steep_net_adjoint_union_probability hd hDegree hk₁ hRanks hFit hRare hCost
    _ (fun u hu => lly_second_net_ordered_gap hk₁ hRanks hFit u hu) C ζ

def llySecondNormalizedAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ : ℕ) (τ : ℝ) : Prop :=
  ∃ x : Fin n → ℂ, x ∈ llySecondSteep d ℓ r k₁ k₂ ∧ orderedNormAt x k₁ = 1 ∧
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin (WithLp.toLp 2 x)‖ ≤ τ

theorem lly_second_adjoint_finite_cover {n d ℓ r k₁ k₂ k : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {B δ τ : ℝ} (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3)
    (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ) (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ B)
    (hBudget : τ + ((B + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (B + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤
        Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hFail : llySecondNormalizedAdjointFailure ζ rows ℓ r k₁ k₂ τ) :
    ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k,
      ∃ w ∈ meanCorrectedScalarNet k d 0 δ,
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30 := by
  obtain ⟨x, hx, hNormalized, hSmall⟩ := hFail
  obtain ⟨u, hu, hApprox⟩ := lly_second_normalized_net_approximation_degree hd hℓ hk hk₁ hk₂
    hk₁n hk₂n hFit hδSmall hGrid hResolution x hx hNormalized
  have hn : 0 < n := by omega
  obtain ⟨w, hw, hError⟩ := mean_corrected_scalar_net_adjoint_cover hn hk hd rows ζ hδ hNorm
    x u 0 (by norm_num : ‖(0 : ℂ)‖ ≤ (0 : ℝ)) hApprox
  refine ⟨u, hu, w, hw, ?_⟩
  have hDecomp : (WithLp.toLp 2 (fun i => u i + w) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (fun i => (x i + 0) - (u i + w)) := by
    ext i
    change u i + w = x i - ((x i + 0) - (u i + w))
    ring
  rw [hDecomp, map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add hSmall hError).trans hBudget)

theorem lly_second_adjoint_probability_polynomial {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ) (ζ : ℂ)
    (hBudget : τ + ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
        (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondNormalizedAdjointFailure ζ rows ℓ r k₁ k₂ τ) ≤
      (n : ℝ) ^ (-A) +
        ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
          (meanCorrectedScalarNet k d 0 δ).card * Real.exp (-(k₁ : ℝ) * d / 16) := by
  have hCover : ∀ rows : RowSliceMatrix n d,
      llySecondNormalizedAdjointFailure ζ rows ℓ r k₁ k₂ τ →
      rowSliceComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ∨
        ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∃ w ∈ meanCorrectedScalarNet k d 0 δ,
          ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
            (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30 := by
    intro rows hFail
    by_cases hGood : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤
        rowSliceComplexNormConstant A * Real.sqrt d
    · exact Or.inr (lly_second_adjoint_finite_cover hd hℓ hk hk₁ (by omega : 0 < k₂)
        (by omega : k₁ ≤ n) (by omega : k₂ ≤ n) hFirstFit hδ hδSmall hGrid hResolution
        ζ rows hGood hBudget hFail)
    · exact Or.inl (lt_of_not_ge hGood)
  apply (uniformProbability_mono hCover).trans ((uniformProbability_or_le _ _).trans ?_)
  exact add_le_add
    (rowSlice_complex_norm_failure_polynomial (by omega : 0 < n) hn le_rfl hd
      (by omega : d ≤ n) hA hDegreeLog)
    (lly_second_net_adjoint_union_probability hd hDegree hk₁ hRanks hRanksFit hRare hCost _ ζ)

theorem lly_second_adjoint_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ) (ζ : ℂ)
    (hBudget : τ + ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
        (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondNormalizedAdjointFailure ζ rows ℓ r k₁ k₂ τ) ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  apply (lly_second_adjoint_probability_polynomial hn hd hDegree hℓ hk hk₁ hRanks hRanksFit
    hFirstFit hRare hCost hA hDegreeLog hδ hδSmall hGrid hResolution ζ hBudget).trans
  apply add_le_add le_rfl
  apply (mul_le_mul_of_nonneg_right hEntropy (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end CircularLaw
