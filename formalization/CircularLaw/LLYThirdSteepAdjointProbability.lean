import CircularLaw.LLYThirdSteepNet
import CircularLaw.MeanCorrectedScalarNet
import CircularLaw.OrderedAdjointSmallBall

/-!
# Actual adjoint probability bounds for the LLY third class

The finite cover is constructed from the actual almost-constant vector.
The probability estimate charges the centered-norm failure, the literal
net cardinalities, and the selected-row Bernoulli conditioning loss.
Only deterministic radius and parameter budgets remain in this bound.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lly_third_net_ordered_gap {n d r k₁ k₂ k₃ k : ℕ}
    (hk₂ : 0 < k₂) (hRanks : k₂ ≤ k₃) (hFit : k₃ + k₂ ≤ n)
    (u : Fin n → ℂ) (hu : u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k) :
    ∀ j : Fin n, k₃ ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm u j < orderedNorm u ⟨k₂ - 1, by omega⟩ := by
  have h := lly_third_net_geometry u hu
  rw [orderedNormAt_eq u hk₂ (by omega : k₂ ≤ n)] at h
  intro j hj
  have hZero : orderedNorm u j = 0 := by
    have hOrder : (⟨k₃ - 1, by omega⟩ : Fin n) ≤ j :=
      Fin.le_iff_val_le_val.mpr (by change k₃ - 1 ≤ j.val; omega)
    have hNorm := orderedNorm_antitone u hOrder
    rw [← orderedNormAt_eq u (by omega : 0 < k₃) (by omega : k₃ ≤ n), h.2] at hNorm
    exact le_antisymm hNorm (orderedNorm_nonneg u j)
  simpa only [hZero, add_zero] using h.1

theorem lly_third_net_fixed_vector_adjoint {n d r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk₂ : 0 < k₂)
    (hRanks : k₂ ≤ k₃) (hFit : k₃ + k₂ ≤ n)
    (u : Fin n → ℂ) (hu : u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k) (w ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt n / 3) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
        (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
          Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n := by
  have hBound := row_slice_ordered_adjoint_small_ball hd hDegree hk₂ hRanks hFit u w ζ
    (by norm_num : (0 : ℝ) < 1 / 3) (le_refl (1 : ℝ)) (by
      simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using
        lly_third_net_ordered_gap hk₂ hRanks hFit u hu)
  apply (uniformProbability_mono ?_).trans (by simpa only [one_pow, mul_one] using hBound)
  intro rows hSmall
  have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hSquare
  convert hSquare using 1
  ring

theorem lly_third_net_adjoint_union_probability {n d r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk₂ : 0 < k₂)
    (hRanks : k₂ ≤ k₃) (hFit : k₃ + k₂ ≤ n) (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k, ∃ w ∈ C,
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt n / 3) ≤
      ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) * C.card *
        ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
          (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
            Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n) := by
  apply (uniformProbability_finset_exists_le (llyThirdNonconstantNet n d r k₁ k₂ k₃ k) _).trans
  calc
    _ ≤ ∑ _u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
        (C.card : ℝ) * ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
          (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
            Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n) := by
      apply Finset.sum_le_sum
      intro u hu
      apply (uniformProbability_finset_exists_le C _).trans
      calc
        _ ≤ ∑ _w ∈ C, (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
            (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
              Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n :=
          Finset.sum_le_sum (fun w _ => lly_third_net_fixed_vector_adjoint hd hDegree hk₂ hRanks hFit u hu w ζ)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

def llyThirdNormalizedAlmostAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ k₃ : ℕ) (δ τ : ℝ) : Prop :=
  ∃ x : Fin n → ℂ, x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ∧ orderedNormAt x k₂ = 1 ∧
    ∃ c : ℂ, ∃ F : Finset (Fin n), n - k₃ < F.card ∧
      (∀ j ∈ F, ‖x j - c‖ ≤ δ) ∧
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin (WithLp.toLp 2 x)‖ ≤ τ

theorem lly_third_almost_adjoint_finite_cover {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hHalf : 2 * k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {B δ τ : ℝ} (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ B)
    (hBudget : τ + ((B + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (B + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3)
    (hFail : llyThirdNormalizedAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ τ) :
    ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
      ∃ w ∈ meanCorrectedScalarNet k d (1 / 3) δ,
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt n / 3 := by
  obtain ⟨x, hx, hNormalized, c, F, hMany, hClose, hSmall⟩ := hFail
  obtain ⟨u, hu, hApprox⟩ := lly_third_normalized_net_approximation hk hk₁ hk₂ hk₃ hk₁n hk₂n
    hHalf hFit hδSmall hGrid x hx hNormalized c F hMany hClose
  have hn : 0 < n := by omega
  have hCenter := lly_third_normalized_center_bound hk₃ hHalf x hx hNormalized c F hδSmall hMany hClose
  obtain ⟨w, hw, hError⟩ := mean_corrected_scalar_net_adjoint_cover hn hk hd rows ζ hδ hNorm
    (fun i => x i - c) u c hCenter hApprox
  refine ⟨u, hu, w, hw, ?_⟩
  have hDecomp : (WithLp.toLp 2 (fun i => u i + w) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (fun i => ((x i - c) + c) - (u i + w)) := by
    ext i
    change u i + w = x i - ((x i - c + c) - (u i + w))
    ring
  rw [hDecomp, map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add hSmall hError).trans hBudget)

theorem lly_third_almost_adjoint_probability_polynomial {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₁n : k₁ ≤ n)
    (hRanks : k₂ ≤ k₃) (hHalf : 2 * k₃ ≤ n) (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ) (ζ : ℂ)
    (hBudget : τ + ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
        (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyThirdNormalizedAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ τ) ≤
      (n : ℝ) ^ (-A) +
        ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) *
          (meanCorrectedScalarNet k d (1 / 3) δ).card *
            ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
              (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
                Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n) := by
  have hCover : ∀ rows : RowSliceMatrix n d,
      llyThirdNormalizedAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ τ →
      rowSliceComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ∨
        ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
          ∃ w ∈ meanCorrectedScalarNet k d (1 / 3) δ,
            ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
              (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt n / 3 := by
    intro rows hFail
    by_cases hGood : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤
        rowSliceComplexNormConstant A * Real.sqrt d
    · exact Or.inr (lly_third_almost_adjoint_finite_cover hd hk hk₁ hk₂ hk₃ hk₁n (by omega : k₂ ≤ n)
        hHalf hFirstFit hδ hδSmall hGrid ζ rows hGood hBudget hFail)
    · exact Or.inl (lt_of_not_ge hGood)
  apply (uniformProbability_mono hCover).trans ((uniformProbability_or_le _ _).trans ?_)
  exact add_le_add
    (rowSlice_complex_norm_failure_polynomial (by omega : 0 < n) hn le_rfl hd (by omega : d ≤ n) hA hDegreeLog)
    (lly_third_net_adjoint_union_probability hd hDegree hk₂ hRanks (by omega : k₃ + k₂ ≤ n) _ ζ)

end CircularLaw
