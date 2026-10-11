import CircularLaw.LLYSecondSteepAdjointProbability
import CircularLaw.LLYThirdSteepNormalization

/-!
# Normalization of actual unit vectors in the second steep class

The exclusion of all first jumps bounds the norm by the first-rank
modulus. Dividing by that modulus carries every actual unit-vector
failure to the checked normalized finite-net event.
-/

noncomputable section
open Classical

namespace CircularLaw

def llySecondSteepNormConstant (n d r : ℕ) : ℝ :=
  Real.sqrt n * (6 * (d : ℝ)) ^ (r + 1)

theorem lly_second_steep_norm_bound {n d ℓ r k₁ k₂ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hFit : k₁ ≤ ℓ ^ (r + 1))
    (x : EuclideanSpace ℂ (Fin n)) (hx : (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂) :
    ‖x‖ ≤ llySecondSteepNormConstant n d r * orderedNormAt (fun j => x j) k₁ := by
  apply (euclidean_norm_le_first_ordered hn x).trans
  have h := mul_le_mul_of_nonneg_left
    (lly_not_first_steep_chain hk₁ hFit (fun j => x j) hx.1) (Real.sqrt_nonneg n)
  simpa only [llySecondSteepNormConstant, mul_assoc] using h

def llySecondUnitAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ : ℕ) (s : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∧
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ s

theorem lly_second_unit_adjoint_normalization {n d ℓ r k₁ k₂ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {s : ℝ} (hs : 0 ≤ s) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hFail : llySecondUnitAdjointFailure ζ rows ℓ r k₁ k₂ s) :
    llySecondNormalizedAdjointFailure ζ rows ℓ r k₁ k₂
      (llySecondSteepNormConstant n d r * s) := by
  obtain ⟨x, hUnit, hSecond, hSmall⟩ := hFail
  let q := orderedNormAt (fun j => x j) k₁
  have hq : 0 < q := lt_of_le_of_lt
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (orderedNormAt_nonneg _ _)) hSecond.2
  have hScaleBound : q⁻¹ ≤ llySecondSteepNormConstant n d r := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hq).mpr
    have h := lly_second_steep_norm_bound hn hk₁ hFit x hSecond
    rwa [hUnit] at h
  let z : ℂ := (q : ℂ)⁻¹
  have hz : z ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')
  have hNormZ : ‖z‖ = q⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  refine ⟨z • (fun j => x j), (lly_second_steep_smul_iff z hz _).mpr hSecond, ?_, ?_⟩
  · rw [orderedNormAt_smul, hNormZ]
    exact inv_mul_cancel₀ hq.ne'
  · have hVector : (WithLp.toLp 2 (z • (fun j => x j)) : EuclideanSpace ℂ (Fin n)) = z • x := by
      ext j
      rfl
    rw [hVector, map_smul, norm_smul, hNormZ]
    exact (mul_le_mul_of_nonneg_left hSmall (inv_nonneg.mpr hq.le)).trans
      (mul_le_mul_of_nonneg_right hScaleBound hs)

theorem lly_second_unit_adjoint_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    {A δ s : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ) (hs : 0 ≤ s) (ζ : ℂ)
    (hBudget : llySecondSteepNormConstant n d r * s +
      ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
          (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llySecondUnitAdjointFailure ζ rows ℓ r k₁ k₂ s) ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  apply (uniformProbability_mono (fun rows hFail =>
    lly_second_unit_adjoint_normalization (by omega : 0 < n) hk₁ hFirstFit hs ζ rows hFail)).trans
  exact lly_second_adjoint_probability_absorbed hn hd hDegree hℓ hk hk₁ hRanks hRanksFit
    hFirstFit hRare hCost hA hDegreeLog hδ hδSmall hGrid hResolution ζ hBudget hEntropy

end CircularLaw
