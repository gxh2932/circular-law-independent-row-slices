import CircularLaw.LLYThirdSteepAdjointProbability
import CircularLaw.SourceHomogeneity
import CircularLaw.InvertibilityDistanceGeometry

/-!
# Unit-vector third-class adjoint failure reaches the checked finite net

The actual LLY classes are homogeneous. The norm bound from their first
two exclusions controls normalization at the second rank and both the
almost-constant radius and the actual shifted-adjoint residual.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lly_first_steep_smul_iff {n d ℓ r k : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ llyFirstSteep d ℓ r k ↔ x ∈ llyFirstSteep d ℓ r k := by
  simp only [llyFirstSteep, Set.mem_setOf_eq, ordered_jump_smul_iff z hz]

theorem lly_second_steep_smul_iff {n d ℓ r k₁ k₂ : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ llySecondSteep d ℓ r k₁ k₂ ↔ x ∈ llySecondSteep d ℓ r k₁ k₂ := by
  simp only [llySecondSteep, Set.mem_setOf_eq, lly_first_steep_smul_iff z hz,
    ordered_jump_smul_iff z hz]

theorem lly_third_steep_smul_iff {n d ℓ r k₁ k₂ k₃ : ℕ} (z : ℂ) (hz : z ≠ 0) (x : Fin n → ℂ) :
    z • x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ↔ x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ := by
  simp only [llyThirdSteep, Set.mem_setOf_eq, lly_first_steep_smul_iff z hz,
    lly_second_steep_smul_iff z hz, ordered_jump_smul_iff z hz]

def llyThirdSteepNormConstant (n d r : ℕ) : ℝ :=
  Real.sqrt n * (6 * (d : ℝ)) ^ (r + 1) * (d : ℝ) ^ (3 / 4 : ℝ)

theorem lly_third_steep_norm_bound {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hFit : k₁ ≤ ℓ ^ (r + 1))
    (x : EuclideanSpace ℂ (Fin n)) (hx : (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃) :
    ‖x‖ ≤ llyThirdSteepNormConstant n d r * orderedNormAt (fun j => x j) k₂ := by
  have hMiddle : orderedNormAt (fun j => x j) k₁ ≤
      (d : ℝ) ^ (3 / 4 : ℝ) * orderedNormAt (fun j => x j) k₂ :=
    le_of_not_gt (fun h => hx.2.1 ⟨hx.1, h⟩)
  apply (euclidean_norm_le_first_ordered hn x).trans
  have hTop := lly_not_first_steep_chain hk₁ hFit (fun j => x j) hx.1
  have hScaled := mul_le_mul_of_nonneg_left hMiddle
    (by positivity : 0 ≤ (6 * (d : ℝ)) ^ (r + 1))
  have hBound := mul_le_mul_of_nonneg_left (hTop.trans hScaled) (Real.sqrt_nonneg n)
  convert hBound using 1
  unfold llyThirdSteepNormConstant
  ring

def llyThirdAlmostUnitAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ k₃ : ℕ) (α ρ s : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ∧ ¬sourceNonAlmostConstant α ρ x ∧
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ s

theorem lly_third_almost_unit_adjoint_normalization {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₃n : k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {α ρ δ s : ℝ} (hρ : 0 ≤ ρ) (hDensity : α * n ≤ k₃)
    (hRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n)
    (hs : 0 ≤ s) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hFail : llyThirdAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ s) :
    llyThirdNormalizedAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ
      (llyThirdSteepNormConstant n d r * s) := by
  obtain ⟨x, hUnit, hThird, hAlmost, hSmall⟩ := hFail
  let q := orderedNormAt (fun j => x j) k₂
  have hq : 0 < q := lt_of_le_of_lt
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (orderedNormAt_nonneg _ _)) hThird.2.2
  have hScaleBound : q⁻¹ ≤ llyThirdSteepNormConstant n d r := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hq).mpr
    have h := lly_third_steep_norm_bound hn hk₁ hFit x hThird
    rwa [hUnit] at h
  let z : ℂ := (q : ℂ)⁻¹
  have hz : z ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')
  have hNormZ : ‖z‖ = q⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  unfold sourceNonAlmostConstant at hAlmost
  push_neg at hAlmost
  obtain ⟨c, hc⟩ := hAlmost
  let F := Finset.univ.filter (fun j => ‖x j - c‖ ≤ ρ / Real.sqrt n)
  have hMany : n - k₃ < F.card := by
    have hReal : ((n - k₃ : ℕ) : ℝ) < F.card := by
      rw [Nat.cast_sub hk₃n]
      change (n : ℝ) - k₃ < F.card
      dsimp only [F] at *
      nlinarith only [hc, hDensity]
    exact_mod_cast hReal
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hCloseBound : q⁻¹ * (ρ / Real.sqrt n) ≤ δ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hRoot).mpr
    exact (mul_le_mul_of_nonneg_right hScaleBound hρ).trans hRadius
  refine ⟨z • (fun j => x j), (lly_third_steep_smul_iff z hz _).mpr hThird, ?_, z * c, F, hMany, ?_, ?_⟩
  · rw [orderedNormAt_smul, hNormZ]
    exact inv_mul_cancel₀ hq.ne'
  · intro j hj
    have hClose := (Finset.mem_filter.mp hj).2
    change ‖z * x j - z * c‖ ≤ δ
    rw [← mul_sub, norm_mul, hNormZ]
    exact (mul_le_mul_of_nonneg_left hClose (inv_nonneg.mpr hq.le)).trans hCloseBound
  · have hVector : (WithLp.toLp 2 (z • (fun j => x j)) : EuclideanSpace ℂ (Fin n)) = z • x := by
      ext j
      rfl
    rw [hVector, map_smul, norm_smul, hNormZ]
    exact (mul_le_mul_of_nonneg_left hSmall (inv_nonneg.mpr hq.le)).trans
      (mul_le_mul_of_nonneg_right hScaleBound hs)

theorem lly_third_almost_unit_adjoint_probability {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₁n : k₁ ≤ n)
    (hRanks : k₂ ≤ k₃) (hHalf : 2 * k₃ ≤ n) (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    {A α ρ δ s : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hρ : 0 ≤ ρ) (hDensity : α * n ≤ k₃)
    (hRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n)
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hs : 0 ≤ s) (ζ : ℂ)
    (hBudget : llyThirdSteepNormConstant n d r * s +
      ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
          (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyThirdAlmostUnitAdjointFailure ζ rows ℓ r k₁ k₂ k₃ α ρ s) ≤
      (n : ℝ) ^ (-A) +
        ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) *
          (meanCorrectedScalarNet k d (1 / 3) δ).card *
            ((4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ k₂ *
              (4 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
                Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ n) := by
  apply (uniformProbability_mono (fun rows hFail =>
    lly_third_almost_unit_adjoint_normalization (by omega : 0 < n) hk₁ (by omega : k₃ ≤ n)
      hFirstFit hρ hDensity hRadius hs ζ rows hFail)).trans
  exact lly_third_almost_adjoint_probability_polynomial hn hd hDegree hk hk₁ hk₂ hk₃ hk₁n hRanks
    hHalf hFirstFit hA hDegreeLog hδ hδSmall hGrid ζ hBudget

end CircularLaw
