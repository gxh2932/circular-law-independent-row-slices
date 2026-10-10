import CircularLaw.OrderedLargeTailRightAction
import CircularLaw.LLYThirdSteepNormalization
import CircularLaw.MeanCorrectedRetainedNet

/-!
# Retained right-kernel bounds for almost-constant third-class vectors

The almost-constant condition remains in the event: it supplies the
actual small scalar center and finite third-class cover. The direct
row-slice estimate charges no Bernoulli row-conditioning loss.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lly_third_net_retained_right_action_union_probability {n d r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk₂ : 0 < k₂)
    (hRanks : k₂ ≤ k₃) (hTail : 4 * k₃ ≤ n)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k, ∃ w ∈ C,
        ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt n / 3) ≤
      ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) * C.card *
        (8 * Real.exp 1 * separatedBlockSmallBallCoefficient ((k₂ : ℝ) * ((d : ℝ) / n))) ^ I.card := by
  apply (uniformProbability_finset_exists_le (llyThirdNonconstantNet n d r k₁ k₂ k₃ k) _).trans
  calc
    _ ≤ ∑ _u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
        (C.card : ℝ) * (8 * Real.exp 1 *
          separatedBlockSmallBallCoefficient ((k₂ : ℝ) * ((d : ℝ) / n))) ^ I.card := by
      apply Finset.sum_le_sum
      intro u hu
      apply (uniformProbability_finset_exists_le C _).trans
      calc
        _ ≤ ∑ _w ∈ C, (8 * Real.exp 1 *
            separatedBlockSmallBallCoefficient ((k₂ : ℝ) * ((d : ℝ) / n))) ^ I.card :=
          Finset.sum_le_sum (fun w _ => row_slice_retained_ordered_large_tail_right_action_norm_small_ball
            hd hDegree hk₂ (by omega : k₂ ≤ n) hTail I hRows u w ζ
            (lly_third_net_ordered_gap hk₂ hRanks (by omega : k₃ + k₂ ≤ n) u hu))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

def llyThirdNormalizedAlmostRightFailure {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (rows : RowSliceMatrix n d) (ℓ r k₁ k₂ k₃ : ℕ) (δ τ : ℝ) : Prop :=
  ∃ x : Fin n → ℂ, x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ∧ orderedNormAt x k₂ = 1 ∧
    ∃ c : ℂ, ∃ F : Finset (Fin n), n - k₃ < F.card ∧
      (∀ j ∈ F, ‖x j - c‖ ≤ δ) ∧
        ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin (WithLp.toLp 2 x)‖ ≤ τ

def llyThirdAlmostUnitRetainedKernelFailure {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (rows : RowSliceMatrix n d) (ℓ r k₁ k₂ k₃ : ℕ) (α ρ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ∧ ¬sourceNonAlmostConstant α ρ x ∧
      (retainedShiftedMatrix I ζ rows).toEuclideanLin x = 0

theorem lly_third_almost_retained_right_finite_cover {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hHalf : 2 * k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {B δ τ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100)
    (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ) (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hNorm : RetainedCenteredNormBound I rows B)
    (hBudget : τ + ((B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3)
    (hFail : llyThirdNormalizedAlmostRightFailure I ζ rows ℓ r k₁ k₂ k₃ δ τ) :
    ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
      ∃ w ∈ meanCorrectedScalarNet k d (1 / 3) δ,
        ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt n / 3 := by
  obtain ⟨x, hx, hNormalized, c, F, hMany, hClose, hSmall⟩ := hFail
  obtain ⟨u, hu, hApprox⟩ := lly_third_normalized_net_approximation hk hk₁ hk₂ hk₃ hk₁n hk₂n
    hHalf hFit hδSmall hGrid x hx hNormalized c F hMany hClose
  have hCenter := lly_third_normalized_center_bound hk₃ hHalf x hx hNormalized c F hδSmall hMany hClose
  obtain ⟨w, hw, hError⟩ := mean_corrected_scalar_net_retained_cover (by omega : 0 < n)
    hk hd I rows ζ hB hδ hNorm (fun j => x j - c) u c hCenter hApprox
  refine ⟨u, hu, w, hw, ?_⟩
  have hDecomp : (WithLp.toLp 2 (fun j => u j + w) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (fun j => ((x j - c) + c) - (u j + w)) := by
    ext j
    change u j + w = x j - ((x j - c + c) - (u j + w))
    ring
  rw [hDecomp, map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add hSmall hError).trans hBudget)

theorem lly_third_almost_retained_right_probability {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₁n : k₁ ≤ n)
    (hRanks : k₂ ≤ k₃) (hTail : 4 * k₃ ≤ n) (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (ζ : ℂ)
    (hBudget : τ + ((rowSliceComplexNormConstant A * Real.sqrt d + ‖ζ‖) *
      (2 * Real.sqrt n * δ) + (rowSliceComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) *
        Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyThirdNormalizedAlmostRightFailure I ζ rows ℓ r k₁ k₂ k₃ δ τ) ≤
        (n : ℝ) ^ (-A) + ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) *
          (meanCorrectedScalarNet k d (1 / 3) δ).card *
            (8 * Real.exp 1 * separatedBlockSmallBallCoefficient ((k₂ : ℝ) * ((d : ℝ) / n))) ^ I.card := by
  have hCover : ∀ rows : RowSliceMatrix n d,
      llyThirdNormalizedAlmostRightFailure I ζ rows ℓ r k₁ k₂ k₃ δ τ →
      ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant A) ∨
        ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k, ∃ w ∈ meanCorrectedScalarNet k d (1 / 3) δ,
          ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
            (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt n / 3 := by
    intro rows hFail
    by_cases hNorm : RetainedCenteredNormBound I rows (rowSliceComplexNormConstant A)
    · exact Or.inr (lly_third_almost_retained_right_finite_cover hd hk hk₁ hk₂ hk₃ hk₁n
        (by omega : k₂ ≤ n) (by omega : 2 * k₃ ≤ n) hFirstFit
        (rowSliceComplexNormConstant_nonneg hA) hδ hδSmall hGrid I ζ rows hNorm hBudget hFail)
    · exact Or.inl hNorm
  apply (uniformProbability_mono hCover).trans ((uniformProbability_or_le _ _).trans ?_)
  exact add_le_add (retainedCenteredNormBound_failure_polynomial hn hd (by omega : d ≤ n)
    hA hDegreeLog I) (lly_third_net_retained_right_action_union_probability hd hDegree hk₂ hRanks
      hTail I hRows _ ζ)

theorem lly_third_almost_unit_retained_kernel_normalization {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₃n : k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {α ρ δ : ℝ} (hρ : 0 ≤ ρ) (hDensity : α * n ≤ k₃)
    (hRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    (hFail : llyThirdAlmostUnitRetainedKernelFailure I ζ rows ℓ r k₁ k₂ k₃ α ρ) :
    llyThirdNormalizedAlmostRightFailure I ζ rows ℓ r k₁ k₂ k₃ δ 0 := by
  obtain ⟨x, hUnit, hThird, hAlmost, hKernel⟩ := hFail
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
    rw [hVector, map_smul, hKernel, smul_zero, norm_zero]

end CircularLaw
