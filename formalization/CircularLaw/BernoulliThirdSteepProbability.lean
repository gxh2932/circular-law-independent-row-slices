import CircularLaw.BernoulliSecondSteepProbability
import CircularLaw.LLYThirdSteepNormalization

/-!
# Actual Bernoulli probabilities for almost-constant third-class vectors

Almost constancy supplies the small scalar center of the deterministic
third-class cover. All retained-row fixed-vector probabilities concern the
original independent Bernoulli entries, without a slice conditioning loss.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem bernoulli_third_net_retained_union_probability {n d r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk₂ : 0 < k₂)
    (hRanks : k₂ ≤ k₃) (hFit : k₃ + k₂ ≤ n)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (C : Finset ℂ) (ζ : ℂ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k, ∃ w ∈ C,
        ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt n / 3} ≤
      ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) * C.card *
        (8 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
          Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ I.card :=
  bernoulli_ordered_large_net_union_probability hd hDegree hk₂ hFit I hRows _
    (fun u hu => lly_third_net_ordered_gap hk₂ hRanks hFit u hu) C ζ

def BernoulliThirdNormalizedAlmostRightFailure {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (sample : BernoulliSquareSample n) (ℓ r k₁ k₂ k₃ : ℕ) (δ τ : ℝ) : Prop :=
  ∃ x : Fin n → ℂ, x ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ∧ orderedNormAt x k₂ = 1 ∧
    ∃ c : ℂ, ∃ F : Finset (Fin n), n - k₃ < F.card ∧
      (∀ j ∈ F, ‖x j - c‖ ≤ δ) ∧
        ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin (WithLp.toLp 2 x)‖ ≤ τ

theorem bernoulli_third_retained_finite_cover {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hd : 0 < d) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hHalf : 2 * k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {B δ τ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100)
    (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ) (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (hNorm : BernoulliRetainedCenteredNormBound I d sample B)
    (hBudget : τ + ((B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3)
    (hFail : BernoulliThirdNormalizedAlmostRightFailure (d := d) I ζ sample ℓ r k₁ k₂ k₃ δ τ) :
    ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
      ∃ w ∈ meanCorrectedScalarNet k d (1 / 3) δ,
        ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt n / 3 := by
  obtain ⟨x, hx, hNormalized, c, F, hMany, hClose, hSmall⟩ := hFail
  obtain ⟨u, hu, hApprox⟩ := lly_third_normalized_net_approximation hk hk₁ hk₂ hk₃ hk₁n hk₂n
    hHalf hFit hδSmall hGrid x hx hNormalized c F hMany hClose
  have hCenter := lly_third_normalized_center_bound hk₃ hHalf x hx hNormalized c F hδSmall hMany hClose
  obtain ⟨w, hw, hError⟩ := bernoulli_mean_corrected_scalar_net_retained_cover (by omega : 0 < n)
    hk hd I sample ζ hB hδ hNorm (fun j => x j - c) u c hCenter hApprox
  refine ⟨u, hu, w, hw, ?_⟩
  have hDecomp : (WithLp.toLp 2 (fun j => u j + w) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (fun j => ((x j - c) + c) - (u j + w)) := by
    ext j
    change u j + w = x j - ((x j - c + c) - (u j + w))
    ring
  rw [hDecomp, map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add hSmall hError).trans hBudget)

theorem bernoulli_third_retained_probability {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₁n : k₁ ≤ n)
    (hRanks : k₂ ≤ k₃) (hHalf : 2 * k₃ ≤ n) (hRanksFit : k₃ + k₂ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (ζ : ℂ)
    (hBudget : τ + ((bernoulliComplexNormConstant A * Real.sqrt d + ‖ζ‖) *
      (2 * Real.sqrt n * δ) + (bernoulliComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) *
        Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliThirdNormalizedAlmostRightFailure (d := d) I ζ sample ℓ r k₁ k₂ k₃ δ τ} ≤
        (n : ℝ) ^ (-A) + ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) *
          (meanCorrectedScalarNet k d (1 / 3) δ).card *
            (8 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
              Real.sqrt ((k₂ : ℝ) * ((d : ℝ) / n)))) ^ I.card := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliThirdNormalizedAlmostRightFailure (d := d) I ζ sample ℓ r k₁ k₂ k₃ δ τ} ⊆
      {sample | ¬BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)} ∪
        {sample | ∃ u ∈ llyThirdNonconstantNet n d r k₁ k₂ k₃ k,
          ∃ w ∈ meanCorrectedScalarNet k d (1 / 3) δ,
            ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
              (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt n / 3} := by
    intro sample hFail
    by_cases hNorm : BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)
    · exact Or.inr (bernoulli_third_retained_finite_cover hd hk hk₁ hk₂ hk₃ hk₁n
        (by omega : k₂ ≤ n) hHalf hFirstFit (bernoulli_complex_norm_constant_nonneg hA)
        hδ hδSmall hGrid I ζ sample hNorm hBudget hFail)
    · exact Or.inl hNorm
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans ((measureReal_union_le _ _).trans ?_)
  exact add_le_add (bernoulli_retained_centered_norm_failure_polynomial hn hd (by omega : d ≤ n)
    hA hDegreeLog I) (bernoulli_third_net_retained_union_probability hd hDegree hk₂ hRanks hRanksFit I hRows _ ζ)

def BernoulliThirdUnitRetainedFailure {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (sample : BernoulliSquareSample n) (ℓ r k₁ k₂ k₃ : ℕ) (α ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llyThirdSteep d ℓ r k₁ k₂ k₃ ∧ ¬sourceNonAlmostConstant α ρ x ∧
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤ τ

theorem bernoulli_third_unit_retained_normalization {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hk₃n : k₃ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {α ρ δ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hDensity : α * n ≤ k₃)
    (hRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n)
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (hFail : BernoulliThirdUnitRetainedFailure (d := d) I ζ sample ℓ r k₁ k₂ k₃ α ρ τ) :
    BernoulliThirdNormalizedAlmostRightFailure (d := d) I ζ sample ℓ r k₁ k₂ k₃ δ
      (llyThirdSteepNormConstant n d r * τ) := by
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
      (mul_le_mul_of_nonneg_right hScaleBound hτ)

end CircularLaw
