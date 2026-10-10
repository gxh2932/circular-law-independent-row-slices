import CircularLaw.BernoulliThirdSteepProbability
import CircularLaw.SeparatedBlockCoefficientDecay

/-!
# Actual unit-vector steep failures and their Bernoulli probabilities

Homogeneous normalization keeps the actual right action. The second-class
bound uses the rare exponential estimate. The third-class coefficient is
bounded by the already checked separated-block coefficient, permitting
reuse of its source entropy budget without any unproved probability input.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def BernoulliSecondUnitRetainedFailure {n d : ℕ} (I : Finset (Fin n))
    (ζ : ℂ) (sample : BernoulliSquareSample n) (ℓ r k₁ k₂ : ℕ) (τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∧
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤ τ

theorem bernoulli_second_unit_retained_normalization {n d ℓ r k₁ k₂ : ℕ}
    (hn : 0 < n) (hk₁ : 0 < k₁) (hFit : k₁ ≤ ℓ ^ (r + 1)) {τ : ℝ} (hτ : 0 ≤ τ)
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (hFail : BernoulliSecondUnitRetainedFailure (d := d) I ζ sample ℓ r k₁ k₂ τ) :
    BernoulliSecondNormalizedRightFailure (d := d) I ζ sample ℓ r k₁ k₂
      (llySecondSteepNormConstant n d r * τ) := by
  obtain ⟨x, hUnit, hSecond, hSmall⟩ := hFail
  let q := orderedNormAt (fun j => x j) k₁
  have hq : 0 < q := lt_of_le_of_lt
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (orderedNormAt_nonneg _ _)) hSecond.2
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
      (mul_le_mul_of_nonneg_right hScaleBound hτ)

theorem bernoulli_second_unit_retained_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ) (hτ : 0 ≤ τ)
    (I : Finset (Fin n)) (hRows : (4 / 5 : ℝ) * n ≤ I.card) (ζ : ℂ)
    (hBudget : llySecondSteepNormConstant n d r * τ +
      ((bernoulliComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (bernoulliComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
          (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliSecondUnitRetainedFailure (d := d) I ζ sample ℓ r k₁ k₂ τ} ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (bernoulli_second_retained_probability_absorbed
      (τ := llySecondSteepNormConstant n d r * τ) hn hd hdn hℓ hk hk₁ hRanks hRanksFit
      hFirstFit hRare hA hDegreeLog hδ hδSmall hGrid hResolution I hRows ζ hBudget hEntropy)
  intro sample hFail
  exact bernoulli_second_unit_retained_normalization (by omega : 0 < n) hk₁ hFirstFit hτ I ζ sample hFail

theorem bernoulli_scalar_coefficient_le_separated_block (q : ℝ) :
    bernoulliScalarSmallBallConstant / Real.sqrt q ≤ separatedBlockSmallBallCoefficient q := by
  have hCoeff : 0 ≤ bernoulliScalarSmallBallConstant / Real.sqrt q :=
    div_nonneg bernoulli_scalar_small_ball_constant_pos.le (Real.sqrt_nonneg _)
  unfold separatedBlockSmallBallCoefficient
  rw [mul_div_assoc]
  linarith [Real.exp_pos (-q / 48)]

theorem bernoulli_third_unit_retained_probability {n d ℓ r k₁ k₂ k₃ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hDegree : 2 * d ≤ n) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₁n : k₁ ≤ n)
    (hRanks : k₂ ≤ k₃) (hHalf : 2 * k₃ ≤ n) (hRanksFit : k₃ + k₂ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    {A α ρ δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hDensity : α * n ≤ k₃)
    (hRadius : llyThirdSteepNormConstant n d r * ρ ≤ δ * Real.sqrt n)
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 100) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (ζ : ℂ)
    (hBudget : llyThirdSteepNormConstant n d r * τ +
      ((bernoulliComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (bernoulliComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
          (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt n / 3) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliThirdUnitRetainedFailure (d := d) I ζ sample ℓ r k₁ k₂ k₃ α ρ τ} ≤
        (n : ℝ) ^ (-A) + ((llyThirdNonconstantNet n d r k₁ k₂ k₃ k).card : ℝ) *
          (meanCorrectedScalarNet k d (1 / 3) δ).card *
            (8 * Real.exp 1 * separatedBlockSmallBallCoefficient
              ((k₂ : ℝ) * ((d : ℝ) / n))) ^ I.card := by
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    ((bernoulli_third_retained_probability (τ := llyThirdSteepNormConstant n d r * τ)
      hn hd hDegree hk hk₁ hk₂ hk₃ hk₁n hRanks hHalf hRanksFit hFirstFit hA hDegreeLog
      hδ hδSmall hGrid I hRows ζ hBudget).trans ?_)
  · intro sample hFail
    exact bernoulli_third_unit_retained_normalization (by omega : 0 < n) hk₁
      (by omega : k₃ ≤ n) hFirstFit hρ hτ hDensity hRadius I ζ sample hFail
  · apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (mul_nonneg (by positivity)
      (div_nonneg bernoulli_scalar_small_ball_constant_pos.le (Real.sqrt_nonneg _)))
    exact mul_le_mul_of_nonneg_left (bernoulli_scalar_coefficient_le_separated_block _)
      (by positivity)

end CircularLaw
