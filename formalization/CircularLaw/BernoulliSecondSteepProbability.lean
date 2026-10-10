import CircularLaw.BernoulliOrderedNetSmallBall
import CircularLaw.BernoulliMeanCorrectedNet
import CircularLaw.LLYSecondSteepNormalization

/-!
# Actual Bernoulli probabilities for the second steep class

The deterministic layered cover is paired with the mean-corrected scalar
net. Its fixed vectors have the proved rare-selection decay. The actual
centered Bernoulli norm supplies the only additional exceptional event.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem bernoulli_retained_centered_norm_failure_polynomial {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) (I : Finset (Fin n)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)} ≤
        (n : ℝ) ^ (-A) := by
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (bernoulli_retained_centered_norm_simultaneous_failure hn hd hdn hA hDegree)
  intro sample hFail hAll
  exact hFail (hAll I)

theorem bernoulli_second_net_retained_union_probability {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (hk₁ : 0 < k₁)
    (hRanks : k₁ ≤ k₂) (hFit : k₂ + k₁ ≤ n)
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (I : Finset (Fin n)) (hRows : (4 / 5 : ℝ) * n ≤ I.card) (C : Finset ℂ) (ζ : ℂ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∃ w ∈ C,
        ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
          (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30} ≤
      ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) * C.card *
        Real.exp (-(k₁ : ℝ) * d / 16) :=
  bernoulli_ordered_rare_net_union_probability hn hdn hk₁ hFit I hRows hRare _
    (fun u hu => lly_second_net_ordered_gap hk₁ hRanks hFit u hu) C ζ

def BernoulliSecondNormalizedRightFailure {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (sample : BernoulliSquareSample n) (ℓ r k₁ k₂ : ℕ) (τ : ℝ) : Prop :=
  ∃ x : Fin n → ℂ, x ∈ llySecondSteep d ℓ r k₁ k₂ ∧ orderedNormAt x k₁ = 1 ∧
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin (WithLp.toLp 2 x)‖ ≤ τ

theorem bernoulli_second_retained_finite_cover {n d ℓ r k₁ k₂ k : ℕ}
    (hd : 0 < d) (hℓ : 0 < ℓ) (hk : 0 < k) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hFit : k₁ ≤ ℓ ^ (r + 1))
    {B δ τ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3)
    (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ) (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (hNorm : BernoulliRetainedCenteredNormBound I d sample B)
    (hBudget : τ + ((B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤
        Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hFail : BernoulliSecondNormalizedRightFailure (d := d) I ζ sample ℓ r k₁ k₂ τ) :
    ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k, ∃ w ∈ meanCorrectedScalarNet k d 0 δ,
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30 := by
  obtain ⟨x, hx, hNormalized, hSmall⟩ := hFail
  obtain ⟨u, hu, hApprox⟩ := lly_second_normalized_net_approximation_degree hd hℓ hk hk₁ hk₂
    hk₁n hk₂n hFit hδSmall hGrid hResolution x hx hNormalized
  obtain ⟨w, hw, hError⟩ := bernoulli_mean_corrected_scalar_net_retained_cover (by omega : 0 < n)
    hk hd I sample ζ hB hδ hNorm x u 0 (by norm_num : ‖(0 : ℂ)‖ ≤ (0 : ℝ)) hApprox
  refine ⟨u, hu, w, hw, ?_⟩
  have hDecomp : (WithLp.toLp 2 (fun j => u j + w) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 x - WithLp.toLp 2 (fun j => (x j + 0) - (u j + w)) := by
    ext j
    change u j + w = x j - ((x j + 0) - (u j + w))
    ring
  rw [hDecomp, map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add hSmall hError).trans hBudget)

theorem bernoulli_second_retained_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    {A δ τ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (4 / 5 : ℝ) * n ≤ I.card) (ζ : ℂ)
    (hBudget : τ + ((bernoulliComplexNormConstant A * Real.sqrt d + ‖ζ‖) *
      (2 * Real.sqrt n * δ) + (bernoulliComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) *
        Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliSecondNormalizedRightFailure (d := d) I ζ sample ℓ r k₁ k₂ τ} ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  have hEvent : {sample : BernoulliSquareSample n |
      BernoulliSecondNormalizedRightFailure (d := d) I ζ sample ℓ r k₁ k₂ τ} ⊆
      {sample | ¬BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)} ∪
        {sample | ∃ u ∈ llySecondNonconstantNet n d ℓ r k₁ k₂ k,
          ∃ w ∈ meanCorrectedScalarNet k d 0 δ,
            ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
              (WithLp.toLp 2 (fun j => u j + w))‖ ≤ Real.sqrt ((k₁ : ℝ) * d) / 30} := by
    intro sample hFail
    by_cases hNorm : BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)
    · exact Or.inr (bernoulli_second_retained_finite_cover hd hℓ hk hk₁ (by omega : 0 < k₂)
        (by omega : k₁ ≤ n) (by omega : k₂ ≤ n) hFirstFit (bernoulli_complex_norm_constant_nonneg hA)
        hδ hδSmall hGrid hResolution I ζ sample hNorm hBudget hFail)
    · exact Or.inl hNorm
  apply (measureReal_mono hEvent (h₂ := by finiteness)).trans ((measureReal_union_le _ _).trans ?_)
  apply add_le_add (bernoulli_retained_centered_norm_failure_polynomial hn hd hdn hA hDegreeLog I)
  apply (bernoulli_second_net_retained_union_probability (by omega : 0 < n) hdn hk₁ hRanks
    hRanksFit hRare I hRows _ ζ).trans
  apply (mul_le_mul_of_nonneg_right hEntropy (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

def BernoulliSecondRetainedKernelFailure {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (sample : BernoulliSquareSample n) (ℓ r k₁ k₂ : ℕ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), (fun j => x j) ∈ llySecondSteep d ℓ r k₁ k₂ ∧
    (retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x = 0

theorem bernoulli_second_retained_kernel_normalization {n d ℓ r k₁ k₂ : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (hFail : BernoulliSecondRetainedKernelFailure (d := d) I ζ sample ℓ r k₁ k₂) :
    BernoulliSecondNormalizedRightFailure (d := d) I ζ sample ℓ r k₁ k₂ 0 := by
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

theorem bernoulli_second_retained_kernel_probability_absorbed {n d ℓ r k₁ k₂ k : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k)
    (hk₁ : 0 < k₁) (hRanks : k₁ ≤ k₂) (hRanksFit : k₂ + k₁ ≤ n)
    (hFirstFit : k₁ ≤ ℓ ^ (r + 1))
    (hRare : (k₁ : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    {A δ : ℝ} (hA : 0 ≤ A) (hDegreeLog : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ))
    (hδ : 0 ≤ δ) (hδSmall : δ < 1 / 3) (hGrid : Real.sqrt 2 / (k : ℝ) ≤ δ)
    (hResolution : 1 / (d : ℝ) ^ (3 / 4 : ℝ) ≤ δ)
    (I : Finset (Fin n)) (hRows : (4 / 5 : ℝ) * n ≤ I.card) (ζ : ℂ)
    (hBudget : ((bernoulliComplexNormConstant A * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
      (bernoulliComplexNormConstant A * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n *
        (Real.sqrt 2 / ((k : ℝ) * d))) ≤ Real.sqrt ((k₁ : ℝ) * d) / 30)
    (hEntropy : ((llySecondNonconstantNet n d ℓ r k₁ k₂ k).card : ℝ) *
      (meanCorrectedScalarNet k d 0 δ).card ≤ Real.exp ((k₁ : ℝ) * d / 32)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliSecondRetainedKernelFailure (d := d) I ζ sample ℓ r k₁ k₂} ≤
        (n : ℝ) ^ (-A) + Real.exp (-(k₁ : ℝ) * d / 32) := by
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (bernoulli_second_retained_probability_absorbed (τ := 0) hn hd hdn hℓ hk hk₁ hRanks hRanksFit
      hFirstFit hRare hA hDegreeLog hδ hδSmall hGrid hResolution I hRows ζ
        (by simpa only [zero_add] using hBudget) hEntropy)
  intro sample hFail
  exact bernoulli_second_retained_kernel_normalization I ζ sample hFail

end CircularLaw
