import CircularLaw.BernoulliRetainedNorm
import CircularLaw.BernoulliLLYRowAction
import CircularLaw.MeanCorrectedScalarNet

/-!
# Mean-corrected nets for the actual Bernoulli right action

The expected Bernoulli matrix is the constant matrix with entries d/n.
A zero-sum error removes that expectation. The remaining constant error
pays the degree d and the checked centered norm, including its random
row-sum fluctuation. The scalar grid remains the existing finite net.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem bernoulli_centered_apply_eq_row_form {n : ℕ} (d : ℕ)
    (sample : BernoulliSquareSample n) (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x i =
      (∑ j, weightedBernoulliValue (x j) (sample (i, j))) - (d : ℂ) / n * ∑ j, x j := by
  change (∑ j, (bernoulliCenteredValue (rowBernoulliParameter n d) (sample (i, j)) : ℂ) * x j) = _
  simp only [bernoulliCenteredValue, Complex.ofReal_sub, rowBernoulliParameter_coe,
    Complex.ofReal_div, Complex.ofReal_natCast, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  cases sample (i, j) <;> simp [weightedBernoulliValue]

theorem bernoulli_retained_shifted_zero_sum_bound {n d : ℕ}
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (ζ : ℂ) {B : ℝ}
    (hNorm : BernoulliRetainedCenteredNormBound I d sample B)
    (x : EuclideanSpace ℂ (Fin n)) (hSum : ∑ j, x j = 0) :
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤
      (B * Real.sqrt d + ‖ζ‖) * ‖x‖ := by
  have hAction : (retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x =
      (retainedCenteredBernoulliMatrix I d sample).toEuclideanLin x -
        ζ • (WithLp.toLp 2 (fun i : I => x i.val) : EuclideanSpace ℂ I) := by
    ext i
    change (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i.val =
      (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x i.val - ζ * x i.val
    rw [shifted_bernoulli_matrix_apply_eq_row_form, bernoulli_centered_apply_eq_row_form,
      hSum, mul_zero, sub_zero]
  rw [hAction]
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  have hRight := mul_le_mul_of_nonneg_left (euclidean_retained_norm_le I (fun j => x j))
    (norm_nonneg ζ)
  have hBound := add_le_add (hNorm x) hRight
  convert hBound using 1
  ring

theorem bernoulli_retained_shifted_constant_bound {n d : ℕ} (hn : 0 < n)
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (ζ a : ℂ) {B : ℝ}
    (hNorm : BernoulliRetainedCenteredNormBound I d sample B) :
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
      (WithLp.toLp 2 (fun _ => a))‖ ≤
        (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * ‖a‖ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun _ => a)
  let v : EuclideanSpace ℂ I := WithLp.toLp 2 (fun _ => a)
  have hAction : (retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x =
      (retainedCenteredBernoulliMatrix I d sample).toEuclideanLin x + ((d : ℂ) - ζ) • v := by
    ext i
    change (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i.val =
      (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x i.val +
        ((d : ℂ) - ζ) * a
    rw [shifted_bernoulli_matrix_apply_eq_row_form, bernoulli_centered_apply_eq_row_form]
    simp only [x, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hScalar : ‖(d : ℂ) - ζ‖ ≤ (d : ℝ) + ‖ζ‖ := by
    simpa only [Complex.norm_natCast] using norm_sub_le (d : ℂ) ζ
  have hRestriction : ‖v‖ ≤ Real.sqrt n * ‖a‖ := by
    exact (euclidean_retained_norm_le I (fun _ => a)).trans_eq (euclidean_constant_norm a)
  change ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤ _
  rw [hAction]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  calc
    _ ≤ B * Real.sqrt d * ‖x‖ + ((d : ℝ) + ‖ζ‖) * (Real.sqrt n * ‖a‖) :=
      add_le_add (hNorm x) (mul_le_mul hScalar hRestriction (norm_nonneg _) (by positivity))
    _ = _ := by rw [show ‖x‖ = Real.sqrt n * ‖a‖ from euclidean_constant_norm a]; ring

theorem bernoulli_retained_mean_corrected_error {n d : ℕ} (hn : 0 < n)
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (ζ : ℂ) {B δ ε : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hNorm : BernoulliRetainedCenteredNormBound I d sample B)
    (x u : Fin n → ℂ) (c w : ℂ) (hBound : ∀ j, ‖x j - u j‖ ≤ δ)
    (hMean : ‖c + coordinateMean (fun j => x j - u j) - w‖ ≤ ε) :
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
      (WithLp.toLp 2 (fun j => (x j + c) - (u j + w)))‖ ≤
        (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
          (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * ε := by
  let v : Fin n → ℂ := fun j => x j - u j
  let a := c + coordinateMean v - w
  have hDecomp : (WithLp.toLp 2 (fun j => (x j + c) - (u j + w)) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 (meanCenteredVector v) + WithLp.toLp 2 (fun _ => a) := by
    ext j
    change (x j + c) - (u j + w) = (x j - u j - coordinateMean v) + (c + coordinateMean v - w)
    ring
  rw [hDecomp, map_add]
  apply (norm_add_le _ _).trans
  exact add_le_add
    ((bernoulli_retained_shifted_zero_sum_bound I sample ζ hNorm _ (meanCenteredVector_sum hn v)).trans
      (mul_le_mul_of_nonneg_left (meanCenteredVector_euclidean_bound hn v hδ hBound) (by positivity)))
    ((bernoulli_retained_shifted_constant_bound hn I sample ζ a hNorm).trans
      (mul_le_mul_of_nonneg_left hMean (by positivity)))

theorem bernoulli_mean_corrected_scalar_net_retained_cover {n k d : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (I : Finset (Fin n)) (sample : BernoulliSquareSample n) (ζ : ℂ) {B R δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hNorm : BernoulliRetainedCenteredNormBound I d sample B)
    (x u : Fin n → ℂ) (c : ℂ) (hCenter : ‖c‖ ≤ R) (hBound : ∀ j, ‖x j - u j‖ ≤ δ) :
    ∃ w ∈ meanCorrectedScalarNet k d R δ,
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => (x j + c) - (u j + w)))‖ ≤
          (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt n * δ) +
            (B * Real.sqrt d + d + ‖ζ‖) * Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d)) := by
  obtain ⟨w, hw, hMean⟩ := mean_corrected_scalar_net_cover hn hk hd x u c hCenter hBound
  exact ⟨w, hw, bernoulli_retained_mean_corrected_error hn I sample ζ hB hδ hNorm x u c w hBound hMean⟩

end CircularLaw
