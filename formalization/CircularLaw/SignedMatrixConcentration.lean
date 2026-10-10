import CircularLaw.WeightedMatrixConcentration

/-!
# Signed coefficients in the light-term concentration estimate

Positive and negative parts are bounded separately under the actual
slice matrix law. Their squared-weight proxies are bounded by that of
the original coefficients. The event union gives a two-sided signed
tail without assuming within-row independence or negative association
for mixed-sign coordinate functions.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def positiveMatrixWeights {ι : Type*} {n : ℕ} (w : ι → Fin n → ℝ) : ι → Fin n → ℝ :=
  fun i j => max (w i j) 0

def negativeMatrixWeights {ι : Type*} {n : ℕ} (w : ι → Fin n → ℝ) : ι → Fin n → ℝ :=
  fun i j => max (-w i j) 0

theorem matrix_weights_positive_sub_negative {ι : Type*} {n : ℕ} (w : ι → Fin n → ℝ) :
    w = fun i j => positiveMatrixWeights w i j - negativeMatrixWeights w i j := by
  funext i j
  unfold positiveMatrixWeights negativeMatrixWeights
  by_cases h : 0 ≤ w i j
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · have hNonpos := le_of_not_ge h
    rw [max_eq_right hNonpos, max_eq_left (neg_nonneg.mpr hNonpos)]
    ring

theorem weightedSliceSum_sub {n d : ℕ} (M : Finset (Fin n)) (a b : Fin n → ℝ) (s : RowSlice n d) :
    weightedSliceSum M (fun j => a j - b j) s = weightedSliceSum M a s - weightedSliceSum M b s := by
  unfold weightedSliceSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [sub_self]

theorem centeredWeightedSliceMatrixSum_sub {ι : Type*} [Fintype ι] {n d : ℕ}
    (a b : ι → Fin n → ℝ) (rows : ι → RowSlice n d) :
    centeredWeightedSliceMatrixSum (fun i j => a i j - b i j) rows =
      centeredWeightedSliceMatrixSum a rows - centeredWeightedSliceMatrixSum b rows := by
  unfold centeredWeightedSliceMatrixSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedSliceSum_sub, Finset.sum_sub_distrib]
  ring

theorem centeredWeightedSliceMatrixSum_signed {ι : Type*} [Fintype ι] {n d : ℕ}
    (w : ι → Fin n → ℝ) (rows : ι → RowSlice n d) :
    centeredWeightedSliceMatrixSum w rows =
      centeredWeightedSliceMatrixSum (positiveMatrixWeights w) rows -
        centeredWeightedSliceMatrixSum (negativeMatrixWeights w) rows := by
  conv_lhs => rw [matrix_weights_positive_sub_negative w]
  exact centeredWeightedSliceMatrixSum_sub _ _ rows

theorem weightedSliceMatrixVariance_mono_abs {ι : Type*} [Fintype ι] (n d : ℕ)
    (a b : ι → Fin n → ℝ) (h : ∀ i j, |a i j| ≤ |b i j|) :
    weightedSliceMatrixVariance n d a ≤ weightedSliceMatrixVariance n d b := by
  unfold weightedSliceMatrixVariance
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a i j)) (h i j) 2

theorem matrix_parts_variance_le {ι : Type*} [Fintype ι] (n d : ℕ) (w : ι → Fin n → ℝ) :
    weightedSliceMatrixVariance n d (positiveMatrixWeights w) ≤ weightedSliceMatrixVariance n d w ∧
      weightedSliceMatrixVariance n d (negativeMatrixWeights w) ≤ weightedSliceMatrixVariance n d w := by
  constructor
  · apply weightedSliceMatrixVariance_mono_abs
    intro i j
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  · apply weightedSliceMatrixVariance_mono_abs
    intro i j
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)

theorem signed_matrix_bernstein_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    {K t v : ℝ} (hKPos : 0 < K) (ht : 0 < t) (hK : ∀ i j, |w i j| ≤ K)
    (hV : weightedSliceMatrixVariance n d w ≤ v) :
    uniformProbability (fun rows : ι → RowSlice n d => t ≤ |centeredWeightedSliceMatrixSum w rows|) ≤
      4 * Real.exp (-t ^ 2 / (16 * v + 8 * K * t)) := by
  have hPlus (i : ι) (j : Fin n) : positiveMatrixWeights w i j ≤ K :=
    (max_le (le_abs_self _) (abs_nonneg _)).trans (hK i j)
  have hMinus (i : ι) (j : Fin n) : negativeMatrixWeights w i j ≤ K :=
    (max_le (neg_le_abs _) (abs_nonneg _)).trans (hK i j)
  have hParts := matrix_parts_variance_le n d w
  have hPlusBound := weighted_matrix_bernstein_tail_with_variance_upper hn hd (positiveMatrixWeights w)
    (fun _ _ => le_max_right _ _) hKPos (by positivity : 0 < t / 2) hPlus (hParts.1.trans hV)
  have hMinusBound := weighted_matrix_bernstein_tail_with_variance_upper hn hd (negativeMatrixWeights w)
    (fun _ _ => le_max_right _ _) hKPos (by positivity : 0 < t / 2) hMinus (hParts.2.trans hV)
  have hCover : ∀ rows : ι → RowSlice n d, t ≤ |centeredWeightedSliceMatrixSum w rows| →
      t / 2 ≤ |centeredWeightedSliceMatrixSum (positiveMatrixWeights w) rows| ∨
        t / 2 ≤ |centeredWeightedSliceMatrixSum (negativeMatrixWeights w) rows| := by
    intro rows hEvent
    by_cases hPlusEvent : t / 2 ≤ |centeredWeightedSliceMatrixSum (positiveMatrixWeights w) rows|
    · exact Or.inl hPlusEvent
    · apply Or.inr
      apply le_of_not_gt
      intro hMinusEvent
      rw [centeredWeightedSliceMatrixSum_signed] at hEvent
      have hTriangle := abs_sub (centeredWeightedSliceMatrixSum (positiveMatrixWeights w) rows)
        (centeredWeightedSliceMatrixSum (negativeMatrixWeights w) rows)
      have hPlusSmall := lt_of_not_ge hPlusEvent
      linarith only [hEvent, hTriangle, hPlusSmall, hMinusEvent]
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_or_le _ _).trans
  have h := add_le_add hPlusBound hMinusBound
  have hRate : -(t / 2) ^ 2 / (4 * (v + K * (t / 2))) = -t ^ 2 / (16 * v + 8 * K * t) := by
    have hv : 0 ≤ v := (weightedSliceMatrixVariance_nonneg n d w).trans hV
    have hDenOne : 0 < v + K * (t / 2) := by positivity
    have hDenTwo : 0 < 16 * v + 8 * K * t := by positivity
    field_simp
    ring
  rw [hRate] at h
  convert h using 1
  ring

end CircularLaw
