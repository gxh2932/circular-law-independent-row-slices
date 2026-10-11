import CircularLaw.WeightedMatrixLaplace
import CircularLaw.RowLoadFailure

/-!
# Two-sided concentration for weighted row-slice matrices

The finite Markov argument applies to both signs of the tilt. Optimizing
within the checked bounded-tilt range gives a Bernstein-type tail with
the actual squared-weight variance proxy and maximum weight. The rows
are independent under their exact slice product law.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem weighted_matrix_upper_laplace_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {K tilt : ℝ} (hK : ∀ i j, w i j ≤ K)
    (htilt : 0 ≤ tilt) (hScale : tilt * K ≤ 1) (t : ℝ) :
    uniformProbability (fun rows : ι → RowSlice n d => t ≤ centeredWeightedSliceMatrixSum w rows) ≤
      Real.exp (tilt ^ 2 * weightedSliceMatrixVariance n d w - tilt * t) := by
  let f := fun rows : ι → RowSlice n d => Real.exp (tilt * centeredWeightedSliceMatrixSum w rows)
  have hMark := finite_uniform_markov (fun rows : ι → RowSlice n d => t ≤ centeredWeightedSliceMatrixSum w rows)
    f (a := Real.exp (tilt * t)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
    (fun _ hEvent => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hEvent htilt))
  have hMGF := finiteMean_matrix_weighted_laplace_quadratic hn hd w hw hK (tilt := tilt)
    (by simpa only [abs_of_nonneg htilt] using hScale)
  apply hMark.trans
  apply (div_le_div_of_nonneg_right hMGF (Real.exp_nonneg (tilt * t))).trans_eq
  rw [← Real.exp_sub]

theorem weighted_matrix_lower_laplace_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {K tilt : ℝ} (hK : ∀ i j, w i j ≤ K)
    (htilt : 0 ≤ tilt) (hScale : tilt * K ≤ 1) (t : ℝ) :
    uniformProbability (fun rows : ι → RowSlice n d => centeredWeightedSliceMatrixSum w rows ≤ -t) ≤
      Real.exp (tilt ^ 2 * weightedSliceMatrixVariance n d w - tilt * t) := by
  let f := fun rows : ι → RowSlice n d => Real.exp (-tilt * centeredWeightedSliceMatrixSum w rows)
  have hMark := finite_uniform_markov (fun rows : ι → RowSlice n d => centeredWeightedSliceMatrixSum w rows ≤ -t)
    f (a := Real.exp (tilt * t)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
    (fun _ hEvent => Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonpos_left hEvent (neg_nonpos.mpr htilt)
      nlinarith only [h]))
  have hMGF := finiteMean_matrix_weighted_laplace_quadratic hn hd w hw hK
    (tilt := -tilt) (by simpa only [abs_neg, abs_of_nonneg htilt] using hScale)
  simp only [neg_sq] at hMGF
  apply hMark.trans
  apply (div_le_div_of_nonneg_right hMGF (Real.exp_nonneg (tilt * t))).trans_eq
  rw [← Real.exp_sub]

theorem weighted_matrix_two_sided_laplace_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {K tilt : ℝ} (hK : ∀ i j, w i j ≤ K)
    (htilt : 0 ≤ tilt) (hScale : tilt * K ≤ 1) (t : ℝ) :
    uniformProbability (fun rows : ι → RowSlice n d => t ≤ |centeredWeightedSliceMatrixSum w rows|) ≤
      2 * Real.exp (tilt ^ 2 * weightedSliceMatrixVariance n d w - tilt * t) := by
  have hCover : ∀ rows : ι → RowSlice n d, t ≤ |centeredWeightedSliceMatrixSum w rows| →
      t ≤ centeredWeightedSliceMatrixSum w rows ∨ centeredWeightedSliceMatrixSum w rows ≤ -t := by
    intro rows hEvent
    by_cases hSign : 0 ≤ centeredWeightedSliceMatrixSum w rows
    · exact Or.inl (by simpa only [abs_of_nonneg hSign] using hEvent)
    · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hSign)] at hEvent; linarith only [hEvent])
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_or_le _ _).trans
  have h := add_le_add (weighted_matrix_upper_laplace_tail hn hd w hw hK htilt hScale t)
    (weighted_matrix_lower_laplace_tail hn hd w hw hK htilt hScale t)
  convert h using 1
  ring

theorem weighted_matrix_bernstein_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {K t : ℝ} (hKPos : 0 < K) (ht : 0 < t)
    (hK : ∀ i j, w i j ≤ K) :
    uniformProbability (fun rows : ι → RowSlice n d => t ≤ |centeredWeightedSliceMatrixSum w rows|) ≤
      2 * Real.exp (-t ^ 2 / (4 * (weightedSliceMatrixVariance n d w + K * t))) := by
  let v := weightedSliceMatrixVariance n d w
  let D := v + K * t
  let tilt := t / (2 * D)
  have hv : 0 ≤ v := weightedSliceMatrixVariance_nonneg n d w
  have hD : 0 < D := by dsimp only [D]; positivity
  have htilt : 0 ≤ tilt := div_nonneg ht.le (by positivity)
  have hScale : tilt * K ≤ 1 := by
    dsimp only [tilt]
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by positivity : 0 < 2 * D)).mpr
    dsimp only [D]
    nlinarith only [hv, (mul_pos hKPos ht).le]
  have hTail := weighted_matrix_two_sided_laplace_tail hn hd w hw hK htilt hScale t
  apply hTail.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hvD : v ≤ D := by dsimp only [D]; nlinarith only [(mul_pos hKPos ht).le]
  calc
    _ ≤ tilt ^ 2 * D - tilt * t := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hvD (sq_nonneg tilt)) _
    _ = _ := by
      dsimp only [tilt, D, v]
      field_simp
      ring

theorem weighted_matrix_bernstein_tail_with_variance_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) (w : ι → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {K t v : ℝ} (hKPos : 0 < K) (ht : 0 < t)
    (hK : ∀ i j, w i j ≤ K) (hV : weightedSliceMatrixVariance n d w ≤ v) :
    uniformProbability (fun rows : ι → RowSlice n d => t ≤ |centeredWeightedSliceMatrixSum w rows|) ≤
      2 * Real.exp (-t ^ 2 / (4 * (v + K * t))) := by
  apply (weighted_matrix_bernstein_tail hn hd w hw hKPos ht hK).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hVariance := weightedSliceMatrixVariance_nonneg n d w
  have hDen : 0 < 4 * (weightedSliceMatrixVariance n d w + K * t) := by positivity
  have hCompare : 4 * (weightedSliceMatrixVariance n d w + K * t) ≤ 4 * (v + K * t) := by
    linarith only [hV]
  have h := div_le_div_of_nonneg_left (sq_nonneg t) hDen hCompare
  simpa only [neg_div] using neg_le_neg h

end CircularLaw
