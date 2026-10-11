import CircularLaw.LightCoupleBounds

/-!
# The source light-sum probability bound

The literal threshold is `sqrt(N)/n`. Squared mass at most one gives
variance proxy at most `d/n`. For a coefficient matrix with zero total
sum, the checked mean bound supplies the source `d/sqrt(N)` offset.
The resulting probability has rate `4*exp(-B*n/32)` for every `B>=1`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lightMatrixWeights_variance_le {ι : Type*} [Fintype ι] {n d : ℕ}
    (Q : ι → Fin n → ℝ) (K : ℝ) (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    weightedSliceMatrixVariance n d (lightMatrixWeights Q K) ≤ (d : ℝ) / n := by
  unfold weightedSliceMatrixVariance
  have h := mul_le_mul_of_nonneg_left ((lightMatrixWeights_squared_sum_le Q K).trans hSquare)
    (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)
  simpa only [mul_one] using h

theorem lightMatrixWeights_source_mean_bound {ι : Type*} [Fintype ι] {n d : ℕ}
    (hn : 0 < n) {N : ℝ} (hN : 0 < N) (Q : ι → Fin n → ℝ)
    (hZero : (∑ i, ∑ j, Q i j) = 0) (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    |((d : ℝ) / n) * ∑ i, ∑ j, lightMatrixWeights Q (Real.sqrt N / n) i j| ≤
      (d : ℝ) / Real.sqrt N := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)]
  apply (mul_le_mul_of_nonneg_left
    (lightMatrixWeights_sum_abs_le Q (div_pos hRoot hnR) hZero hSquare)
    (by positivity : (0 : ℝ) ≤ (d : ℝ) / n)).trans_eq
  field_simp

theorem light_bernstein_rate {n d : ℕ} (hn : 0 < n) {N B : ℝ}
    (hN : 0 < N) (hdN : (d : ℝ) ≤ N) (hB : 1 ≤ B) :
    B * (n : ℝ) / 32 ≤ (B * Real.sqrt N) ^ 2 /
      (16 * ((d : ℝ) / n) + 8 * (Real.sqrt N / n) * (B * Real.sqrt N)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBPos : 0 < B := by linarith
  have hRoot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hDen : 16 * ((d : ℝ) / n) + 8 * (Real.sqrt N / n) * (B * Real.sqrt N) =
      (16 * (d : ℝ) + 8 * B * N) / n := by
    calc
      _ = (16 * (d : ℝ) + 8 * B * Real.sqrt N ^ 2) / n := by ring
      _ = _ := by rw [Real.sq_sqrt hN.le]
  rw [hDen, mul_pow, Real.sq_sqrt hN.le, div_div_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 16 * (d : ℝ) + 8 * B * N)).mpr
  have hDegree := mul_le_mul_of_nonneg_left hdN hBPos.le
  have hPower := mul_le_mul_of_nonneg_right hB (mul_nonneg hBPos.le hN.le)
  have hNum : B * (16 * (d : ℝ) + 8 * B * N) ≤ 32 * B ^ 2 * N := by
    nlinarith only [hDegree, hPower, mul_nonneg (sq_nonneg B) hN.le]
  have hScaled := mul_le_mul_of_nonneg_right hNum (by positivity : (0 : ℝ) ≤ (n : ℝ) / 32)
  nlinarith only [hScaled]

theorem source_light_centered_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) {N B : ℝ}
    (hN : 0 < N) (hdN : (d : ℝ) ≤ N) (hB : 1 ≤ B)
    (Q : ι → Fin n → ℝ) (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      B * Real.sqrt N ≤ |centeredWeightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows|) ≤
        4 * Real.exp (-B * n / 32) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBPos : 0 < B := by linarith
  have hRoot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hTail := signed_matrix_bernstein_tail hn hd (lightMatrixWeights Q (Real.sqrt N / n))
    (div_pos hRoot hnR) (mul_pos hBPos hRoot)
    (lightMatrixWeights_cap Q (div_nonneg hRoot.le hnR.le))
    (lightMatrixWeights_variance_le Q (Real.sqrt N / n) hSquare)
  apply hTail.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div, neg_mul] using neg_le_neg (light_bernstein_rate hn hN hdN hB)

theorem source_light_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) {N B : ℝ}
    (hN : 0 < N) (hdN : (d : ℝ) ≤ N) (hB : 1 ≤ B)
    (Q : ι → Fin n → ℝ) (hZero : (∑ i, ∑ j, Q i j) = 0)
    (hSquare : (∑ i, ∑ j, Q i j ^ 2) ≤ 1) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (d : ℝ) / Real.sqrt N + B * Real.sqrt N ≤
        |weightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows|) ≤
          4 * Real.exp (-B * n / 32) := by
  have hMean := lightMatrixWeights_source_mean_bound (d := d) hn hN Q hZero hSquare
  have hCover : ∀ rows : ι → RowSlice n d,
      (d : ℝ) / Real.sqrt N + B * Real.sqrt N ≤
        |weightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows| →
      B * Real.sqrt N ≤ |centeredWeightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows| := by
    intro rows hEvent
    have hIdentity : weightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows =
        centeredWeightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows +
          ((d : ℝ) / n) * ∑ i, ∑ j, lightMatrixWeights Q (Real.sqrt N / n) i j := by
      rw [centeredWeightedSliceMatrixSum_eq]
      ring
    have hTriangle := abs_add_le
      (centeredWeightedSliceMatrixSum (lightMatrixWeights Q (Real.sqrt N / n)) rows)
      (((d : ℝ) / n) * ∑ i, ∑ j, lightMatrixWeights Q (Real.sqrt N / n) i j)
    rw [← hIdentity] at hTriangle
    linarith only [hEvent, hTriangle, hMean]
  exact (uniformProbability_mono hCover).trans (source_light_centered_probability hn hd hN hdN hB Q hSquare)

theorem source_rankOne_light_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n) {N B : ℝ}
    (hN : 0 < N) (hdN : (d : ℝ) ≤ N) (hB : 1 ≤ B)
    (x : ι → ℝ) (y : Fin n → ℝ) (hx : (∑ i, x i ^ 2) = 1)
    (hy : (∑ j, y j ^ 2) = 1) (hyZero : (∑ j, y j) = 0) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (d : ℝ) / Real.sqrt N + B * Real.sqrt N ≤
        |weightedSliceMatrixSum (lightMatrixWeights (fun i j => x i * y j) (Real.sqrt N / n)) rows|) ≤
          4 * Real.exp (-B * n / 32) := by
  apply source_light_probability hn hd hN hdN hB _ (rankOneWeights_sum_zero x y hyZero)
  rw [rankOneWeights_squared_sum, hx, hy]
  norm_num

end CircularLaw
