import CircularLaw.RowSliceOutNeighbourLaplace
import CircularLaw.RowSliceOutNeighbourMean
import CircularLaw.RowSliceEdgeLowerTail
import CircularLaw.BinomialEntropy

/-!
# Uniform out-neighbour expansion in the actual row-slice model

The negative exponential moment and exact mean give the lower tail.
The uniform estimate counts every row subset before a vector is chosen.
All degree, rank, density and entropy conditions remain explicit.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem row_slice_out_neighbour_lower_laplace_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) {tilt : ℝ} (htilt : 0 ≤ tilt) (u : ℝ) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      ((rowSliceOutNeighbours S rows).card : ℝ) ≤ u) ≤
        Real.exp (rowSliceOutNeighbourMean (n := n) d S * (Real.exp (-tilt) - 1) + tilt * u) := by
  let f := fun rows : Fin m → RowSlice n d => Real.exp (-tilt * ((rowSliceOutNeighbours S rows).card : ℝ))
  have hMark := finite_uniform_markov
    (fun rows : Fin m → RowSlice n d => ((rowSliceOutNeighbours S rows).card : ℝ) ≤ u)
    f (a := Real.exp (-tilt * u)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
    (fun _ hEvent => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hEvent (by linarith)))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (out_neighbour_negative_laplace_exp hn hd S htilt)
    (Real.exp_nonneg (-tilt * u))).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

theorem row_slice_out_neighbour_chernoff_lower_tail {m n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (S : Finset (Fin m)) {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * S.card ≤ ε * n) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      ((rowSliceOutNeighbours S rows).card : ℝ) ≤ (1 - ε) * (d : ℝ) * S.card) ≤
        Real.exp (-ε ^ 2 * (d : ℝ) * S.card / 8) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMean := rowSliceOutNeighbourMean_bounds hn hd S
  have hMeanNonneg := rowSliceOutNeighbourMean_nonneg hn hd S
  have hSizeRatio : (d : ℝ) * S.card / (2 * n) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith only [hSize]
  have hMeanLower : (1 - ε / 2) * (d : ℝ) * S.card ≤ rowSliceOutNeighbourMean (n := n) d S := by
    apply (show (1 - ε / 2) * (d : ℝ) * S.card ≤
        (d : ℝ) * S.card * (1 - (d : ℝ) * S.card / (2 * n)) from ?_).trans hMean.1
    have h := mul_le_mul_of_nonneg_left hSizeRatio (by positivity : 0 ≤ (d : ℝ) * S.card)
    nlinarith only [h]
  apply (row_slice_out_neighbour_lower_laplace_tail hn hd S (by positivity : 0 ≤ ε / 2) _).trans
  apply Real.exp_le_exp.mpr
  have hTaylor := mul_le_mul_of_nonneg_left
    (real_exp_neg_le_quadratic (by positivity : 0 ≤ ε / 2)) hMeanNonneg
  have hLowerScaled := mul_le_mul_of_nonneg_right hMeanLower (by positivity : 0 ≤ ε / 2)
  have hUpperScaled := mul_le_mul_of_nonneg_right hMean.2 (by positivity : 0 ≤ (ε / 2) ^ 2 / 2)
  nlinarith only [hTaylor, hLowerScaled, hUpperScaled]

def RowSliceOutExpansion {n d : ℕ} (k : ℕ) (ε : ℝ) (rows : RowSliceMatrix n d) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → (1 - ε) * (d : ℝ) * k ≤ (rowSliceOutNeighbours S rows).card

theorem row_slice_out_expansion_failure_counting {n d k : ℕ} (hn : 0 < n) (hd : d ≤ n)
    {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k ≤ ε * n) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬RowSliceOutExpansion k ε rows) ≤
      (n.choose k : ℝ) * Real.exp (-ε ^ 2 * (d : ℝ) * k / 8) := by
  let A := (Finset.univ : Finset (Fin n)).powersetCard k
  let E := fun S : Finset (Fin n) => fun rows : RowSliceMatrix n d =>
    ((rowSliceOutNeighbours S rows).card : ℝ) ≤ (1 - ε) * (d : ℝ) * k
  apply (uniformProbability_mono ?_).trans ((uniformProbability_finset_exists_le A E).trans ?_)
  · intro rows hBad
    unfold RowSliceOutExpansion at hBad
    push_neg at hBad
    obtain ⟨S, hS, hSmall⟩ := hBad
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, hSmall.le⟩
  · calc
      _ ≤ ∑ _S ∈ A, Real.exp (-ε ^ 2 * (d : ℝ) * k / 8) := by
        apply Finset.sum_le_sum
        intro S hS
        have hCard := (Finset.mem_powersetCard.mp hS).2
        have h := row_slice_out_neighbour_chernoff_lower_tail hn hd S hε (by simpa only [hCard] using hSize)
        simpa only [E, hCard] using h
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

theorem row_slice_out_expansion_failure_entropy {n d k : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (hk : 0 < k) (hkn : k ≤ n) {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k ≤ ε * n) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬RowSliceOutExpansion k ε rows) ≤
      Real.exp ((k : ℝ) * Real.log (Real.exp 1 * n / k) - ε ^ 2 * (d : ℝ) * k / 8) := by
  apply (row_slice_out_expansion_failure_counting hn hd hε hSize).trans
  apply (mul_le_mul_of_nonneg_right (choose_le_exp_entropy hn hk hkn) (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem row_slice_out_expansion_failure_absorbed {n d k : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (hk : 0 < k) (hkn : k ≤ n) {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k ≤ ε * n)
    (hEntropy : 16 * Real.log (Real.exp 1 * n / k) ≤ ε ^ 2 * d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬RowSliceOutExpansion k ε rows) ≤
      Real.exp (-ε ^ 2 * (d : ℝ) * k / 16) := by
  apply (row_slice_out_expansion_failure_entropy hn hd hk hkn hε hSize).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hEntropy (Nat.cast_nonneg (α := ℝ) k)
  nlinarith only [h]

theorem row_slice_out_expansion_failure_union {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (A : Finset ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hRanks : ∀ k ∈ A, 0 < k ∧ k ≤ n ∧ (d : ℝ) * k ≤ ε * n ∧
      16 * Real.log (Real.exp 1 * n / k) ≤ ε ^ 2 * d) :
    uniformProbability (fun rows : RowSliceMatrix n d => ∃ k ∈ A, ¬RowSliceOutExpansion k ε rows) ≤
      (A.card : ℝ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) := by
  apply (uniformProbability_finset_exists_le A (fun k rows => ¬RowSliceOutExpansion k ε rows)).trans
  calc
    _ ≤ ∑ _k ∈ A, Real.exp (-ε ^ 2 * (d : ℝ) / 16) := by
      apply Finset.sum_le_sum
      intro k hkA
      obtain ⟨hk, hkn, hSize, hEntropy⟩ := hRanks k hkA
      apply (row_slice_out_expansion_failure_absorbed hn hd hk hkn hε hSize hEntropy).trans
      apply Real.exp_le_exp.mpr
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h := mul_le_mul_of_nonneg_right hkR (by positivity : 0 ≤ ε ^ 2 * (d : ℝ))
      nlinarith only [h]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end CircularLaw
