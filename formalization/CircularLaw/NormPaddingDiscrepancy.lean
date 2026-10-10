import CircularLaw.NormRectangularPadding

/-!
# Discrepancy survives literal zero-row padding

The active source rows give the exact padded edge count. Their smaller
cardinality gives a larger source discrepancy ratio. Nonnegative edge
counts, monotonic logarithms and the checked entropy monotonicity carry
both alternatives to the padded square matrix. Zero edge counts use
the first alternative directly.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem normPadMatrix_discrepancy {m n : ℕ} (hm : m ≤ n) {density cap kappa₂ : ℝ}
    (hDensity : 0 < density) (hCap : 0 ≤ cap) (hKappa : 0 ≤ kappa₂)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hDP : MatrixDiscrepancy density cap kappa₂ M) :
    MatrixDiscrepancy density cap kappa₂ (normPadMatrix M) := by
  intro S T hS hT
  let S₀ := normPadActiveRows hm S
  let E := matrixEdgeCount M S₀ T
  let sourceMean := density * ((S₀.card : ℝ) * (T.card : ℝ))
  let paddedMean := density * ((S.card : ℝ) * (T.card : ℝ))
  have hEdge : matrixEdgeCount (normPadMatrix M) S T = E := normPadMatrix_edgeCount hm M S T
  rw [hEdge]
  change E / paddedMean ≤ cap ∨ E * Real.log (E / paddedMean) ≤ kappa₂ * edgeSetEntropy n (max S.card T.card)
  by_cases hZero : E = 0
  · left
    rw [hZero, zero_div]
    exact hCap
  have hE : 0 ≤ E := matrixEdgeCount_nonneg M hM S₀ T
  have hEPos : 0 < E := lt_of_le_of_ne hE (Ne.symm hZero)
  have hSourceNonempty : S₀.Nonempty := by
    by_contra hEmpty
    have hSet : S₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    apply hZero
    change matrixEdgeCount M S₀ T = 0
    simp only [matrixEdgeCount, hSet, Finset.sum_empty]
  have hSourceCard : (0 : ℝ) < S₀.card := by exact_mod_cast hSourceNonempty.card_pos
  have hRowCard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hColumnCard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hSourceMean : 0 < sourceMean := mul_pos hDensity (mul_pos hSourceCard hColumnCard)
  have hPaddedMean : 0 < paddedMean := mul_pos hDensity (mul_pos hRowCard hColumnCard)
  have hCard : S₀.card ≤ S.card := normPadActiveRows_card_le hm S
  have hCardReal : (S₀.card : ℝ) ≤ S.card := by exact_mod_cast hCard
  have hMeans : sourceMean ≤ paddedMean :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCardReal hColumnCard.le) hDensity.le
  have hRatios : E / paddedMean ≤ E / sourceMean := by
    apply (div_le_div_iff₀ hPaddedMean hSourceMean).mpr
    exact mul_le_mul_of_nonneg_left hMeans hE
  have hActual := hDP S₀ T hSourceNonempty hT
  change E / sourceMean ≤ cap ∨ E * Real.log (E / sourceMean) ≤
    kappa₂ * edgeSetEntropy n (max S₀.card T.card) at hActual
  rcases hActual with hSmall | hEntropy
  · exact Or.inl (hRatios.trans hSmall)
  · right
    have hLog := Real.log_le_log (div_pos hEPos hPaddedMean) hRatios
    have hMaxPos : 0 < max S₀.card T.card := hT.card_pos.trans_le (le_max_right _ _)
    have hMax : max S₀.card T.card ≤ max S.card T.card := max_le_max hCard le_rfl
    have hRowBound : S.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    have hColumnBound : T.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
    have hMaxBound : max S.card T.card ≤ n := max_le hRowBound hColumnBound
    have hEntropyMono := edgeSetEntropy_mono hMaxPos hMax hMaxBound
    calc
      _ ≤ E * Real.log (E / sourceMean) := mul_le_mul_of_nonneg_left hLog hE
      _ ≤ kappa₂ * edgeSetEntropy n (max S₀.card T.card) := hEntropy
      _ ≤ _ := mul_le_mul_of_nonneg_left hEntropyMono hKappa

end CircularLaw
