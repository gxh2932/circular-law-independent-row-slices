import CircularLaw.GaussianTwoWordPairings

/-!
# Pairing formulas without balance assumptions

If the direct and adjoint cardinalities agree, a finite bijection exists
and the checked Wick formula applies. Otherwise the matching type is
empty and the actual integral vanishes by imbalance. The same argument
applies jointly to two words, even if neither is individually balanced.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem gaussian_matrix_word_all_pairing_integral (n k : ℕ) (b : Fin (k + 1) → Bool) :
    (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing b,
        (n : ℂ) ^ gaussianWordVertexExponent b (finRotate (k + 1)) e := by
  by_cases h : Nonempty (GaussianWordPairing b)
  · obtain ⟨e₀⟩ := h
    exact gaussian_matrix_word_vertex_integral n k b e₀
  · letI : IsEmpty (GaussianWordPairing b) := ⟨fun e => h ⟨e⟩⟩
    have hCount : (List.ofFn b).count false ≠ (List.ofFn b).count true := by
      intro hCount
      have hCard : Fintype.card (GaussianDirectPositions b) =
          Fintype.card (GaussianAdjointPositions b) := by
        simpa only [list_ofFn_count_eq_fiber_card] using hCount
      exact h ⟨Fintype.equivOfCardEq hCard⟩
    rw [gaussian_matrix_word_trace_count_mismatch_zero n _ hCount]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]

theorem gaussian_two_word_direct_card (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Fintype.card (GaussianDirectPositions (Sum.elim b c)) =
      (List.ofFn b).count false + (List.ofFn c).count false := by
  have e : GaussianDirectPositions (Sum.elim b c) ≃
      GaussianDirectPositions b ⊕ GaussianDirectPositions c := Equiv.subtypeSum
  rw [Fintype.card_congr e, Fintype.card_sum,
    ← list_ofFn_count_eq_fiber_card b false, ← list_ofFn_count_eq_fiber_card c false]

theorem gaussian_two_word_adjoint_card (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Fintype.card (GaussianAdjointPositions (Sum.elim b c)) =
      (List.ofFn b).count true + (List.ofFn c).count true := by
  have e : GaussianAdjointPositions (Sum.elim b c) ≃
      GaussianAdjointPositions b ⊕ GaussianAdjointPositions c := Equiv.subtypeSum
  rw [Fintype.card_congr e, Fintype.card_sum,
    ← list_ofFn_count_eq_fiber_card b true, ← list_ofFn_count_eq_fiber_card c true]

theorem gaussian_two_word_pairing_balance_iff (k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    Fintype.card (GaussianDirectPositions (Sum.elim b c)) =
      Fintype.card (GaussianAdjointPositions (Sum.elim b c)) ↔
        gaussianMatrixWordImbalance (List.ofFn b) + gaussianMatrixWordImbalance (List.ofFn c) = 0 := by
  rw [gaussian_two_word_direct_card, gaussian_two_word_adjoint_card,
    gaussian_matrix_word_imbalance_counts, gaussian_matrix_word_imbalance_counts]
  omega

theorem gaussian_two_word_all_pairing_integral (n k l : ℕ)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool) :
    (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace *
      (gaussianMatrixWord (List.ofFn c) x).trace ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing (Sum.elim b c),
        (n : ℂ) ^ gaussianWordVertexExponent (Sum.elim b c)
          (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) e := by
  by_cases h : Nonempty (GaussianWordPairing (Sum.elim b c))
  · obtain ⟨e₀⟩ := h
    exact gaussian_two_word_trace_pairing_integral n k l b c e₀
  · letI : IsEmpty (GaussianWordPairing (Sum.elim b c)) := ⟨fun e => h ⟨e⟩⟩
    have hIm : gaussianMatrixWordImbalance (List.ofFn b) +
        gaussianMatrixWordImbalance (List.ofFn c) ≠ 0 := by
      intro hZero
      exact h ⟨Fintype.equivOfCardEq ((gaussian_two_word_pairing_balance_iff k l b c).mpr hZero)⟩
    rw [gaussian_matrix_word_trace_product_integral_unbalanced n _ _ hIm]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]

end CircularLaw
