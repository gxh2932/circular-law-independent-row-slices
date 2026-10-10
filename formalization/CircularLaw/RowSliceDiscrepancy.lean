import CircularLaw.RowSliceEdgeTails
import CircularLaw.EdgeDiscrepancyEntropy

/-!
# Discrepancy for the actual uniform row-slice law

The two alternatives use the literal edge count, its actual mean and
the size cost of the larger coordinate set. Failure is the checked
logarithmic bad event, with the source constants `exp(2)` and
`2*(beta+4)`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def RowSliceDiscrepancy {m n d : ℕ} (kappa₁ kappa₂ : ℝ)
    (rows : Fin m → RowSlice n d) : Prop :=
  ∀ S : Finset (Fin m), ∀ T : Finset (Fin n), S.Nonempty → T.Nonempty →
    rowSliceEdgeCount S T rows / rowSliceEdgeMean d S T ≤ kappa₁ ∨
      rowSliceEdgeCount S T rows * Real.log (rowSliceEdgeCount S T rows / rowSliceEdgeMean d S T) ≤
        kappa₂ * edgeSetEntropy n (max S.card T.card)

def rowSliceDiscrepancyBad {m n d : ℕ} (beta : ℝ)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (rows : Fin m → RowSlice n d) : Prop :=
  Real.exp 2 * rowSliceEdgeMean d S T < rowSliceEdgeCount S T rows ∧
    2 * (beta + 4) * edgeSetEntropy n (max S.card T.card) <
      rowSliceEdgeCount S T rows * Real.log (rowSliceEdgeCount S T rows / rowSliceEdgeMean d S T)

theorem rowSliceDiscrepancy_failure_iff {m n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (beta : ℝ) (rows : Fin m → RowSlice n d) :
    (¬RowSliceDiscrepancy (Real.exp 2) (2 * (beta + 4)) rows) ↔
      ∃ S : Finset (Fin m), ∃ T : Finset (Fin n),
        S.Nonempty ∧ T.Nonempty ∧ rowSliceDiscrepancyBad beta S T rows := by
  constructor
  · intro hFail
    unfold RowSliceDiscrepancy at hFail
    push_neg at hFail
    obtain ⟨S, T, hS, hT, hRatio, hCost⟩ := hFail
    have hMean := rowSliceEdgeMean_pos hn hd hS hT
    exact ⟨S, T, hS, hT, (lt_div_iff₀ hMean).mp hRatio, hCost⟩
  · rintro ⟨S, T, hS, hT, hBad⟩ hGood
    have hMean := rowSliceEdgeMean_pos hn hd hS hT
    rcases hGood S T hS hT with hRatio | hCost
    · exact not_lt_of_ge ((div_le_iff₀ hMean).mp hRatio) hBad.1
    · exact not_lt_of_ge hCost hBad.2

theorem rowSliceDiscrepancy_fixed_sets_probability {m n d : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hdn : d ≤ n) (beta : ℝ)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (hS : S.Nonempty) (hT : T.Nonempty) :
    uniformProbability (rowSliceDiscrepancyBad (d := d) beta S T) ≤
      Real.exp (-(beta + 4) * edgeSetEntropy n (max S.card T.card)) := by
  apply (rowSliceEdge_logarithmic_bad_event hn hdn S T (rowSliceEdgeMean_pos hn hd hS hT)
    (2 * (beta + 4) * edgeSetEntropy n (max S.card T.card))).trans_eq
  congr 1
  ring

end CircularLaw
