import CircularLaw.BernoulliSubsetPoissonTail
import CircularLaw.BernoulliUniformRowLoad
import CircularLaw.RowSliceMatrixDiscrepancy

/-!
# Actual Bernoulli matrix edge counts and fixed-set discrepancy tails

The zero-one matrix edge count is the literal Bernoulli count on S×T.
Its logarithmic upper tail supplies the deterministic discrepancy input.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def bernoulliSquareMatrixReal {n : ℕ} (sample : BernoulliSquareSample n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cond (sample (i, j)) 1 0

theorem bernoulli_square_matrix_real_nonneg {n : ℕ} (sample : BernoulliSquareSample n)
    (i j : Fin n) : 0 ≤ bernoulliSquareMatrixReal sample i j := by
  cases h : sample (i, j) <;> simp [bernoulliSquareMatrixReal, h]

theorem bernoulli_square_matrix_real_edge_count {n : ℕ} (sample : BernoulliSquareSample n)
    (S T : Finset (Fin n)) :
    matrixEdgeCount (bernoulliSquareMatrixReal sample) S T = bernoulliSubsetCount (S.product T) sample := by
  unfold matrixEdgeCount bernoulliSquareMatrixReal bernoulliSubsetCount
  exact (Finset.sum_product S T (fun a => (cond (sample a) 1 0 : ℝ))).symm

def BernoulliMatrixDiscrepancyBad {n : ℕ} (d : ℕ) (beta : ℝ)
    (S T : Finset (Fin n)) (sample : BernoulliSquareSample n) : Prop :=
  Real.exp 2 * rowSliceEdgeMean d S T < matrixEdgeCount (bernoulliSquareMatrixReal sample) S T ∧
    2 * (beta + 4) * edgeSetEntropy n (max S.card T.card) <
      matrixEdgeCount (bernoulliSquareMatrixReal sample) S T *
        Real.log (matrixEdgeCount (bernoulliSquareMatrixReal sample) S T / rowSliceEdgeMean d S T)

theorem bernoulli_matrix_discrepancy_failure_iff {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (beta : ℝ) (sample : BernoulliSquareSample n) :
    (¬MatrixDiscrepancy ((d : ℝ) / n) (Real.exp 2) (2 * (beta + 4))
      (bernoulliSquareMatrixReal sample)) ↔
      ∃ S T : Finset (Fin n), S.Nonempty ∧ T.Nonempty ∧ BernoulliMatrixDiscrepancyBad d beta S T sample := by
  constructor
  · intro hFail
    unfold MatrixDiscrepancy at hFail
    push_neg at hFail
    obtain ⟨S, T, hS, hT, hRatio, hCost⟩ := hFail
    have hMean := rowSliceEdgeMean_pos hn hd hS hT
    exact ⟨S, T, hS, hT, (lt_div_iff₀ hMean).mp hRatio, hCost⟩
  · rintro ⟨S, T, hS, hT, hBad⟩ hGood
    have hMean := rowSliceEdgeMean_pos hn hd hS hT
    rcases hGood S T hS hT with hRatio | hCost
    · exact not_lt_of_ge ((div_le_iff₀ hMean).mp hRatio) hBad.1
    · exact not_lt_of_ge hCost hBad.2

theorem bernoulli_matrix_discrepancy_fixed_sets_probability {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (beta : ℝ)
    (S T : Finset (Fin n)) (hS : S.Nonempty) (hT : T.Nonempty) :
    (sparseBernoulliMatrixLaw n d).real {sample | BernoulliMatrixDiscrepancyBad d beta S T sample} ≤
      Real.exp (-(beta + 4) * edgeSetEntropy n (max S.card T.card)) := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn]
  let p := rowBernoulliParameter n d
  have hp := rowBernoulliParameter_le_one hn hdn
  have hMean : ((S.product T).card : ℝ) * p = rowSliceEdgeMean d S T := by
    change ((S.product T).card : ℝ) * (rowBernoulliParameter n d : ℝ) = rowSliceEdgeMean d S T
    have hCard : (S.product T).card = S.card * T.card := Finset.card_product S T
    rw [hCard, Nat.cast_mul, rowBernoulliParameter_coe, rowSliceEdgeMean]
    ring
  have h := bernoulli_subset_count_logarithmic_bad_event p hp (S.product T)
    (by rw [hMean]; exact rowSliceEdgeMean_pos hn hd hS hT)
    (2 * (beta + 4) * edgeSetEntropy n (max S.card T.card))
  simp only [hMean, ← bernoulli_square_matrix_real_edge_count] at h
  apply h.trans_eq
  congr 1
  ring

end CircularLaw
