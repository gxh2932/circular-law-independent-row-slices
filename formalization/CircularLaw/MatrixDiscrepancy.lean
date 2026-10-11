import CircularLaw.EdgeDiscrepancyEntropy

/-!
# Deterministic matrix discrepancy and degree bounds

These are the literal rectangular edge count and the two discrepancy
alternatives. They are defined for an arbitrary real matrix so the
deterministic heavy-term argument can use the same statements as the
checked random row-slice probability estimates.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def matrixEdgeCount {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m)) (T : Finset (Fin n)) : ℝ := ∑ i ∈ S, ∑ j ∈ T, M i j

def MatrixDiscrepancy {m n : ℕ} (density kappa₁ kappa₂ : ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ S : Finset (Fin m), ∀ T : Finset (Fin n), S.Nonempty → T.Nonempty →
    matrixEdgeCount M S T / (density * ((S.card : ℝ) * (T.card : ℝ))) ≤ kappa₁ ∨
      matrixEdgeCount M S T * Real.log (matrixEdgeCount M S T / (density * ((S.card : ℝ) * (T.card : ℝ)))) ≤
        kappa₂ * edgeSetEntropy n (max S.card T.card)

def MatrixRowColumnBound {m n : ℕ} (B : ℝ) (M : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i : Fin m, (∑ j : Fin n, M i j) ≤ B) ∧
    ∀ j : Fin n, (∑ i : Fin m, M i j) ≤ B

theorem matrixEdgeCount_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (S : Finset (Fin m)) (T : Finset (Fin n)) :
    0 ≤ matrixEdgeCount M S T := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hM i j))

theorem matrixEdgeCount_le_rows {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) {B : ℝ} (hRow : ∀ i, (∑ j, M i j) ≤ B)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    matrixEdgeCount M S T ≤ (S.card : ℝ) * B := by
  calc
    _ ≤ ∑ i ∈ S, ∑ j : Fin n, M i j := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun j _ _ => hM i j)
    _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum (fun i _ => hRow i)
    _ = _ := by simp

theorem matrixEdgeCount_le_columns {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) {B : ℝ} (hColumn : ∀ j, (∑ i, M i j) ≤ B)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    matrixEdgeCount M S T ≤ (T.card : ℝ) * B := by
  unfold matrixEdgeCount
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j ∈ T, ∑ i : Fin m, M i j := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hM i j)
    _ ≤ ∑ _j ∈ T, B := Finset.sum_le_sum (fun j _ => hColumn j)
    _ = _ := by simp

end CircularLaw
