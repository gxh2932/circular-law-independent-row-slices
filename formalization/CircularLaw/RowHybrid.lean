import CircularLaw.HybridRowReindex

/-!
# Literal prefix hybrids of slice and Bernoulli rows

The first `t` rows use the slice sample; the rest use the Bernoulli
sample. Removing the selected row gives the same other-row matrix before
and after replacement. Row reindexing then identifies both potentials
with the checked inserted-row Schur model.
-/

noncomputable section
open Classical
open scoped Matrix NNReal

namespace CircularLaw

abbrev ReplacementRowPair (n d : ℕ) := RowSlice n d × (Fin n → Bool)

def rowHybridMatrix {n d k : ℕ} (u : Fin k → EuclideanSpace ℂ (Fin n))
    (t : ℕ) (rows : Fin k → ReplacementRowPair n d) : Matrix (Fin k) (Fin n) ℂ :=
  fun i j => ((if i.val < t then rowSliceEuclideanRow (rows i).1
    else bernoulliCubeVector (rows i).2) + u i) j

def rowShiftNormBound {n k : ℕ} (u : Fin k → EuclideanSpace ℂ (Fin n)) : ℝ :=
  (Finset.univ.sup (fun i => ‖u i‖₊) : ℝ≥0)

theorem norm_le_rowShiftNormBound {n k : ℕ}
    (u : Fin k → EuclideanSpace ℂ (Fin n)) (i : Fin k) : ‖u i‖ ≤ rowShiftNormBound u := by
  exact_mod_cast (Finset.le_sup (f := fun i => ‖u i‖₊) (Finset.mem_univ i))

theorem rowShiftNormBound_nonneg {n k : ℕ}
    (u : Fin k → EuclideanSpace ℂ (Fin n)) : 0 ≤ rowShiftNormBound u :=
  NNReal.coe_nonneg _

theorem rowShiftNormBound_attained {n k : ℕ} (hk : 0 < k)
    (u : Fin k → EuclideanSpace ℂ (Fin n)) :
    ∃ i, rowShiftNormBound u = ‖u i‖ := by
  have hNonempty : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hNonempty (fun i => ‖u i‖₊)
  exact ⟨i, congrArg (fun a : ℝ≥0 => (a : ℝ)) hi⟩

def hybridOtherRows {m n d : ℕ} (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n))
    (i : Fin (m + 1)) (rest : Fin m → ReplacementRowPair n d) : Matrix (Fin m) (Fin n) ℂ :=
  fun j a => ((if (i.succAbove j).val < i.val then rowSliceEuclideanRow (rest j).1
    else bernoulliCubeVector (rest j).2) + u (i.succAbove j)) a

theorem rowHybridMatrix_before_isolate {m n d : ℕ}
    (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (i : Fin (m + 1))
    (rest : Fin m → ReplacementRowPair n d) (pair : ReplacementRowPair n d) :
    (rowHybridMatrix u i.val (i.insertNth pair rest)).submatrix (hybridRowIndexEquiv i) id =
      hybridInsertedRows (hybridOtherRows u i rest) (bernoulliCubeVector pair.2 + u i) := by
  ext (j | j) a
  · cases j
    simp [rowHybridMatrix, hybridRowIndexEquiv, hybridInsertedRows, hybridCandidateRow]
  · simp [rowHybridMatrix, hybridRowIndexEquiv, hybridInsertedRows, hybridOtherRows]

theorem rowHybridMatrix_after_isolate {m n d : ℕ}
    (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (i : Fin (m + 1))
    (rest : Fin m → ReplacementRowPair n d) (pair : ReplacementRowPair n d) :
    (rowHybridMatrix u (i.val + 1) (i.insertNth pair rest)).submatrix (hybridRowIndexEquiv i) id =
      hybridInsertedRows (hybridOtherRows u i rest) (rowSliceEuclideanRow pair.1 + u i) := by
  ext (j | j) a
  · cases j
    simp [rowHybridMatrix, hybridRowIndexEquiv, hybridInsertedRows, hybridCandidateRow]
  · have hNe : (i.succAbove j).val ≠ i.val := fun h => i.succAbove_ne j (Fin.ext h)
    have hLt : (i.succAbove j).val < i.val + 1 ↔ (i.succAbove j).val < i.val := by omega
    simp [rowHybridMatrix, hybridRowIndexEquiv, hybridInsertedRows, hybridOtherRows, hLt]

theorem rowHybrid_potential_increment {m n d : ℕ}
    (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n)) (i : Fin (m + 1))
    (rest : Fin m → ReplacementRowPair n d) (pair : ReplacementRowPair n d) (η : ℝ) :
    regularizedRowPotential (rowHybridMatrix u (i.val + 1) (i.insertNth pair rest)) η -
        regularizedRowPotential (rowHybridMatrix u i.val (i.insertNth pair rest)) η =
      regularizedRowPotential
        (hybridInsertedRows (hybridOtherRows u i rest) (rowSliceEuclideanRow pair.1 + u i)) η -
      regularizedRowPotential
        (hybridInsertedRows (hybridOtherRows u i rest) (bernoulliCubeVector pair.2 + u i)) η := by
  rw [← regularizedRowPotential_row_submatrix _ (hybridRowIndexEquiv i),
    rowHybridMatrix_after_isolate,
    ← regularizedRowPotential_row_submatrix (rowHybridMatrix u i.val _) (hybridRowIndexEquiv i),
    rowHybridMatrix_before_isolate]

theorem rowHybridMatrix_zero {n d k : ℕ}
    (u : Fin k → EuclideanSpace ℂ (Fin n)) (rows : Fin k → ReplacementRowPair n d) :
    rowHybridMatrix u 0 rows = fun i j => (bernoulliCubeVector (rows i).2 + u i) j := by
  ext i j
  simp [rowHybridMatrix]

theorem rowHybridMatrix_full {n d k : ℕ}
    (u : Fin k → EuclideanSpace ℂ (Fin n)) (rows : Fin k → ReplacementRowPair n d) :
    rowHybridMatrix u k rows = fun i j => (rowSliceEuclideanRow (rows i).1 + u i) j := by
  ext i j
  simp [rowHybridMatrix, i.isLt]

end CircularLaw
