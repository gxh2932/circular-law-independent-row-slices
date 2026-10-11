import CircularLaw.GreedyPrefixColumnConditional
import CircularLaw.BernoulliPrefixNormalizedFailure

/-!
# Rectangular ambient views of the actual alternating process

Explicit dimension equalities transport the greedy product and logarithm
to an ambient rectangular prefix. The row and column deletion and fresh
vector identities hold before and after either insertion without replacing
the ambient sample by a separate random matrix.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

def bernoulliShiftedAmbientPrefix {N a m : ℕ} (ha : a ≤ N) (hm : m ≤ N) (ham : a ≤ m)
    (z : ℂ) (x : BernoulliSquareSample N) : Matrix (Fin a) (Fin m) ℂ :=
  diagonalEmbeddedShift (bernoulliRectangularMatrix (bernoulliPrefixSample ha hm x))
    ⟨Fin.castLE ham, Fin.castLE_injective ham⟩ z

theorem source_prefix_retained_product_at_dimensions {N M s a m r : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (ham : a ≤ m)
    (hRows : sourceAlternatingPrefixRows N M s = a)
    (hCols : sourceAlternatingPrefixColumns N M s = m)
    (hr : r ≤ a) (d : ℝ) (z : ℂ) (x : BernoulliSquareSample N) :
    sourcePrefixRetainedProduct N M s r d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x) =
      leadingRowSingularProduct (degreeNormalizingScalar d • bernoulliShiftedAmbientPrefix ha hm ham z x) hr := by
  subst a
  subst m
  rw [sourcePrefixRetainedProduct, dif_pos hr]
  rfl

theorem source_prefix_retained_log_at_dimensions {N M s a m r : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (ham : a ≤ m)
    (hRows : sourceAlternatingPrefixRows N M s = a)
    (hCols : sourceAlternatingPrefixColumns N M s = m)
    (hr : r ≤ a) (d : ℝ) (z : ℂ) (x : BernoulliSquareSample N) :
    sourcePrefixRetainedLog N M s r d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x) =
      degreeNormalizedLeadingLogPrefix d (bernoulliShiftedAmbientPrefix ha hm ham z x) hr / N := by
  subst a
  subst m
  rw [sourcePrefixRetainedLog, dif_pos hr]
  rfl

theorem bernoulli_shifted_ambient_row_old {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : a + 1 ≤ N) (ham : a + 1 ≤ m)
    (z : ℂ) (x : BernoulliSquareSample N) :
    (bernoulliShiftedAmbientPrefix hNext hm ham z x).submatrix Fin.castSucc id =
      bernoulliShiftedAmbientPrefix ha hm ((Nat.le_succ a).trans ham) z x := by
  ext i j
  simp [bernoulliShiftedAmbientPrefix, Matrix.submatrix_apply, diagonalEmbeddedShift,
    bernoulliRectangularMatrix, bernoulliPrefixSample, bernoulliPrefixEntryEmbedding, Fin.ext_iff]

theorem bernoulli_shifted_ambient_column_old {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : m + 1 ≤ N) (ham : a ≤ m)
    (z : ℂ) (x : BernoulliSquareSample N) :
    (bernoulliShiftedAmbientPrefix ha hNext (ham.trans (Nat.le_succ m)) z x).submatrix id Fin.castSucc =
      bernoulliShiftedAmbientPrefix ha hm ham z x := by
  ext i j
  simp [bernoulliShiftedAmbientPrefix, Matrix.submatrix_apply, diagonalEmbeddedShift,
    bernoulliRectangularMatrix, bernoulliPrefixSample, bernoulliPrefixEntryEmbedding, Fin.ext_iff]

theorem bernoulli_shifted_ambient_row_fresh {N a m : ℕ}
    (hm : m ≤ N) (hNext : a + 1 ≤ N) (ham : a + 1 ≤ m)
    (z : ℂ) (x : BernoulliSquareSample N) :
    lastRowVector (bernoulliShiftedAmbientPrefix hNext hm ham z x) =
      bernoulliCubeVector (fun j => x (bernoulliFreshRowEntryEmbedding hNext hm j)) +
        sourceFreshRowDiagonalShift a m z := by
  ext j
  simp only [lastRowVector, bernoulliShiftedAmbientPrefix, diagonalEmbeddedShift,
    bernoulliRectangularMatrix, bernoulliPrefixSample, bernoulliPrefixEntryEmbedding,
    bernoulliFreshRowEntryEmbedding, bernoulliCubeVector, sourceFreshRowDiagonalShift,
    PiLp.add_apply, Function.Embedding.coeFn_mk]
  by_cases h : j.val = a
  · have hFin : Fin.castLE ham (Fin.last a) = j := by apply Fin.ext; exact h.symm
    simp [hFin, h, sub_eq_add_neg]
  · have hFin : Fin.castLE ham (Fin.last a) ≠ j := by
      intro heq
      exact h (congrArg Fin.val heq).symm
    simp [hFin, h]

theorem bernoulli_shifted_ambient_column_fresh {N a m : ℕ}
    (ha : a ≤ N) (hNext : m + 1 ≤ N) (ham : a ≤ m)
    (z : ℂ) (x : BernoulliSquareSample N) :
    lastColumnVector (bernoulliShiftedAmbientPrefix ha hNext (ham.trans (Nat.le_succ m)) z x) =
      bernoulliCubeVector (fun i => x (bernoulliFreshColumnEntryEmbedding ha hNext i)) := by
  ext i
  have hFin : Fin.castLE (ham.trans (Nat.le_succ m)) i ≠ Fin.last m := by
    intro heq
    have hVal := congrArg Fin.val heq
    exact (Nat.ne_of_lt (i.isLt.trans_le ham)) hVal
  simp [lastColumnVector, bernoulliShiftedAmbientPrefix, diagonalEmbeddedShift,
    bernoulliRectangularMatrix, bernoulliPrefixSample, bernoulliPrefixEntryEmbedding,
    bernoulliFreshColumnEntryEmbedding, bernoulliCubeVector, hFin]

end CircularLaw
